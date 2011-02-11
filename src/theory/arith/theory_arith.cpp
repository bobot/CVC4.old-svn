/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): barrett, dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/node.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_builder.h"

#include "theory/theory_engine.h"

#include "util/rational.h"
#include "util/integer.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/arithvar_dense_set.h"

#include "theory/arith/arith_rewriter.h"
#include "theory/arith/unate_propagator.h"

#include "theory/arith/theory_arith.h"
#include "theory/arith/normal_form.h"

#include <map>
#include <stdint.h>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

struct SlackAttrID;
typedef expr::Attribute<SlackAttrID, Node> Slack;

TheoryArith::TheoryArith(context::Context* c, OutputChannel& out) :
  Theory(THEORY_ARITH, c, out),
  d_constants(NodeManager::currentNM()),
  d_partialModel(c),
  d_basicManager(),
  d_activityMonitor(),
  d_diseq(c),
  d_tableau(d_activityMonitor, d_basicManager),
  d_propagator(c, out),
  d_simplex(d_constants, d_partialModel, d_basicManager,  d_out, d_activityMonitor, d_tableau),
  d_statistics()
{}

TheoryArith::~TheoryArith(){}

TheoryArith::Statistics::Statistics():
  d_statUserVariables("theory::arith::UserVariables", 0),
  d_statSlackVariables("theory::arith::SlackVariables", 0),
  d_statDisequalitySplits("theory::arith::DisequalitySplits", 0),
  d_statDisequalityConflicts("theory::arith::DisequalityConflicts", 0),
  d_staticLearningTimer("theory::arith::staticLearningTimer")
{
  StatisticsRegistry::registerStat(&d_statUserVariables);
  StatisticsRegistry::registerStat(&d_statSlackVariables);
  StatisticsRegistry::registerStat(&d_statDisequalitySplits);
  StatisticsRegistry::registerStat(&d_statDisequalityConflicts);
  StatisticsRegistry::registerStat(&d_staticLearningTimer);
}

TheoryArith::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUserVariables);
  StatisticsRegistry::unregisterStat(&d_statSlackVariables);
  StatisticsRegistry::unregisterStat(&d_statDisequalitySplits);
  StatisticsRegistry::unregisterStat(&d_statDisequalityConflicts);
  StatisticsRegistry::unregisterStat(&d_staticLearningTimer);
}

void TheoryArith::staticLearning(TNode n, NodeBuilder<>& learned) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_staticLearningTimer);

  vector<TNode> workList;
  workList.push_back(n);
  __gnu_cxx::hash_set<TNode, TNodeHashFunction> processed;

  while(!workList.empty()) {
    n = workList.back();

    bool unprocessedChildren = false;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      if(processed.find(*i) == processed.end()) {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }

    if(unprocessedChildren) {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if(processed.find(n) != processed.end()) {
      continue;
    }
    processed.insert(n);

    // == MINS ==

    Debug("mins") << "===================== looking at" << endl << n << endl;
    if(n.getKind() == kind::ITE && n[0].getKind() != EQUAL && isRelationOperator(n[0].getKind())  ){
      TNode c = n[0];
      Kind k = simplifiedKind(c);
      TNode t = n[1];
      TNode e = n[2];
      TNode cleft = (c.getKind() == NOT) ? c[0][0] : c[0];
      TNode cright = (c.getKind() == NOT) ? c[0][1] : c[1];

      if((t == cright) && (e == cleft)){
	TNode tmp = t;
	t = e;
	e = tmp;
	k = reverseRelationKind(k);
      }
      if(t == cleft && e == cright){
	// t == cleft && e == cright
	Assert( t == cleft );
	Assert( e == cright );
	switch(k){
	case LT:   // (ite (< x y) x y)
	case LEQ: { // (ite (<= x y) x y)
	  Node nLeqX = NodeBuilder<2>(LEQ) << n << t;
	  Node nLeqY = NodeBuilder<2>(LEQ) << n << e;
	  Debug("arith::mins") << n << "is a min =>"  << nLeqX << nLeqY << endl;
	  learned << nLeqX << nLeqY;
	  break;
	}
	case GT: // (ite (> x y) x y)
	case GEQ: { // (ite (>= x y) x y)
	  Node nGeqX = NodeBuilder<2>(GEQ) << n << t;
	  Node nGeqY = NodeBuilder<2>(GEQ) << n << e;
	  Debug("arith::mins") << n << "is a max =>"  << nGeqX << nGeqY << endl;
	  learned << nGeqX << nGeqY;
	  break;
	}
	default: Unreachable();
	}
      }
    }
    // == 2-CONSTANTS ==

    if(n.getKind() == ITE &&
       (n[1].getKind() == CONST_RATIONAL || n[1].getKind() == CONST_INTEGER) &&
       (n[2].getKind() == CONST_RATIONAL || n[2].getKind() == CONST_INTEGER)) {
      Rational t = coerceToRational(n[1]);
      Rational e = coerceToRational(n[2]);
      TNode min = (t <= e) ? n[1] : n[2];
      TNode max = (t >= e) ? n[1] : n[2];

      Node nGeqMin = NodeBuilder<2>(GEQ) << n << min;
      Node nLeqMax = NodeBuilder<2>(LEQ) << n << max;
      Debug("arith::mins") << n << " is a constant sandwich"  << nGeqMin << nLeqMax << endl;
      learned << nGeqMin << nLeqMax;
    }

    // // binary OR of binary ANDs of EQUALities
    // if(n.getKind() == kind::OR && n.getNumChildren() == 2 &&
    //    n[0].getKind() == kind::AND && n[0].getNumChildren() == 2 &&
    //    n[1].getKind() == kind::AND && n[1].getNumChildren() == 2 &&
    //    (n[0][0].getKind() == kind::EQUAL || n[0][0].getKind() == kind::IFF) &&
    //    (n[0][1].getKind() == kind::EQUAL || n[0][1].getKind() == kind::IFF) &&
    //    (n[1][0].getKind() == kind::EQUAL || n[1][0].getKind() == kind::IFF) &&
    //    (n[1][1].getKind() == kind::EQUAL || n[1][1].getKind() == kind::IFF)) {
    //   // now we have (a = b && c = d) || (e = f && g = h)

    //   Debug("diamonds") << "has form of a diamond!" << endl;

    //   TNode
    //     a = n[0][0][0], b = n[0][0][1],
    //     c = n[0][1][0], d = n[0][1][1],
    //     e = n[1][0][0], f = n[1][0][1],
    //     g = n[1][1][0], h = n[1][1][1];

    //   // test that one of {a, b} = one of {c, d}, and make "b" the
    //   // shared node (i.e. put in the form (a = b && b = d))
    //   // note we don't actually care about the shared ones, so the
    //   // "swaps" below are one-sided, ignoring b and c
    //   if(a == c) {
    //     a = b;
    //   } else if(a == d) {
    //     a = b;
    //     d = c;
    //   } else if(b == c) {
    //     // nothing to do
    //   } else if(b == d) {
    //     d = c;
    //   } else {
    //     // condition not satisfied
    //     Debug("diamonds") << "+ A fails" << endl;
    //     continue;
    //   }

    //   Debug("diamonds") << "+ A holds" << endl;

    //   // same: one of {e, f} = one of {g, h}, and make "f" the
    //   // shared node (i.e. put in the form (e = f && f = h))
    //   if(e == g) {
    //     e = f;
    //   } else if(e == h) {
    //     e = f;
    //     h = g;
    //   } else if(f == g) {
    //     // nothing to do
    //   } else if(f == h) {
    //     h = g;
    //   } else {
    //     // condition not satisfied
    //     Debug("diamonds") << "+ B fails" << endl;
    //     continue;
    //   }

    //   Debug("diamonds") << "+ B holds" << endl;

    //   // now we have (a = b && b = d) || (e = f && f = h)
    //   // test that {a, d} == {e, h}
    //   if( (a == e && d == h) ||
    //       (a == h && d == e) ) {
    //     // learn: n implies a == d
    //     Debug("diamonds") << "+ C holds" << endl;
    //     Node newEquality = a.getType().isBoolean() ? a.iffNode(d) : a.eqNode(d);
    //     Debug("diamonds") << "  ==> " << newEquality << endl;
    //     learned << n.impNode(newEquality);
    //   } else {
    //     Debug("diamonds") << "+ C fails" << endl;
    //   }
    // }
  }
}



ArithVar TheoryArith::findBasicRow(ArithVar variable){
  for(ArithVarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    ArithVar x_j = *basicIter;
    ReducedRowVector* row_j = d_tableau.lookup(x_j);

    if(row_j->has(variable)){
      return x_j;
    }
  }
  return ARITHVAR_SENTINEL;
}


void TheoryArith::preRegisterTerm(TNode n) {
  Debug("arith_preregister") <<"begin arith::preRegisterTerm("<< n <<")"<< endl;
  Kind k = n.getKind();

  bool isStrictlyVarList = k == kind::MULT && VarList::isMember(n);

  if(isStrictlyVarList){
    d_out->setIncomplete();
  }

  if(isLeaf(n) || isStrictlyVarList){
    ++(d_statistics.d_statUserVariables);
    ArithVar varN = requestArithVar(n,false);
    setupInitialValue(varN);
  }


  //TODO is an atom
  if(isRelationOperator(k)){
    Assert(Comparison::isNormalAtom(n));


    d_propagator.addAtom(n);

    TNode left  = n[0];
    TNode right = n[1];
    if(left.getKind() == PLUS){
      //We may need to introduce a slack variable.
      Assert(left.getNumChildren() >= 2);
      if(!left.hasAttribute(Slack())){
        setupSlack(left);
      }
    }
  }
  Debug("arith_preregister") << "end arith::preRegisterTerm("<< n <<")"<< endl;
}


ArithVar TheoryArith::requestArithVar(TNode x, bool basic){
  Assert(isLeaf(x));
  Assert(!hasArithVar(x));

  ArithVar varX = d_variables.size();
  d_variables.push_back(Node(x));

  d_simplex.increaseMax();

  setArithVar(x,varX);

  Assert(varX == d_activityMonitor.size());
  d_activityMonitor.push_back(0);

  d_basicManager.init(varX,basic);
  d_tableau.increaseSize();

  Debug("arith::arithvar") << x << " |-> " << varX << endl;

  return varX;
}

void TheoryArith::asVectors(Polynomial& p, std::vector<Rational>& coeffs, std::vector<ArithVar>& variables) const{
  for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){
    const Monomial& mono = *i;
    const Constant& constant = mono.getConstant();
    const VarList& variable = mono.getVarList();

    Node n = variable.getNode();

    Debug("rewriter") << "should be var: " << n << endl;

    Assert(isLeaf(n));
    Assert(hasArithVar(n));

    ArithVar av = asArithVar(n);

    coeffs.push_back(constant.getValue());
    variables.push_back(av);
  }
}

void TheoryArith::setupSlack(TNode left){

  ++(d_statistics.d_statSlackVariables);
  TypeNode real_type = NodeManager::currentNM()->realType();
  Node slack = NodeManager::currentNM()->mkVar(real_type);
  left.setAttribute(Slack(), slack);

  ArithVar varSlack = requestArithVar(slack, true);

  Polynomial polyLeft = Polynomial::parsePolynomial(left);

  vector<ArithVar> variables;
  vector<Rational> coefficients;

  asVectors(polyLeft, coefficients, variables);

  d_tableau.addRow(varSlack, coefficients, variables);

  setupInitialValue(varSlack);
}

/* Requirements:
 * For basic variables the row must have been added to the tableau.
 */
void TheoryArith::setupInitialValue(ArithVar x){

  if(!d_basicManager.isMember(x)){
    d_partialModel.initialize(x,d_constants.d_ZERO_DELTA);
  }else{
    //If the variable is basic, assertions may have already happened and updates
    //may have occured before setting this variable up.

    //This can go away if the tableau creation is done at preregister
    //time instead of register
    DeltaRational safeAssignment = d_simplex.computeRowValue(x, true);
    DeltaRational assignment = d_simplex.computeRowValue(x, false);
    d_partialModel.initialize(x,safeAssignment);
    d_partialModel.setAssignment(x,assignment);


    //d_simplex.checkBasicVariable(x);
    //Conciously violating unneeded check

    //Strictly speaking checking x is unnessecary as it cannot have an upper or
    //lower bound. This is done to strongly enforce the notion that basic
    //variables should not be changed without begin checked.

  }
  Debug("arithgc") << "setupVariable("<<x<<")"<<std::endl;
};

void TheoryArith::registerTerm(TNode tn){
  Debug("arith") << "registerTerm(" << tn << ")" << endl;
}

template <bool selectLeft>
TNode getSide(TNode assertion, Kind simpleKind){
  switch(simpleKind){
  case LT:
  case GT:
  case DISTINCT:
    return selectLeft ? (assertion[0])[0] : (assertion[0])[1];
  case LEQ:
  case GEQ:
  case EQUAL:
    return selectLeft ? assertion[0] : assertion[1];
  default:
    Unreachable();
    return TNode::null();
  }
}

ArithVar TheoryArith::determineLeftVariable(TNode assertion, Kind simpleKind){
  TNode left = getSide<true>(assertion, simpleKind);

  if(isLeaf(left)){
    return asArithVar(left);
  }else{
    Assert(left.hasAttribute(Slack()));
    TNode slack = left.getAttribute(Slack());
    return asArithVar(slack);
  }
}

DeltaRational determineRightConstant(TNode assertion, Kind simpleKind){
  TNode right = getSide<false>(assertion, simpleKind);

  Assert(right.getKind() == CONST_RATIONAL);
  const Rational& noninf = right.getConst<Rational>();

  Rational inf = Rational(Integer(deltaCoeff(simpleKind)));
  return DeltaRational(noninf, inf);
}

bool TheoryArith::assertionCases(TNode assertion){
  Kind simpKind = simplifiedKind(assertion);
  Assert(simpKind != UNDEFINED_KIND);
  ArithVar x_i = determineLeftVariable(assertion, simpKind);
  DeltaRational c_i = determineRightConstant(assertion, simpKind);

  Debug("arith_assertions") << "arith assertion(" << assertion
                            << " \\-> "
                            <<x_i<<" "<< simpKind <<" "<< c_i << ")" << std::endl;
  switch(simpKind){
  case LEQ:
    if (d_partialModel.hasLowerBound(x_i) && d_partialModel.getLowerBound(x_i) == c_i) {
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        NodeBuilder<3> conflict(kind::AND);
        conflict << diseq << assertion << d_partialModel.getLowerConstraint(x_i);
        ++(d_statistics.d_statDisequalityConflicts);
        d_out->conflict((TNode)conflict);
        return true;
      }
    }
  case LT:
    return d_simplex.AssertUpper(x_i, c_i, assertion);
  case GEQ:
    if (d_partialModel.hasUpperBound(x_i) && d_partialModel.getUpperBound(x_i) == c_i) {
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        NodeBuilder<3> conflict(kind::AND);
        conflict << diseq << assertion << d_partialModel.getUpperConstraint(x_i);
        ++(d_statistics.d_statDisequalityConflicts);
        d_out->conflict((TNode)conflict);
        return true;
      }
    }
  case GT:
    return d_simplex.AssertLower(x_i, c_i, assertion);
  case EQUAL:
    return d_simplex.AssertEquality(x_i, c_i, assertion);
  case DISTINCT:
    {
      d_diseq.insert(assertion);
      // Check if it conflicts with the the bounds
      TNode eq = assertion[0];
      Assert(eq.getKind() == kind::EQUAL);
      TNode lhs = eq[0];
      TNode rhs = eq[1];
      Assert(rhs.getKind() == CONST_RATIONAL);
      ArithVar lhsVar = determineLeftVariable(eq, kind::EQUAL);
      DeltaRational rhsValue = determineRightConstant(eq, kind::EQUAL);
      if (d_partialModel.hasLowerBound(lhsVar) && d_partialModel.hasUpperBound(lhsVar) &&
          d_partialModel.getLowerBound(lhsVar) == rhsValue && d_partialModel.getUpperBound(lhsVar) == rhsValue) {
        NodeBuilder<3> conflict(kind::AND);
        conflict << assertion << d_partialModel.getLowerConstraint(lhsVar) << d_partialModel.getUpperConstraint(lhsVar);
        d_out->conflict((TNode)conflict);
      }
    }
    return false;
  default:
    Unreachable();
    return false;
  }
}

void TheoryArith::check(Effort effortLevel){
  Debug("arith") << "TheoryArith::check begun" << std::endl;

  while(!done()){

    Node assertion = get();

    //d_propagator.assertLiteral(assertion);
    bool conflictDuringAnAssert = assertionCases(assertion);

    if(conflictDuringAnAssert){
      d_partialModel.revertAssignmentChanges();
      return;
    }
  }

  if(Debug.isOn("arith::print_assertions") && fullEffort(effortLevel)) {
    Debug("arith::print_assertions") << "Assertions:" << endl;
    for (ArithVar i = 0; i < d_variables.size(); ++ i) {
      if (d_partialModel.hasLowerBound(i)) {
        Node lConstr = d_partialModel.getLowerConstraint(i);
        Debug("arith::print_assertions") << lConstr.toString() << endl;
      }

      if (d_partialModel.hasUpperBound(i)) {
        Node uConstr = d_partialModel.getUpperConstraint(i);
        Debug("arith::print_assertions") << uConstr.toString() << endl;
      }
    }
    context::CDSet<Node, NodeHashFunction>::iterator it = d_diseq.begin();
    context::CDSet<Node, NodeHashFunction>::iterator it_end = d_diseq.end();
    for(; it != it_end; ++ it) {
      Debug("arith::print_assertions") << *it << endl;
    }
  }

  Node possibleConflict = d_simplex.updateInconsistentVars();
  if(possibleConflict != Node::null()){

    d_partialModel.revertAssignmentChanges();

    if(Debug.isOn("arith::print-conflict"))
      Debug("arith_conflict") << (possibleConflict) << std::endl;

    d_out->conflict(possibleConflict);

    Debug("arith_conflict") <<"Found a conflict "<< possibleConflict << endl;
  }else{
    d_partialModel.commitAssignmentChanges();

    if (fullEffort(effortLevel)) {
      context::CDSet<Node, NodeHashFunction>::iterator it = d_diseq.begin();
      context::CDSet<Node, NodeHashFunction>::iterator it_end = d_diseq.end();
      for(; it != it_end; ++ it) {
        TNode eq = (*it)[0];
        Assert(eq.getKind() == kind::EQUAL);
        TNode lhs = eq[0];
        TNode rhs = eq[1];
        Assert(rhs.getKind() == CONST_RATIONAL);
        ArithVar lhsVar = determineLeftVariable(eq, kind::EQUAL);
        if(d_tableau.isEjected(lhsVar)){
          d_simplex.reinjectVariable(lhsVar);
        }
        DeltaRational lhsValue = d_partialModel.getAssignment(lhsVar);
        DeltaRational rhsValue = determineRightConstant(eq, kind::EQUAL);
        if (lhsValue == rhsValue) {
          Debug("arith_lemma") << "Splitting on " << eq << endl;
          Debug("arith_lemma") << "LHS value = " << lhsValue << endl;
          Debug("arith_lemma") << "RHS value = " << rhsValue << endl;
          Node ltNode = NodeBuilder<2>(kind::LT) << lhs << rhs;
          Node gtNode = NodeBuilder<2>(kind::GT) << lhs << rhs;
          Node lemma = NodeBuilder<3>(OR) << eq << ltNode << gtNode;

          // < => !>
          Node imp1 = NodeBuilder<2>(kind::IMPLIES) << ltNode << gtNode.notNode();
          // < => !=
          Node imp2 = NodeBuilder<2>(kind::IMPLIES) << ltNode << eq.notNode();
          // > => !=
          Node imp3 = NodeBuilder<2>(kind::IMPLIES) << gtNode << eq.notNode();
          // All the implication
          Node impClosure = NodeBuilder<3>(kind::AND) << imp1 << imp2 << imp3;

          ++(d_statistics.d_statDisequalitySplits);
          d_out->lemma(lemma.andNode(impClosure));
        }
      }
    }
  }
  if(Debug.isOn("paranoid:check_tableau")){ d_simplex.checkTableau(); }

  Debug("arith") << "TheoryArith::check end" << std::endl;

  if(Debug.isOn("arith::print_model")) {
    Debug("arith::print_model") << "Model:" << endl;

    for (ArithVar i = 0; i < d_variables.size(); ++ i) {
      Debug("arith::print_model") << d_variables[i] << " : " <<
        d_partialModel.getAssignment(i);
      if(d_basicManager.isMember(i))
        Debug("arith::print_model") << " (basic)";
      Debug("arith::print_model") << endl;
    }
  }
}

void TheoryArith::explain(TNode n) {
  // Node explanation = d_propagator.explain(n);
  // Debug("arith") << "arith::explain("<<explanation<<")->"
  //                << explanation << endl;
  // d_out->explanation(explanation, true);
}

void TheoryArith::propagate(Effort e) {

  // if(quickCheckOrMore(e)){
  //   std::vector<Node> implied = d_propagator.getImpliedLiterals();
  //   for(std::vector<Node>::iterator i = implied.begin();
  //       i != implied.end();
  //       ++i){
  //     d_out->propagate(*i);
  //   }
  // }
}

Node TheoryArith::getValue(TNode n, TheoryEngine* engine) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::VARIABLE: {
    ArithVar var = asArithVar(n);
    if(d_tableau.isEjected(var)){
      d_simplex.reinjectVariable(var);
    }

    DeltaRational drat = d_partialModel.getAssignment(var);
    const Rational& delta = d_partialModel.getDelta();
    Debug("getValue") << n << " " << drat << " " << delta << endl;
    return nodeManager->
      mkConst( drat.getNoninfinitesimalPart() +
               drat.getInfinitesimalPart() * delta );
  }

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( engine->getValue(n[0]) == engine->getValue(n[1]) );

  case kind::PLUS: { // 2+ args
    Rational value = d_constants.d_ZERO;
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      value += engine->getValue(*i).getConst<Rational>();
    }
    return nodeManager->mkConst(value);
  }

  case kind::MULT: { // 2+ args
    Rational value = d_constants.d_ONE;
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      value *= engine->getValue(*i).getConst<Rational>();
    }
    return nodeManager->mkConst(value);
  }

  case kind::MINUS: // 2 args
    // should have been rewritten
    Unreachable();

  case kind::UMINUS: // 1 arg
    // should have been rewritten
    Unreachable();

  case kind::DIVISION: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() /
                                 engine->getValue(n[1]).getConst<Rational>() );

  case kind::LT: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() <
                                 engine->getValue(n[1]).getConst<Rational>() );

  case kind::LEQ: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() <=
                                 engine->getValue(n[1]).getConst<Rational>() );

  case kind::GT: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() >
                                 engine->getValue(n[1]).getConst<Rational>() );

  case kind::GEQ: // 2 args
    return nodeManager->mkConst( engine->getValue(n[0]).getConst<Rational>() >=
                                 engine->getValue(n[1]).getConst<Rational>() );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryArith::notifyEq(TNode lhs, TNode rhs) {

}

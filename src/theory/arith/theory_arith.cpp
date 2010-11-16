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


struct ReverseSlackAttrID;
typedef expr::Attribute<ReverseSlackAttrID, Node> ReverseSlack;

TheoryArith::TheoryArith(int id, context::Context* c, OutputChannel& out) :
  Theory(id, c, out),
  d_constants(NodeManager::currentNM()),
  d_partialModel(c),
  d_basicManager(),
  d_activityMonitor(),
  d_diseq(c),
  d_tableau(d_activityMonitor, d_basicManager),
  d_rewriter(&d_constants),
  d_propagator(c, out),
  d_simplex(d_constants, d_partialModel, d_basicManager,  d_out, d_activityMonitor, d_tableau),
  d_statistics()
{}

TheoryArith::~TheoryArith(){}

TheoryArith::Statistics::Statistics():
  d_statUserVariables("theory::arith::UserVariables", 0),
  d_statSlackVariables("theory::arith::SlackVariables", 0),
  d_statDisequalitySplits("theory::arith::DisequalitySplits", 0),
  d_statDisequalityConflicts("theory::arith::DisequalityConflicts", 0)
{
  StatisticsRegistry::registerStat(&d_statUserVariables);
  StatisticsRegistry::registerStat(&d_statSlackVariables);
  StatisticsRegistry::registerStat(&d_statDisequalitySplits);
  StatisticsRegistry::registerStat(&d_statDisequalityConflicts);
}

TheoryArith::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUserVariables);
  StatisticsRegistry::unregisterStat(&d_statSlackVariables);
  StatisticsRegistry::unregisterStat(&d_statDisequalitySplits);
  StatisticsRegistry::unregisterStat(&d_statDisequalityConflicts);
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

  if(isTheoryLeaf(n) || isStrictlyVarList){
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



bool TheoryArith::isTheoryLeaf(TNode x) const{
  return x.getMetaKind() == kind::metakind::VARIABLE;
}

ArithVar TheoryArith::requestArithVar(TNode x, bool basic){
  Assert(isTheoryLeaf(x));
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

    Assert(isTheoryLeaf(n));
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
  slack.setAttribute(ReverseSlack(), left);

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

RewriteResponse TheoryArith::preRewrite(TNode n, bool topLevel) {
  return d_rewriter.preRewrite(n);
}

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

  if(isTheoryLeaf(left)){
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

      Assert(c_i.getInfinitesimalPart() == 0);
      VarRationalPair assignment = make_pair(x_i, c_i.getNoninfinitesimalPart());

      if (d_diseq.find(assignment) != d_diseq.end()) {
        Node diseq = assertion[0].eqNode(assertion[1]).notNode();
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

      Assert(c_i.getInfinitesimalPart() == 0);
      VarRationalPair assignment = make_pair(x_i, c_i.getNoninfinitesimalPart());

      if (d_diseq.find(assignment) != d_diseq.end()) {
        Node diseq = assertion[0].eqNode(assertion[1]).notNode();
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
      Assert(c_i.getInfinitesimalPart() == 0);
      VarRationalPair assignment = make_pair(x_i, c_i.getNoninfinitesimalPart());
      d_diseq.insert(assignment);

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
  static int checkNum = 0;

  int checkId = checkNum++;

  Debug("arith") << "TheoryArith::check begun " << checkId << std::endl;

  while(!done()){

    Node assertion = get();

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

    VarRationalCDSet::iterator it = d_diseq.begin();
    VarRationalCDSet::iterator it_end = d_diseq.end();
    for(; it != it_end; ++ it) {
      Node eq = NodeBuilder<2>(kind::EQUAL) << getNodeForVariable((*it).first)
                                            << mkRationalNode((*it).second);
      Node dis = eq.notNode();
      Debug("arith::print_assertions") << dis << endl;
    }
    // context::CDSet<Node, NodeHashFunction>::iterator it = d_diseq.begin();
    // context::CDSet<Node, NodeHashFunction>::iterator it_end = d_diseq.end();
    // for(; it != it_end; ++ it) {
    //   Debug("arith::print_assertions") << *it << endl;
    // }
  }

  Node possibleConflict = d_simplex.updateInconsistentVars();
  if(possibleConflict != Node::null()){

    d_partialModel.revertAssignmentChanges();

    if(Debug.isOn("arith::print-conflict"))
      Debug("arith_conflict") << (possibleConflict) << std::endl;

    d_out->conflict(possibleConflict);

    Debug("arith_conflict") <<"Found a conflict "<< possibleConflict << endl;
  }else{
    ArithPartialModel::HistoryList::const_iterator it = d_partialModel.beginChanged();
    ArithPartialModel::HistoryList::const_iterator it_end = d_partialModel.endChanged();
    for(; it != it_end; ++ it) {
      ArithVar lhsVar = *it;
      if(d_tableau.isEjected(lhsVar)) continue;

      Assert(!d_tableau.isEjected(lhsVar));
      const DeltaRational& lhsValue = d_partialModel.getAssignment(lhsVar);
      if(lhsValue.getInfinitesimalPart() != 0) continue;

      VarRationalPair vp = make_pair(lhsVar, lhsValue.getNoninfinitesimalPart());
      if(d_diseq.find(vp) == d_diseq.end()) continue;

      Node lhs = getNodeForVariable(lhsVar);
      if(lhs.hasAttribute(ReverseSlack())){
        lhs = lhs.getAttribute(ReverseSlack());
      }
      Node rhs = mkRationalNode(lhsValue.getNoninfinitesimalPart());

      Node eq = NodeBuilder<2>(kind::EQUAL) << lhs << rhs;

      Debug("arith_lemma") << "History list" << endl;
      Debug("arith_lemma") << "Splitting on " << eq << endl;
      Debug("arith_lemma") << "LHS = " << lhs << endl;
      Debug("arith_lemma") << "LHS value = " << lhsValue << endl;

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

    d_partialModel.commitAssignmentChanges();

    if (fullEffort(effortLevel)) {
       VarRationalCDSet::iterator it = d_diseq.begin();
       VarRationalCDSet::iterator it_end = d_diseq.end();

      for(; it != it_end; ++ it) {
        // TNode eq = (*it)[0];
        // Assert(eq.getKind() == kind::EQUAL);
        // TNode lhs = eq[0];
        // TNode rhs = eq[1];
        // Assert(rhs.getKind() == CONST_RATIONAL);
        // ArithVar lhsVar = determineLeftVariable(eq, kind::EQUAL);

        ArithVar lhsVar = (*it).first;
        DeltaRational rhsValue = (*it).second;

        if(d_tableau.isEjected(lhsVar)){
          d_simplex.reinjectVariable(lhsVar);
        }
        DeltaRational lhsValue = d_partialModel.getAssignment(lhsVar);
        if (lhsValue == rhsValue) {
          Node lhs = getNodeForVariable(lhsVar);
          if(lhs.hasAttribute(ReverseSlack())){
            lhs = lhs.getAttribute(ReverseSlack());
          }
          Node rhs = mkRationalNode((*it).second);

          Node eq = NodeBuilder<2>(kind::EQUAL) << lhs << rhs;

          Debug("arith_lemma") << "Full Set" << endl;
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

  Debug("arith") << "TheoryArith::check end " << checkId << std::endl;

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

void TheoryArith::explain(TNode n, Effort e) {
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

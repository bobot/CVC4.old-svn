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

#include "theory/arith/tab_model_utilities.h"

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
  d_currentTime(DEFAULT_TIMESTAMP),
  d_constants(NodeManager::currentNM()),
  d_partialModel(c),
  d_basicManager(),
  d_activityMonitor(),
  d_diseq(c),
  d_tableau(d_activityMonitor, d_basicManager, d_partialModel),
  d_propagator(d_lemmasQueue),
  d_simplex(d_constants, d_partialModel, d_basicManager,  d_out, d_activityMonitor, d_tableau),
  d_statistics()
{
  incCurrentTime();
  d_preregisteredAtoms.add(d_constants.d_TRUE);
  d_preregisteredAtoms.add(d_constants.d_FALSE);
}

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

TimeStamp TheoryArith::currentTimeStamp() {
  return d_currentTime;
}

void TheoryArith::incCurrentTime(){
  ++d_currentTime;
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
  Debug("arith_preregister")<<"begin arith::preRegisterTerm("<<n<<")"<<endl;

  if(isRelationOperator(n.getKind())){
    d_preregisteredAtoms.add(n);
  }
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

Node TheoryArith::lazySimplifyAndSetup(TNode lit){
  if(getTimeStamp(lit) < currentTimeStamp() ){
    Node simplified = d_simplifier.simplify(lit);

    if(simplified.getKind() == CONST_BOOLEAN){
      return simplified;
    }
    if(simplified.getKind() == EQUAL && getContext()->getLevel() == 0){
      if(d_simplifier.addEquality(simplified)){
        incCurrentTime();
        return d_constants.d_TRUE;
      }
    }

    arithRegisterLit(simplified);
    return simplified;
  }else{
    return lit;
  }
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

void TheoryArith::arithRegisterMonomial(Monomial m){
  const VarList& vl = m.getVarList();

  Node n = vl.getNode();

  if(hasArithVar(n)){ return; }

  bool isStrictlyVarList = n.getKind() == kind::MULT;

  if(isStrictlyVarList){
    d_out->setIncomplete();
  }

  if(isLeaf(n) || isStrictlyVarList){
    ++(d_statistics.d_statUserVariables);
    ArithVar varN = requestArithVar(n,false);
    setupInitialValue(varN);
  }
}

void TheoryArith::arithRegisterLit(TNode lit){
  Node atom = (lit.getKind() == NOT) ? lit[0] : lit;

  Assert(Comparison::isNormalAtom(atom));

  Node negative = NodeBuilder<1>(kind::NOT) << atom;
  if(d_simplifiedNegatations.find(negative) != d_simplifiedNegatations.end()){
    return;
  }

  Comparison cmp = Comparison::parseNormalForm(atom);
  const Polynomial& left = cmp.getLeft();


  for(Polynomial::iterator i = left.begin(), end = left.end();
      i != end; ++i){
    arithRegisterMonomial(*i);
  }

  d_propagator.addAtom(atom);

  //We may need to introduce a slack variable.
  if(!left.singleton() && !(left.getNode()).hasAttribute(Slack())){
    setupSlack(left);
  }
  d_simplifiedNegatations.insert(negative);
}

void TheoryArith::setupSlack(Polynomial left){

  ++(d_statistics.d_statSlackVariables);
  TypeNode real_type = NodeManager::currentNM()->realType();
  Node slack = NodeManager::currentNM()->mkVar(real_type);
  Node leftNode = left.getNode();
  leftNode.setAttribute(Slack(), slack);

  ArithVar varSlack = requestArithVar(slack, true);

  vector<ArithVar> variables;
  vector<Rational> coefficients;

  asVectors(left, coefficients, variables);

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
    //If the variable is basic, assertions may have already happened
    //and updates may have occured before setting this variable up.

    //This can go away if the tableau creation is done at preregister
    //time instead of register
    DeltaRational safeAssignment = TableauModelUtilities::computeRowValue(d_tableau, d_basicManager, d_partialModel, x, true);
    DeltaRational assignment = TableauModelUtilities::computeRowValue(d_tableau, d_basicManager, d_partialModel, x, false);
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

void TheoryArith::resetInternalState(){
  //incCurrentTime();
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
                            << x_i <<" "<< simpKind <<" "<< c_i << ")"
                            << std::endl;
  switch(simpKind){
  case LEQ:
    if (d_partialModel.hasLowerBound(x_i) &&
        d_partialModel.getLowerBound(x_i) == c_i) {
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        NodeBuilder<3> conflict(kind::AND);
        conflict << diseq << assertion
                 << d_partialModel.getLowerConstraint(x_i);
        ++(d_statistics.d_statDisequalityConflicts);
        d_out->conflict((TNode)conflict);
        return true;
      }
    }
  case LT:
    return d_simplex.AssertUpper(x_i, c_i, assertion);
  case GEQ:
    if (d_partialModel.hasUpperBound(x_i) &&
        d_partialModel.getUpperBound(x_i) == c_i) {
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        NodeBuilder<3> conflict(kind::AND);
        conflict << diseq << assertion
                 << d_partialModel.getUpperConstraint(x_i);
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
      if (d_partialModel.hasLowerBound(lhsVar) &&
          d_partialModel.hasUpperBound(lhsVar) &&
          d_partialModel.getLowerBound(lhsVar) == rhsValue &&
          d_partialModel.getUpperBound(lhsVar) == rhsValue) {
        NodeBuilder<3> conflict(kind::AND);
        conflict << assertion << d_partialModel.getLowerConstraint(lhsVar)
                 << d_partialModel.getUpperConstraint(lhsVar);
        d_out->conflict((TNode)conflict);
        return true;
      }
    }
    return false;
  default:
    Unreachable();
    return false;
  }
}
/*
void TheoryArith::debugValidateAssertions(TheoryEngine* te){
  Debug("arith::validate") << "reached" << endl;
  typedef context::CDList<Node>::const_iterator fiterator;
  for(fiterator i = d_facts.begin(), end = d_facts.end(); i != end; ++i){
    Node assertion = *i;
    Node value = getValue(assertion, te);
    Debug("arith::validate::print") << "val:" << assertion << "|->"<< value << endl;
  }
}
*/

void TheoryArith::debugPrintAssertions(){
  Debug("arith::print_assertions") << "Assertions:" << endl;
  for (ArithVar i = 0; i < d_variables.size(); ++ i) {
    if (d_partialModel.hasLowerBound(i)) {
      Node lConstr = d_partialModel.getLowerConstraint(i);
      Debug("arith::print_assertions") << lConstr << endl;
    }
    if (d_partialModel.hasUpperBound(i)) {
      Node uConstr = d_partialModel.getUpperConstraint(i);
      Debug("arith::print_assertions") << uConstr << endl;
    }
  }
  context::CDSet<Node, NodeHashFunction>::iterator it = d_diseq.begin();
  context::CDSet<Node, NodeHashFunction>::iterator it_end = d_diseq.end();
  for(; it != it_end; ++ it) {
    Debug("arith::print_assertions") << *it << endl;
  }
}

void TheoryArith::debugPrintModel(){
  Debug("arith::print_model") << "Model:" << endl;

  for (ArithVar i = 0; i < d_variables.size(); ++ i) {
    Debug("arith::print_model") << d_variables[i]
                                << "("<< i<<")" << " : "
                                << d_partialModel.getAssignment(i);
    if(d_basicManager.isMember(i))
      Debug("arith::print_model") << " (basic)";
    Debug("arith::print_model") << endl;
  }
}

void TheoryArith::splitDisequalities(){
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
      TableauModelUtilities::reinjectVariable(d_tableau, d_basicManager, d_partialModel, lhsVar);
      //d_simplex.reinjectVariable(lhsVar);
    }
    DeltaRational lhsValue = d_partialModel.getAssignment(lhsVar);
    DeltaRational rhsValue = determineRightConstant(eq, kind::EQUAL);
    if (lhsValue == rhsValue) {
      Debug("arith::lemma") << "Splitting on " << eq << endl;
      Debug("arith::lemma") << "LHS value = " << lhsValue << endl;
      Debug("arith::lemma") << "RHS value = " << rhsValue << endl;
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
      d_out->lemma( lemma.andNode(impClosure));
      //One of the splits is "on-demand", this cannot be sent to the queue
      //(thus delayed) until propagation as check() must have some output.
    }
  }
}

bool TheoryArith::ignore(Node lit){
  Node atom = lit.getKind() == kind::NOT ? lit[0] : lit;
  return
    d_preregisteredAtoms.inForest(atom) &&
    !d_preregisteredAtoms.isClassRepresentative(atom);
}

void TheoryArith::check(Effort effortLevel){
  Debug("arith::check") << "TheoryArith::check begun" << std::endl;

  while(!done()){
    Node assertion = get();
    Debug("arith::assertions")<<"arith::assertion "<<assertion<<std::endl;

    if(ignore(assertion)){
      Debug("arith::assertions::ignore") << "(ignore) "
                                         << assertion
                                         << std::endl;
      continue;
    }

    Node simplified = lazySimplifyAndSetup(assertion);
    // There may be a conflict created by the implications.

    // TODO do we add non-preregistered atoms to
    // d_preregistered when we see them?

    if(Debug.isOn("paranoid:check_tableau")){
      TableauModelUtilities::checkTableau(d_tableau, d_basicManager, d_partialModel);
    }
    if(simplified.getKind() == CONST_BOOLEAN){
      if(simplified.getConst<bool>()){
        continue;
      }else{ //conflict
        d_out->conflict(assertion);
        d_partialModel.revertAssignmentChanges();
        return;
      }
    }

    bool conflictDuringAnAssert = assertionCases(simplified);


    if(Debug.isOn("paranoid:check_tableau")){
      TableauModelUtilities::checkTableau(d_tableau, d_basicManager, d_partialModel);
    }

    //if(Debug.isOn("paranoid:check_tableau")){ d_simplex.checkTableau(); }

    if(conflictDuringAnAssert){
      d_partialModel.revertAssignmentChanges();
      return;
    }
  }



  if(Debug.isOn("arith::print_assertions") && fullEffort(effortLevel)) {
    debugPrintAssertions();
  }
  //if(Debug.isOn("arith::validate")) {
  //  debugValidateAssertions(te);
  //}

  if(Debug.isOn("paranoid:check_tableau")){
      TableauModelUtilities::checkTableau(d_tableau, d_basicManager, d_partialModel);
  }
  Node possibleConflict = d_simplex.updateInconsistentVars();


  if(possibleConflict != Node::null()){

    d_partialModel.revertAssignmentChanges();

    d_out->conflict(possibleConflict);

    Debug("arith_conflict") <<"Found a conflict "<< possibleConflict << endl;
  }else{
    d_partialModel.commitAssignmentChanges();

    if (fullEffort(effortLevel)) { splitDisequalities(); }
  }

  if(Debug.isOn("paranoid:check_tableau")){
    TableauModelUtilities::checkTableau(d_tableau, d_basicManager, d_partialModel);
  }
  if(Debug.isOn("arith::print_model")) { debugPrintModel(); }
  Debug("arith::check") << "TheoryArith::check end" << std::endl;
}

Node TheoryArith::getValue(TNode n, TheoryEngine* engine) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::NOT: // 2 args
    return nodeManager->mkConst(! getValue(n[0],engine).getConst<bool>() );

  case kind::VARIABLE: {
    ArithVar var = asArithVar(n);
    if(d_tableau.isEjected(var)){
      //d_simplex.reinjectVariable(var);
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
  //Node eq = NodeBuilder<2>(EQUAL) << lhs << rhs;
  //assertFact(eq);
}

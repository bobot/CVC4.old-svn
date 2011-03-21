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

#include "theory/valuation.h"

#include "util/rational.h"
#include "util/integer.h"
#include "util/boolean_simplification.h"


#include "theory/rewriter.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/arithvar_set.h"

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
typedef expr::Attribute<SlackAttrID, bool> Slack;

TheoryArith::TheoryArith(context::Context* c, OutputChannel& out) :
  Theory(THEORY_ARITH, c, out),
  d_partialModel(c),
  d_userVariables(),
  d_diseq(c),
  d_tableau(),
  d_restartsCounter(0),
  d_initialDensity(1.0),
  d_tableauResetDensity(2.0),
  d_tableauResetPeriod(10),
  d_propagator(c, out),
  d_simplex(d_partialModel, d_tableau),
  d_DELTA_ZERO(0),
  d_statistics()
{}

TheoryArith::~TheoryArith(){}

TheoryArith::Statistics::Statistics():
  d_statUserVariables("theory::arith::UserVariables", 0),
  d_statSlackVariables("theory::arith::SlackVariables", 0),
  d_statDisequalitySplits("theory::arith::DisequalitySplits", 0),
  d_statDisequalityConflicts("theory::arith::DisequalityConflicts", 0),
  d_staticLearningTimer("theory::arith::staticLearningTimer"),
  d_permanentlyRemovedVariables("theory::arith::permanentlyRemovedVariables", 0),
  d_presolveTime("theory::arith::presolveTime"),
  d_initialTableauDensity("theory::arith::initialTableauDensity", 0.0),
  d_avgTableauDensityAtRestart("theory::arith::avgTableauDensityAtRestarts"),
  d_tableauResets("theory::arith::tableauResets", 0),
  d_restartTimer("theory::arith::restartTimer")
{
  StatisticsRegistry::registerStat(&d_statUserVariables);
  StatisticsRegistry::registerStat(&d_statSlackVariables);
  StatisticsRegistry::registerStat(&d_statDisequalitySplits);
  StatisticsRegistry::registerStat(&d_statDisequalityConflicts);
  StatisticsRegistry::registerStat(&d_staticLearningTimer);

  StatisticsRegistry::registerStat(&d_permanentlyRemovedVariables);
  StatisticsRegistry::registerStat(&d_presolveTime);


  StatisticsRegistry::registerStat(&d_initialTableauDensity);
  StatisticsRegistry::registerStat(&d_avgTableauDensityAtRestart);
  StatisticsRegistry::registerStat(&d_tableauResets);
  StatisticsRegistry::registerStat(&d_restartTimer);
}

TheoryArith::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUserVariables);
  StatisticsRegistry::unregisterStat(&d_statSlackVariables);
  StatisticsRegistry::unregisterStat(&d_statDisequalitySplits);
  StatisticsRegistry::unregisterStat(&d_statDisequalityConflicts);
  StatisticsRegistry::unregisterStat(&d_staticLearningTimer);

  StatisticsRegistry::unregisterStat(&d_permanentlyRemovedVariables);
  StatisticsRegistry::unregisterStat(&d_presolveTime);


  StatisticsRegistry::unregisterStat(&d_initialTableauDensity);
  StatisticsRegistry::unregisterStat(&d_avgTableauDensityAtRestart);
  StatisticsRegistry::unregisterStat(&d_tableauResets);
  StatisticsRegistry::unregisterStat(&d_restartTimer);
}

void TheoryArith::staticLearning(TNode n, NodeBuilder<>& learned) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_staticLearningTimer);

  learner.staticLearning(n, learned);
}



ArithVar TheoryArith::findShortestBasicRow(ArithVar variable){
  ArithVar bestBasic = ARITHVAR_SENTINEL;
  uint64_t rowLength = std::numeric_limits<uint64_t>::max();

  Column::iterator basicIter = d_tableau.beginColumn(variable);
  Column::iterator end = d_tableau.endColumn(variable);
  for(; basicIter != end; ++basicIter){
    ArithVar x_j = *basicIter;
    ReducedRowVector& row_j = d_tableau.lookup(x_j);

    Assert(row_j.has(variable));
    if((row_j.size() < rowLength) ||
       (row_j.size() == rowLength && x_j < bestBasic)){
      bestBasic = x_j;
      rowLength = row_j.size();
    }
  }
  return bestBasic;
}


void TheoryArith::preRegisterTerm(TNode n) {
  Debug("arith_preregister") <<"begin arith::preRegisterTerm("<< n <<")"<< endl;
  Kind k = n.getKind();

  bool isStrictlyVarList = k == kind::MULT && VarList::isMember(n);

  if(isStrictlyVarList){
    d_out->setIncomplete();
  }

  if(Variable::isMember(n) || isStrictlyVarList){
    ++(d_statistics.d_statUserVariables);
    ArithVar varN = requestArithVar(n,false);
    setupInitialValue(varN);
  }

  if(isRelationOperator(k)){
    Assert(Comparison::isNormalAtom(n));


    d_propagator.addAtom(n);

    TNode left  = n[0];
    TNode right = n[1];
    if(left.getKind() == PLUS){
      //We may need to introduce a slack variable.
      Assert(left.getNumChildren() >= 2);
      if(!left.getAttribute(Slack())){
        setupSlack(left);
      }
    }
  }
  Debug("arith_preregister") << "end arith::preRegisterTerm("<< n <<")"<< endl;
}


ArithVar TheoryArith::requestArithVar(TNode x, bool basic){
  Assert(isLeaf(x) || x.getKind() == PLUS);
  Assert(!hasArithVar(x));

  ArithVar varX = d_variables.size();
  d_variables.push_back(Node(x));

  d_simplex.increaseMax();

  setArithVar(x,varX);

  d_userVariables.init(varX, !basic);
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
  left.setAttribute(Slack(), true);

  ArithVar varSlack = requestArithVar(left, true);

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

  if(!d_tableau.isBasic(x)){
    d_partialModel.initialize(x, d_DELTA_ZERO);
  }else{
    //If the variable is basic, assertions may have already happened and updates
    //may have occured before setting this variable up.

    //This can go away if the tableau creation is done at preregister
    //time instead of register
    DeltaRational safeAssignment = d_simplex.computeRowValue(x, true);
    DeltaRational assignment = d_simplex.computeRowValue(x, false);
    d_partialModel.initialize(x,safeAssignment);
    d_partialModel.setAssignment(x,assignment);
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
    return asArithVar(left);
  }
}

DeltaRational determineRightConstant(TNode assertion, Kind simpleKind){
  TNode right = getSide<false>(assertion, simpleKind);

  Assert(right.getKind() == CONST_RATIONAL);
  const Rational& noninf = right.getConst<Rational>();

  Rational inf = Rational(Integer(deltaCoeff(simpleKind)));
  return DeltaRational(noninf, inf);
}

Node TheoryArith::disequalityConflict(TNode eq, TNode lb, TNode ub){
  NodeBuilder<3> conflict(kind::AND);
  conflict << eq << lb << ub;
  ++(d_statistics.d_statDisequalityConflicts);
  return conflict;
}

Node TheoryArith::assertionCases(TNode assertion){
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
        Node lb = d_partialModel.getLowerConstraint(x_i);
        return disequalityConflict(diseq, lb , assertion);
      }
    }
  case LT:
    return  d_simplex.AssertUpper(x_i, c_i, assertion);
  case GEQ:
    if (d_partialModel.hasUpperBound(x_i) && d_partialModel.getUpperBound(x_i) == c_i) {
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        Node ub = d_partialModel.getUpperConstraint(x_i);
        return disequalityConflict(diseq, assertion, ub);
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
        Node lb = d_partialModel.getLowerConstraint(lhsVar);
        Node ub = d_partialModel.getUpperConstraint(lhsVar);
        return disequalityConflict(assertion, lb, ub);
      }
    }
    return Node::null();
  default:
    Unreachable();
    return Node::null();
  }
}



void TheoryArith::check(Effort effortLevel){
  Debug("arith") << "TheoryArith::check begun" << std::endl;

  while(!done()){

    Node assertion = get();
    Node possibleConflict = assertionCases(assertion);

    if(!possibleConflict.isNull()){
      d_partialModel.revertAssignmentChanges();
      Node simpleConflict  = BooleanSimplification::simplifyConflict(possibleConflict);

      Debug("arith::conflict") << "conflict   " << possibleConflict << endl
                               << "simplified " << simpleConflict << endl;
      d_out->conflict(simpleConflict);
      return;
    }
  }

  if(Debug.isOn("arith::print_assertions")) {
    debugPrintAssertions();
  }

  Node possibleConflict = d_simplex.updateInconsistentVars();
  if(possibleConflict != Node::null()){
    d_partialModel.revertAssignmentChanges();
    d_simplex.clearDeducedBounds();

    Node simpleConflict  = BooleanSimplification::simplifyConflict(possibleConflict);

    Debug("arith::conflict") << "conflict   " << possibleConflict << endl
                             << "simplified " << simpleConflict << endl;
    d_out->conflict(simpleConflict);
  }else{
    d_partialModel.commitAssignmentChanges();

    if (fullEffort(effortLevel)) {
      splitDisequalities();
    }
  }

  if(Debug.isOn("paranoid:check_tableau")){ d_simplex.checkTableau(); }
  if(Debug.isOn("arith::print_model")) { debugPrintModel(); }
  Debug("arith") << "TheoryArith::check end" << std::endl;
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
    DeltaRational lhsValue = d_partialModel.getAssignment(lhsVar);
    DeltaRational rhsValue = determineRightConstant(eq, kind::EQUAL);
    if (lhsValue == rhsValue) {
      Debug("arith_lemma") << "Splitting on " << eq << endl;
      Debug("arith_lemma") << "LHS value = " << lhsValue << endl;
      Debug("arith_lemma") << "RHS value = " << rhsValue << endl;
      Node ltNode = NodeBuilder<2>(kind::LT) << lhs << rhs;
      Node gtNode = NodeBuilder<2>(kind::GT) << lhs << rhs;
      Node lemma = NodeBuilder<3>(OR) << eq << ltNode << gtNode;

      // // < => !>
      // Node imp1 = NodeBuilder<2>(kind::IMPLIES) << ltNode << gtNode.notNode();
      // // < => !=
      // Node imp2 = NodeBuilder<2>(kind::IMPLIES) << ltNode << eq.notNode();
      // // > => !=
      // Node imp3 = NodeBuilder<2>(kind::IMPLIES) << gtNode << eq.notNode();
      // // All the implication
      // Node impClosure = NodeBuilder<3>(kind::AND) << imp1 << imp2 << imp3;

      ++(d_statistics.d_statDisequalitySplits);
      d_out->lemma(lemma);
    }
  }
}

/**
 * Should be guarded by at least Debug.isOn("arith::print_assertions").
 * Prints to Debug("arith::print_assertions")
 */
void TheoryArith::debugPrintAssertions() {
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

void TheoryArith::debugPrintModel(){
  Debug("arith::print_model") << "Model:" << endl;

  for (ArithVar i = 0; i < d_variables.size(); ++ i) {
    Debug("arith::print_model") << d_variables[i] << " : " <<
      d_partialModel.getAssignment(i);
    if(d_tableau.isBasic(i))
      Debug("arith::print_model") << " (basic)";
    Debug("arith::print_model") << endl;
  }
}

void TheoryArith::explain(TNode n) {
  Kind simpKind = simplifiedKind(n);
  ArithVar var = determineLeftVariable(n, simpKind);

  TNode bound = TNode::null();
  switch(simpKind){
  case LT: case LEQ:
    bound = d_partialModel.getUpperConstraint(var);
    break;
  case GEQ: case GT:
    bound = d_partialModel.getLowerConstraint(var);
    break;
  default:
    Unreachable();
  }
  AlwaysAssert(bound.getKind() == kind::AND);
  d_out->explanation(bound, true);
}

void TheoryArith::propagate(Effort e) {
  if(quickCheckOrMore(e)){
    while(d_simplex.hasMoreLemmas()){
      Node lemma = d_simplex.popLemma();
      Node simpleLemma = BooleanSimplification::simplifyClause(lemma);
      d_out->lemma(simpleLemma);
    }
    while(d_simplex.hasMoreDeducedUpperBounds()){
      ArithVar var = d_simplex.popDeducedUpperBound();
      Node varAsNode = asNode(var);
      const DeltaRational& ub = d_partialModel.getUpperBound(var);
      Assert(ub.getInfinitesimalPart() <= 0 );
      Kind kind = ub.getInfinitesimalPart() < 0 ? LT : LEQ;
      Node ubAsNode = NodeBuilder<2>(kind) << varAsNode << mkRationalNode(ub.getNoninfinitesimalPart());
      Node bestImplied = d_propagator.getBestImpliedUpperBound(ubAsNode);
      if(!bestImplied.isNull()){
        d_out->propagate(bestImplied);
      }
    }
    while(d_simplex.hasMoreDeducedLowerBounds()){
      ArithVar var = d_simplex.popDeducedLowerBound();
      Node varAsNode = asNode(var);
      const DeltaRational& lb = d_partialModel.getLowerBound(var);
      Assert(lb.getInfinitesimalPart() >= 0 );
      Kind kind = lb.getInfinitesimalPart() > 0 ? GT : GEQ;
      Node lbAsIneq = NodeBuilder<2>(kind) << varAsNode << mkRationalNode(lb.getNoninfinitesimalPart());
      Node bestImplied = d_propagator.getBestImpliedLowerBound(lbAsIneq);
      if(!bestImplied.isNull()){
        d_out->propagate(bestImplied);
      }
    }
  }
}

Node TheoryArith::getValue(TNode n, Valuation* valuation) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::VARIABLE: {
    ArithVar var = asArithVar(n);

    if(d_removedRows.find(var) != d_removedRows.end()){
      Node eq = d_removedRows.find(var)->second;
      Assert(n == eq[0]);
      Node rhs = eq[1];
      return getValue(rhs, valuation);
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
      mkConst( valuation->getValue(n[0]) == valuation->getValue(n[1]) );

  case kind::PLUS: { // 2+ args
    Rational value(0);
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      value += valuation->getValue(*i).getConst<Rational>();
    }
    return nodeManager->mkConst(value);
  }

  case kind::MULT: { // 2+ args
    Rational value(1);
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      value *= valuation->getValue(*i).getConst<Rational>();
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
    return nodeManager->mkConst( valuation->getValue(n[0]).getConst<Rational>() /
                                 valuation->getValue(n[1]).getConst<Rational>() );

  case kind::LT: // 2 args
    return nodeManager->mkConst( valuation->getValue(n[0]).getConst<Rational>() <
                                 valuation->getValue(n[1]).getConst<Rational>() );

  case kind::LEQ: // 2 args
    return nodeManager->mkConst( valuation->getValue(n[0]).getConst<Rational>() <=
                                 valuation->getValue(n[1]).getConst<Rational>() );

  case kind::GT: // 2 args
    return nodeManager->mkConst( valuation->getValue(n[0]).getConst<Rational>() >
                                 valuation->getValue(n[1]).getConst<Rational>() );

  case kind::GEQ: // 2 args
    return nodeManager->mkConst( valuation->getValue(n[0]).getConst<Rational>() >=
                                 valuation->getValue(n[1]).getConst<Rational>() );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryArith::notifyEq(TNode lhs, TNode rhs) {

}

void TheoryArith::notifyRestart(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_restartTimer);

  if(Debug.isOn("paranoid:check_tableau")){ d_simplex.checkTableau(); }

  ++d_restartsCounter;
  if(d_restartsCounter % d_tableauResetPeriod == 0){
    double currentDensity = d_tableau.densityMeasure();
    d_statistics.d_avgTableauDensityAtRestart.addEntry(currentDensity);
    if(currentDensity >= d_tableauResetDensity * d_initialDensity){

      ++d_statistics.d_tableauResets;
      d_tableauResetPeriod += s_TABLEAU_RESET_INCREMENT;
      d_tableauResetDensity += .2;
      d_tableau = d_initialTableau;
    }
  }
}

bool TheoryArith::entireStateIsConsistent(){
  typedef std::vector<Node>::const_iterator VarIter;
  for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
    ArithVar var = asArithVar(*i);
    if(!d_partialModel.assignmentIsConsistent(var)){
      d_partialModel.printModel(var);
      cerr << "Assignment is not consistent for " << var << *i << endl;
      return false;
    }
  }
  return true;
}

void TheoryArith::permanentlyRemoveVariable(ArithVar v){
  //There are 3 cases
  // 1) v is non-basic and is contained in a row
  // 2) v is basic
  // 3) v is non-basic and is not contained in a row
  //  It appears that this can happen after other variables have been removed!
  //  Tread carefullty with this one.

  bool noRow = false;

  if(!d_tableau.isBasic(v)){
    ArithVar basic = findShortestBasicRow(v);

    if(basic == ARITHVAR_SENTINEL){
      noRow = true;
    }else{
      Assert(basic != ARITHVAR_SENTINEL);
      d_tableau.pivot(basic, v);
    }
  }

  if(d_tableau.isBasic(v)){
    Assert(!noRow);

    //remove the row from the tableau
    ReducedRowVector* row  = d_tableau.removeRow(v);
    Node eq = row->asEquality(d_arithVarToNodeMap);

    if(Debug.isOn("row::print")) row->printRow();
    if(Debug.isOn("tableau")) d_tableau.printTableau();
    Debug("arith::permanentlyRemoveVariable") << eq << endl;
    delete row;

    Assert(d_tableau.getRowCount(v) == 0);
    Assert(d_removedRows.find(v) ==  d_removedRows.end());
    d_removedRows[v] = eq;
  }

  Debug("arith::permanentlyRemoveVariable") << "Permanently removed variable "
                                            << v << ":" << asNode(v) << endl;
  ++(d_statistics.d_permanentlyRemovedVariables);
}

void TheoryArith::presolve(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_presolveTime);

  typedef std::vector<Node>::const_iterator VarIter;
  for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
    Node variableNode = *i;
    ArithVar var = asArithVar(variableNode);
    if(d_userVariables.isMember(var) && !d_propagator.hasAnyAtoms(variableNode)){
      //The user variable is unconstrained.
      //Remove this variable permanently
      permanentlyRemoveVariable(var);
    }
  }

  d_initialTableau = d_tableau;
  d_initialDensity = d_initialTableau.densityMeasure();
  d_statistics.d_initialTableauDensity.setData(d_initialDensity);

  if(Debug.isOn("paranoid:check_tableau")){ d_simplex.checkTableau(); }

  static int callCount = 0;
  Debug("arith::presolve") << "TheoryArith::presolve #" << (callCount++) << endl;

  learner.clear();

  check(FULL_EFFORT);
}

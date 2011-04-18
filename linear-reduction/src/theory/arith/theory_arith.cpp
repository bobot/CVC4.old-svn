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

#include "theory/arith/reduce.h"

#include <map>
#include <stdint.h>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

struct SlackAttrID;
typedef expr::Attribute<SlackAttrID, Node> Slack;

struct IgnoreAtomID;
typedef expr::Attribute<IgnoreAtomID, bool> IgnoreAtom;


TheoryArith::TheoryArith(int id, context::Context* c, OutputChannel& out) :
  Theory(id, c, out),
  d_setupOnline(false),
  d_constants(NodeManager::currentNM()),
  d_partialModel(c),
  d_basicManager(),
  d_activityMonitor(),
  d_diseq(c),
  d_tableau(d_activityMonitor, d_basicManager),
  d_rewriter(&d_constants),
  d_propagator(c, out),
  d_simplex(d_constants, d_partialModel, d_basicManager,  d_out, d_activityMonitor, d_tableau),
  d_oneVar(ARITHVAR_SENTINEL),
  d_statistics()
{
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

void TheoryArith::setupAtom(TNode n){
  Assert(Comparison::isNormalAtom(n));

  if(d_setupAtoms.find(n) != d_setupAtoms.end()){
    if (d_setupOnline) {
      Debug("arith::late::addition")
        << "SPECIAL CASE: " << n << endl
        << (d_setupOnline ? "online" : "not online") << endl;
      Node reverse;
      if (n.getAttribute(ReverseSimplified(), reverse)) {
        Node iff = NodeBuilder<2>(kind::IFF) << n << reverse;
        d_out->lemma(iff);
      }
    }
    return;
  }else{
    d_setupAtoms.insert(n);
  }

  TNode left  = n[0];
  TNode right = n[1];

  if(d_setupOnline){
    Assert(!n.hasAttribute(Simplified()));
    n.setAttribute(Simplified(), n);

    Assert(!n.hasAttribute(ReverseSimplified()));
    n.setAttribute(ReverseSimplified(), n);
  }

  d_propagator.addAtom(n);

  if(left.getKind() == PLUS){
    //We may need to introduce a slack variable.
    Assert(left.getNumChildren() >= 2);
    if(!left.hasAttribute(Slack())){
      setupSlack(left);
    }
  }
}

void TheoryArith::setupAtomList(const vector<Node>& atoms){
  vector<Node>::const_iterator it = atoms.begin();
  vector<Node>::const_iterator it_end = atoms.end();
  for(; it != it_end; ++it){
    Node atom = simplifiedAtom(*it);
    if(atom.getKind() != CONST_BOOLEAN){
      setupAtom(atom);
    }
  }
}

void TheoryArith::preRegisterTerm(TNode n) {

  Debug("arith::preregister") <<"begin arith::preRegisterTerm("<< n <<")"<< endl;

  Kind k = n.getKind();

  bool isStrictlyVarList = k == kind::MULT && VarList::isMember(n);

  if(isStrictlyVarList && d_setupOnline){
    d_out->setIncomplete();
  }

  if(isTheoryLeaf(n) || (isStrictlyVarList && d_setupOnline)){
    ++(d_statistics.d_statUserVariables);
    ArithVar varN = requestArithVar(n,false);
    setupInitialValue(varN);
  }

  if(isRelationOperator(k)){
    Assert(Comparison::isNormalAtom(n));

    d_atoms.push_back(n);
    if(d_setupOnline){
      setupAtom(n);
    }
  }
  Debug("arith::preregister") << "end arith::preRegisterTerm("<< n <<")"<< endl;
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

Node simplifyRec(const map<Node, Node>& simpMap, Node arithNode){
  if(simpMap.find(arithNode) != simpMap.end()){
    return simpMap.find(arithNode)->second;
  }else if(arithNode.getNumChildren() > 0){
    Node::iterator node_it = arithNode.begin();
    Node::iterator node_it_end = arithNode.end();
    NodeBuilder<> nb(arithNode.getKind());
    for(; node_it != node_it_end; ++node_it) {
      nb << simplifyRec(simpMap, *node_it);
    }
    return nb;
  }else{
    return arithNode;
  }
}

Node TheoryArith::fakeRewrite(Node arithNode){
  bool isConstant = arithNode.getMetaKind() == metakind::CONSTANT ||
    (arithNode.getKind() == kind::NOT && arithNode[0].getKind() == CONST_BOOLEAN);

  if(isConstant || isTheoryLeaf(arithNode)){
    // MAybe not handled in postRewrite
    RewriteResponse rr = postRewrite(arithNode, true);
    Assert(rr.isDone()); // This may not be valid
    return rr.getNode();
  }else{
    Assert(arithNode.getNumChildren() > 0);
    NodeBuilder<> nb(arithNode.getKind());
    Node::iterator it = arithNode.begin();
    Node::iterator it_end = arithNode.end();
    for(; it!= it_end; ++it){
      nb << fakeRewrite(*it);
    }
    Node simplified = nb;

    if(simplified.getKind() == kind::NOT || simplified.getKind() == CONST_BOOLEAN){
      return simplified;
    }

    // MAUBE not handled NOT true
    RewriteResponse rr = postRewrite(simplified, true);
    Assert(rr.isDone()); // This may not be valid
    return rr.getNode();
  }
}

Node TheoryArith::simplify(const map<Node, Node>& simpMap, Node arithNode){
  Node simp = simplifyRec(simpMap, arithNode);
  if(simp != arithNode){
    //cout << "Do not check in" << endl;
    return fakeRewrite(simp);
  }else{
    return arithNode;
  }
}

Node TheoryArith::simplifyFP(const map<Node, Node>& simpMap, Node arithNode){
  // WAY SIMPLER
  Node simp = simplify(simpMap, arithNode);
  if(simp != arithNode){
    return simplifyFP(simpMap, simp);
  }else{
    return arithNode;
  }
}

map<Node, Node> TheoryArith::detectSimplifications(const set<Node>& asserted){
  //For each equality in the set asserted
  //  add it to simplifications after doing guassian elimination

  // PASs IN THIS MAP
  map<Node, Node> simplifications;

  Debug("arith::detectSimplifications") << "<detectSimplifications>" << endl;

  set<Node>::iterator it = asserted.begin();
  set<Node>::iterator it_end = asserted.end();
  for(; it != it_end; ++it){
    Node assertion = *it;
    if(assertion.getKind() == EQUAL){
      //Reduce the equation using the current simplifications
      //To get row reduced form "for free" use the simplification
      //routine to simplify the left hand side.
      Node simplifiedEq = simplifyFP(simplifications, assertion);
      Debug("arith::detectSimplifications")
        << assertion << " |-> "  << simplifiedEq << endl;

      Comparison eq = Comparison::parseNormalForm(simplifiedEq);
      const Polynomial& lhs = eq.getLeft();
      const Constant& rhs = eq.getRight();
      Monomial free = Monomial::mkZero();

      Polynomial::iterator monomials_it = lhs.begin();
      Polynomial::iterator monomials_it_end = lhs.end();

      for(; monomials_it != monomials_it_end; ++monomials_it){
        Monomial curr = *monomials_it;
        const VarList& vl = curr.getVarList();
        if(vl.singleton()){
          // MAYBE USELESS
          if(simplifications.find(vl.getNode()) == simplifications.end() ){
            free = curr;
            break;
          }
        }
      }

      if(free.isZero()){
        Debug("arith::detectSimplifications") << "free.isZero() ";
	// MAYBE CONFLICT
      }else{
        const Constant& coeff = free.getConstant();
        const VarList& var = free.getVarList();

        Assert( coeff.getValue() != 0 );

        /* Assertion must have the following form:
         *   (coeff * var + \sum monomials_i = rhs)
         * Introduce the following simplification:
         *   var |-> (rhs - \sum monomials_i )/ coeff
         */
        Polynomial newRhs = Polynomial::parsePolynomial(rhs.getNode()) - lhs;
        newRhs = newRhs + free;

        Node coeffInv = mkRationalNode(coeff.getValue().inverse());
        Monomial coeffInv_mono = Monomial::parseMonomial(coeffInv);
        newRhs = newRhs * coeffInv_mono;

        Debug("arith::detectSimplifications")
          << "Adding simplification " << var.getNode() << " |-> "
          << newRhs.getNode() << endl;

        simplifications.insert(make_pair(var.getNode(), newRhs.getNode()));
      }
    }
  }

  // simplifications now contains row reduced form.
  // The following is to get simplifications from row reduced form
  // to row reduced echelon form.
  map<Node, Node>::iterator simp_it = simplifications.begin();
  map<Node, Node>::iterator simp_it_end = simplifications.end();
  while(simp_it != simp_it_end){
    Node var = simp_it->first;
    Polynomial p = Polynomial::parsePolynomial( simp_it->second );
    // var |-> p

    bool requiresNoSimplification = true;

    Polynomial::iterator monomials_it = p.begin();
    Polynomial::iterator monomials_it_end = p.end();
    for(; monomials_it != monomials_it_end; ++monomials_it){
      Monomial m = *monomials_it;
      Node varInRow = m.getVarList().getNode();

      map<Node, Node>::iterator varInRow_it = simplifications.find(varInRow);
      if(varInRow_it != simp_it_end ){
        Monomial coeff = Monomial::parseMonomial(m.getConstant().getNode());
        //If this is the case varInRow should be simplified out of p
        Polynomial row = Polynomial::parsePolynomial(varInRow_it->second);
        Polynomial tmp0 = (row * coeff);
        Polynomial tmp1 = tmp0 - m;
        Polynomial newP = p + tmp1;

        Debug("arith::detectSimplifications")
          << "RREF reduction " << var << " was " << p.getNode() << endl
          << "\t" << "now " << newP.getNode() << endl;

        simplifications.erase(simp_it);
        pair<map<Node, Node>::iterator, bool>  res;
        res = simplifications.insert(make_pair(var, newP.getNode()));

        simp_it = res.first;
        simp_it_end = simplifications.end();

        requiresNoSimplification = false;
        break;
      }
    }

    //Only reached if the row for p is in row reduced form.
    if(requiresNoSimplification){
      // Wouldnt need to do this if polynomials have the order of variables
      ++simp_it;
    }
  }

  Debug("arith::detectSimplifications") << "</detectSimplifications>" << endl;

  return simplifications;
}

void TheoryArith::simplifyAtoms(const vector<Node>& atoms, const map<Node, Node>& simplifications){
  for(unsigned i = 0; i < atoms.size(); ++i){
    Node atom =  atoms[i];
    Node simplified = simplify(simplifications, atom);

    Debug("arith::simplifyAtoms") << atom << " simplifies to " << simplified << endl;

    atom.setAttribute(Simplified(), simplified);
    if(simplified.getKind() == CONST_BOOLEAN){
      //atom or its negation is now implied (WHAT ABOUT THE NEGATIONS OF CONSTANTS)
      atom.setAttribute(IgnoreAtom(), true);
      continue;
    }else {    //Note the reverse direction may not be unique.
      if(simplified.hasAttribute(ReverseSimplified())){
        Node reverse = simplified.getAttribute(ReverseSimplified());
        Node iff = NodeBuilder<2>(kind::IFF) << atom << reverse;
        Debug("arith::simplifyAtoms") << "Adding: " << iff << endl;
        d_out->lemma(iff); //Do not need to unsimplify


        atom.setAttribute(IgnoreAtom(), true);
      }else{
        simplified.setAttribute(ReverseSimplified(), atom);

        //This is required in case a lemma uses this atom in the future
        simplified.setAttribute(Simplified(), simplified);

        d_simplifiedAtoms.push_back(simplified);

        setupAtom(simplified);
      }
    }
  }
}

Node flattenAnd(Node andNode){
  Assert(andNode.getKind() == AND);
  NodeBuilder<> nb(AND);

  Node::iterator and_it = andNode.begin();
  Node::iterator and_it_end = andNode.end();
  for(; and_it != and_it_end; ++and_it){
    Node curr = *and_it;
    if(curr.getKind() == AND){
      Node::iterator curr_it = curr.begin();
      Node::iterator curr_it_end = curr.end();
      for(; curr_it != curr_it_end; ++curr_it){
        nb << *curr_it;
      }
    }else{
      nb << curr;
    }
  }
  Node result(nb);
  if(result == andNode){
    return andNode;
  }else{
    return flattenAnd(result);
  }
}
bool TheoryArith::detectConflicts(set<Node>& asserted,
                                  const map<Node, Node>& simplifications,
                                  Node simpJustification){
  set<Node>::iterator it = asserted.begin();
  set<Node>::iterator it_end = asserted.end();
  for(; it != it_end; ++it){
    Node assertion = *it;
    Node simplified = simplify(simplifications, assertion);
    bool simplifiesToFalse =
      simplified.getKind() == CONST_BOOLEAN &&
      simplified.getConst<bool>() == false;
    bool simplifiesToNotTrue =
      simplified.getKind() == NOT &&
      simplified[0].getKind() == CONST_BOOLEAN &&
      simplified[0].getConst<bool>() == true;

    if(simplifiesToFalse || simplifiesToNotTrue){
        Node conflict = NodeBuilder<2>(AND)<< simpJustification << assertion;
        Node conflictClause = flattenAnd(conflict);
        d_out->conflict(conflictClause);
        //Do not unsimplify. assertion does not have ReverseSimplify() yet
        return true;
    }
  }
  return false;
}

void TheoryArith::propagateSimplifiedAtoms(const set<Node>& asserted, const vector<Node>& atoms){
  for(unsigned i = 0, size = atoms.size(); i < size; ++i){
    Node atom = atoms[i];
    Node simplified = simplifiedAtom(atom);

    // I am worried about this for some reason
    Assert(simplified.getKind() != kind::NOT);

    if(simplified.getKind() == CONST_BOOLEAN){
      if(asserted.find(atom) == asserted.end() ){
        if(simplified.getConst<bool>()){
          Debug("arith::propagateSimplifiedAtoms") << "propagating " << atom << endl;
          d_toPropagate.push(atom);
          //d_out->propagate(atom); // explanations, A THING OF THE PAST!
          //Do not need to unsimplify
        }else{
          Debug("arith::propagateSimplifiedAtoms") << "propagating " << atom.notNode() << endl;
          d_toPropagate.push(atom.notNode());
          //d_out->propagate(atom.notNode());
        }
      }
    }
  }
}

Node mkAnd(const set<Node>& nodes){
  switch(nodes.size()){
  case 0:
    return mkBoolNode(true);
  case 1:
    return *nodes.begin();
  default:
    {
      NodeBuilder<> andNB(AND);
      set<Node>::const_iterator it = nodes.begin();
      set<Node>::const_iterator it_end = nodes.end();
      for(;it != it_end; ++it){
        andNB << *it;
      }
      return andNB;
    }
  }
}

//Requires d_propagator to be setup with constraints.
vector<ArithVar> TheoryArith::detectUnconstrained(){
  vector<ArithVar> unconstrained;
  for(ArithVar v = 0; v < d_variables.size(); ++v){
    Node left = d_variables[v];

    if(!d_propagator.hasConstraint(left)){
      unconstrained.push_back(v);
    }
  }

  return unconstrained;
}

void TheoryArith::ejectList(const vector<ArithVar>& unconstrained){
  vector<ArithVar>::const_iterator unconstrained_it = unconstrained.begin();
  vector<ArithVar>::const_iterator unconstrained_it_end = unconstrained.end();
  for(; unconstrained_it != unconstrained_it_end; ++ unconstrained_it){
    ArithVar var = *unconstrained_it;
    Debug("arith::ejectList") << "unconstrained " << var << " or " << d_variables[var] << endl;
    //cout << "Do not check this in!" << endl;
  }
}

void TheoryArith::presolve(){
  Debug("arith::presolve") << "TheoryArith::presolve begin" << endl;
  //setupOneVar();

  set<Node> asserted;

  fact_iterator fact_it = facts_begin();
  fact_iterator fact_it_end = facts_end();
  for(; fact_it != fact_it_end; ++fact_it){
    Node assertion = *fact_it;
    Debug("arith::presolve") << "presolve assertion " << assertion << endl;
    asserted.insert(assertion);
  }

  // REnAME TO SOLVE_EQ
  map<Node, Node> simplifications = detectSimplifications(asserted);

  if(Debug.isOn("arith::presolve::simplifications")){
    map<Node, Node>::const_iterator it = simplifications.begin();
    map<Node, Node>::const_iterator it_end = simplifications.end();
    for(; it != it_end; ++it){
      Node key = (*it).first;
      Node value = (*it).second;
      Node eq = NodeBuilder<2>(EQUAL) << key << value;
      Debug("arith::presolve::simplifications") << eq  << endl;
    }
  }

  //This is an overapproximation of the knowledge needed to prove the
  //simplification map just generated.
  // Dont likE
  Node justifySimplifications = mkAnd(asserted);

  bool conflictAfterSimplifying = detectConflicts(asserted, simplifications, justifySimplifications);
  if(conflictAfterSimplifying){
    return;
  }
  //Assume no asserted value is simplified to false

  //Simplify ever atom in the system and construct the Simplified attribute.
  simplifyAtoms(d_atoms, simplifications);

  //propagate atoms that have been simplified to true
  //This requires IgnoreAtom() and Simplify() attributes to be setup
  propagateSimplifiedAtoms(asserted, d_atoms);


  //PIVOT OUT UNCONSTRAINED VARIABLES
  vector<ArithVar> unconstrained = detectUnconstrained();
  ejectList(unconstrained);

  d_setupOnline = true;

  check(FULL_EFFORT);
  Debug("arith::presolve") << "arith::presolve end"<< endl;
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
  Debug("arith::registerTerm") << "registerTerm(" << tn << ")" << endl;
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
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        NodeBuilder<3> conflictNB(kind::AND);
        conflictNB << diseq << assertion << d_partialModel.getLowerConstraint(x_i);
        ++(d_statistics.d_statDisequalityConflicts);
        Node conflict(conflictNB);
        d_out->conflict(unsimplifyBoolean(conflict));
        return true;
      }
    }
  case LT:
    return d_simplex.AssertUpper(x_i, c_i, assertion);
  case GEQ:
    if (d_partialModel.hasUpperBound(x_i) && d_partialModel.getUpperBound(x_i) == c_i) {
      Node diseq = assertion[0].eqNode(assertion[1]).notNode();
      if (d_diseq.find(diseq) != d_diseq.end()) {
        NodeBuilder<3> conflictNB(kind::AND);
        conflictNB << diseq << assertion << d_partialModel.getUpperConstraint(x_i);
        ++(d_statistics.d_statDisequalityConflicts);
        Node conflict (conflictNB);
        d_out->conflict(unsimplifyBoolean(conflict));
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
        NodeBuilder<3> conflictNB(kind::AND);
        conflictNB << assertion;
        conflictNB << d_partialModel.getLowerConstraint(lhsVar);
        conflictNB << d_partialModel.getUpperConstraint(lhsVar);
        Node conflict(conflictNB);
        d_out->conflict(unsimplifyBoolean(conflict));
      }
    }
    return false;
  default:
    Unreachable();
    return false;
  }
}

void TheoryArith::checkAllDisequalities(){
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
      d_out->lemma(lemma.andNode(impClosure));
    }
  }
}

void TheoryArith::check(Effort effortLevel){

  //In order to delay performing the needed setup until after
  //presolve(), quickCheck must be disabled.
  if(!d_setupOnline) return;

  Debug("arith") << "TheoryArith::check begun" << getContext()->getLevel() << std::endl;

  while(!done()){

    Node assertion = get();

    //Check if the literal should be ignored.
    if(assertion.getKind() == NOT){
      if(assertion[0].getAttribute(IgnoreAtom())){
        Debug("arith::check::ignoring")
          << "ignoring "<< assertion << endl
          << "\t should be covered by "<< simplifiedAtom(assertion[0]).notNode() << endl;
        continue;
      }
    }else{
      if(assertion.getAttribute(IgnoreAtom())){
        Debug("arith::check::ignoring")
          << "ignoring "<< assertion << endl
          << "\t should be covered by "<< simplifiedAtom(assertion) << endl;
        continue;
      }
    }

    Node assertionSimp;
    if(assertion.getKind() == NOT){
      assertionSimp = simplifiedAtom(assertion[0]).notNode();
    }else{
      assertionSimp = simplifiedAtom(assertion);
    }

    //d_propagator.assertLiteral(assertion);
    bool conflictDuringAnAssert = assertionCases(assertionSimp);

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

  Node possibleConflict = d_simplex.updateInconsistentVars();
  if(possibleConflict != Node::null()){

    d_partialModel.revertAssignmentChanges();

    if(Debug.isOn("arith::print-conflict"))
      Debug("arith_conflict") << (possibleConflict) << std::endl;

    d_out->conflict(unsimplifyBoolean(possibleConflict));

    Debug("arith_conflict") <<"Found a conflict "<< possibleConflict << endl;
  }else{
    d_partialModel.commitAssignmentChanges();

    if (fullEffort(effortLevel)) {
      checkAllDisequalities();
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

void TheoryArith::explain(TNode n, Effort e) {
  // Node explanation = d_propagator.explain(n);
  // Debug("arith") << "arith::explain("<<explanation<<")->"
  //                << explanation << endl;
  // d_out->explanation(explanation, true);

  Unreachable();
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
  while(!d_toPropagate.empty()){
    Node lit = d_toPropagate.front();
    d_out->propagate(lit);
    d_toPropagate.pop();
  }
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

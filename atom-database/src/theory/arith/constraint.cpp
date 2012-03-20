
#include "cvc4_private.h"

#include "util/integer.h"
#include "util/rational.h"

#include <ostream>


namespace CVC4 {
namespace theory {
namespace arith {

NewAtomDatabase::NewAtomDatabase(context::Context* userContext, context::Context* satContext){
  d_emptyProof = d_proofs.size();
  d_proofs.push_back(NullConstraint);
}

Node ConstraintValue::split(){
  Assert(isEquality() || isDisequality());

  bool isEq = isEquality();

  Constraint eq = isEq ? c : d_negation;
  Constraint diseq = isEq ? d_negation : c;

  TNode eqNode = eq->getLiteral();
  Assert(eqNode.getKind() == kind::EQUAL);
  TNode lhs = eqNode[0];
  TNode rhs = eqNode[1];

  Node ltNode = NodeBuilder<2>(kind::LT) << lhs << rhs;
  Node gtNode = NodeBuilder<2>(kind::GT) << lhs << rhs;

  Node lemma = NodeBuilder<3>(OR) << eqNode << ltNode << gtNode;

  ConstraintDatabase* db = d_eq->d_database;

  db->d_splitWatches.push_back(SplitWatch(diseq));
  db->d_splitWatches.push_back(SplitWatch(eq));
  eq->d_split = true;
  diseq->d_split = true;

  return lemma;
}

Constraint ConstraintDatabase::addLiteral(Node literal, ArithVar v){
  bool isNot = (literal.getKind() == NOT);
  TNode atom = isNot ? literal[0] : literal;

  Constraint atomC = addAtom(atom, v);

  return isNot ? atomC->d_negation : atomC;
}

Constraint ConstraintDatabase::addAtom(TNode atom, ArithVar v){
  Assert(!hasLiteral(atom));
  Assert(v < d_varDatabases.size());

  PerVariableDatabase& vd = d_varDatabases[v];

  Node negation = atom.notNode();

  ConstraintP posC = allocateConstraint(atom, v);
  ConstraintP negC = allocateConstraint(negation, v);

  posC->d_negation = negC;
  negC->d_negation = posC;

  vd.d_constraints.insert(posC);

  if(!negC->isDisequality()){
    vd.d_constraints.insert(negC);
  }

  return posC;
}




ConstraintP NewAtomDatabase::allocateConstraint(Node literal, ArithVar v){
  ConstraintType k = simplifiedKind(literal);
  DeltaRational value = getDeltaRationalValue(literal, k);


  ConstraintP c = new Constraint(k, literal, v, value);

  ConstraintListIterator iter = d_constraints.insert(d_constraints.end(), c);
  c->d_pos = iter;

  d_nodetoConstraintMap[literal] = c;

  return c;
}

ConstraintP NewAtomDatabase::lookup(Node literal){
  NodetoConstraintPMap::iterator iter = d_nodetoConstraintMap.find(literal);
  if(iter == d_nodetoConstraintMap.end()){
    return ConstraintPSentinel;
  }else{
    return iter->second;
  }
}

void NewAtomDatabase::addVariable(ArithVar v){
  Assert(v == d_varDatabases.size());
  d_varDatabases.push_back(PerVariableDatabase(v));
}



void NewAtomDatabase::addVariable(ArithVar v){
  Assert(v == d_varDatabases.size());
  d_varDatabases.push_back(PerVariableDatabase(v));
}

void ConstraintC::markAsTrue(){
  Assert(d_proof == ProofIdSentinel);
  d_proofConstraintWatchList.push_back(ProofConstraintWatch(this, d_database->d_emptyProof));
}

void ConstraintC::markAsTrue(ConstraintC imp){
  Assert(d_proof == ProofIdSentinel);
  d_database->d_proofs.push_back(ConstraintPSentinel);
  d_database->d_proofs.push_back(imp);
  ProofId proof = d_proofs.size();
  d_database->d_proofs.push_back(this);

  d_proofConstraintWatchList.push_back(ProofConstraintWatch(this, proof));
}

void ConstraintC::markAsTrue(ConstraintC impA, ConstraintC impB){
  Assert(d_proof == ProofIdSentinel);
  d_database->d_proofs.push_back(ConstraintPSentinel);
  d_database->d_proofs.push_back(impA);
  d_database->d_proofs.push_back(impB);
  ProofId proof = d_proofs.size();
  d_database->d_proofs.push_back(this);

  d_proofConstraintWatchList.push_back(ProofConstraintWatch(this, proof));
}

void ConstraintC::markAsTrue(const vector<ConstraintC>& a){
  Assert(d_proof == ProofIdSentinel);
  d_database->d_proofs.push_back(ConstraintPSentinel);
  for(vector<ConstraintC>::const_iterator i = a.begin(), end = a.end(); i != end; ++i){
    ConstraintC c_i = *i;
    d_database->d_proofs.push_back(c_i);
  }

  ProofId proof = d_proofs.size();
  d_database->d_proofs.push_back(this);

  d_proofConstraintWatchList.push_back(ProofConstraintWatch(this, proof));
}

SortedConstraintSet& ConstraintC::constraintSet() const{
  return d_database->d_varDatabases[d_variable].d_constraints;
}

void ConstraintC::propagateLowerboundRange(Constraint prev){
  Assert(isLowerBound());
  Assert(prev->isLowerBound());
  // If prev == NULL, intrepret this as x >= -infty
  Assert(prev == NULL || d_value > prev->d_value);

  // It is now known that x >= d_value
  // Assuming it was known that x >= prev->d_value, and d_value > prev->d_value
  // Implies x >= c, where d_value > c > prev->d_value
  // Implies x != c, where d_value > c

  SortedConstraintSetIterator i = (prev == NULL) ? constraintSet().begin() : (prev->d_variablePosition)+1;
  SortedConstraintSetIterator end = d_variablePosition;
  for(;i != end; ++i){
    const ValueCollection& curr = *i;

    Assert( (*curr.d_value) < d_value);

    if(curr.hasLowerBound()){
      d_database->internalPropagate(curr.d_lowerBound, this);
    }else if(curr.hasEquality()){
      Constraint diseq = (curr.d_equality)->d_negation;
      d_database->internalPropagate(diseq, this);
    }
  }
}

void ConstraintC::propagateUpperboundRange(Constraint prev){
  Assert(isUpperBound());
  Assert(prev->isUpperBound());
  // If prev == NULL, intrepret this as x <= infty
  Assert(prev == NULL || d_value < prev->d_value);

  // It is now known that x <= d_value
  // Assuming it was known that x <= prev->d_value, and d_value < prev->d_value
  // Implies x <= c, where d_value < c < prev->d_value
  // Implies x != c, where d_value < c

  SortedConstraintSetIterator i = d_variablePosition+1;
  SortedConstraintSetIterator end = (prev == NULL) ? constraintSet().end() : prev->d_variablePosition;

  for(; i != end; ++i){
    const ValueCollection& curr = *i;
    Assert(d_value < *(curr.d_value));
    if(curr.hasUpperBound()){
      d_database->internalPropagate(curr.d_upperBound, this);
    }else if(curr.hasEquality()){
      Constraint diseq = (curr.d_equality)->d_negation;
      d_database->internalPropagate(diseq, this);
    }
  }
}

void ConstraintC::propagateEquality(ConstraintP prevUB, ConstraintP prevLB){
  Assert(isEquality());
  Assert(prevUB->isUpperBound());
  Assert(prevLB->isLowerBound());

  // If prev == NULL, intrepret this as x <= infty
  Assert(prevLB == NULL || prevLB->d_value <= d_value);
  Assert(prevUB == NULL || d_value <= prevUB->d_value);
  Assert(prevLB == NULL || prevUB == NULL || prevLB->d_value <= prevUB->d_value);

  // It is now known that x = d_value
  // Assuming it was known that prevLB->d_value <= x <= prev->d_value
  // Implies x >= c, where d_value >= c
  // Implies x != c, where d_value != c

  SortedConstraintSetIterator i = (prevLB == NULL) ? constraintSet().begin() : prevLB->d_variablePosition + 1;
  SortedConstraintSetIterator mid = d_variablePosition;
  SortedConstraintSetIterator end = (prevUB == NULL) ? constraintSet().end() : prevUB->d_variablePosition;

  for(; i != mid; ++i){
    const ConstraintValue& curr = *i;
    Assert(d_value >= curr->d_value);
    if(curr->isLowerBound()){
      d_database->internalPropagate(curr, this);
    }else if(curr->isEquality()){
      d_database->internalPropagate(curr->d_negation, this);
    }
  }
  Assert(i == mid);
  ++i;
  for(; i != end; ++i){
    ConstraintP curr = *i;
    Assert(d_value <= curr->d_value);
    if(curr->isUpperBound()){
      d_database->internalPropagate(curr, this);
    }else if(curr->isEquality()){
      d_database->internalPropagate(curr->d_negation, this);
    }
  }
}

void NewAtomDatabase::internalPropagate(ConstraintP consequent, ConstraintP antecedent){
  if(consequent->hasProof()){
    Debug("arith::db") << "Already has proof " << consequent->d_node << endl;
  }else{
    Debug("arith::db") << "Propagating (implies " << antecedent->d_node << " " << consequent->d_node << ")"<< endl;
    consequent->markAsTrue(antecdent);
  }
}


bool ConstraintP::isSelfExplaining() const {
  return d_database->d_proofs[d_proof] == NULL;
}

Node NewAtomDatabase::explain(ConstraintP c){
  Assert(c->hasProof());

  if(c->isSelfExplaining()){
    return c->d_node;
  }else{
    ProofId p = c->d_proof;
    if(d_proofs[p-1] == NULL){
      ConstraintP antecedent = d_proofs[p];
      return antecedent->d_node;
    }else{
      NodeBuilder<> nb(AND);
      explain(nb, c);
      return nb;
    }
  }
}

void NewAtomDatabase::recExplain(NodeBuilder<>& nb, ConstraintP c){
  Assert(c->hasProof());

  if(c->isSelfExplaining()){
    nb << c->d_node;
  }else{
    ProofId p = c->d_proof;
    ConstraintP antecedent = d_proofs[p];

    for(; antecedent != NULL; actecedent = d_proofs[--p] ){
      recExplain(nb, antecedent);
    }
  }
}


bool ConstraintDatabase::containsLiteral(TNode lit) const{
  return d_nodetoConstraintMap.find(lit) != d_nodetoConstraintMap.end();
}

ConstraintP ConstraintDatabase::getUpperBound(ArithVar v, const DeltaRational& b, bool strict) const{
  ValueCollection key(d_value);
  const SortedConstraintSet& constraints = d_varDatabases[v].d_constraints;
  SortedConstraintSet::const_iterator bv = constraints.lower_bound(value);
  if(constraints.end() == bv){
    return NullConstraint;
  }

  //x <= b
  //x <= c, b <= c

  int cmp = b.cmp(*((*bv).d_value));

  if(!strict && cmp < 0){
    // There is no ValueCollection at this exact d_value.
    ++bv;
    Assert( b > (*((*bv).d_value)));
  }else if(strict && cmp <= 0){
    ++bv;
  }
  SortedConstraintSet::const_iterator end = constraints.end();

  for(; bv != end; ++bv){
    const ValueCollection& curr = *bv;
    if(curr.hasUpperBound()){
      return curr.d_upperBound;
    }
  }
  return NullConstraint;
}

ConstraintP ConstraintDatabase::getLowerBound(ArithVar v, const DeltaRational& b, bool strict) const{
  ValueCollection key(d_value);
  const SortedConstraintSet& constraints = d_varDatabases[v].d_constraints;
  SortedConstraintSet::const_iterator bv = constraints.lower_bound(value);
  if(constraints.end() == bv){
    return NullConstraint;
  }

  //x >= b
  //x = c, b <= c
  int cmp = b.cmp(*((*bv).d_value));
  if(strict && b == *((*bv).d_value)){
    --bv;
  }

  for(cmp)
}

ConstraintP ConstraintDatabase::getBestImpliedUpperBound(ArithVar v, const DeltaRational& b) const{
  return getUpperBound(v, b, false);
}

ConstraintP ConstraintDatabase::getWeakerImpliedUpperBound(ArithVar v, const DeltaRational& b) const{
  return getUpperBound(v, b, true);
}


Node ConstraintDatabase::getWeakerImpliedUpperBound(TNode upperBound) const{

}

Node ConstraintDatabase::getWeakerImpliedLowerBound(TNode lowerBound) const{

}


}/* arith namespace */
}/* theory namespace */
}/* CVC4 namespace */

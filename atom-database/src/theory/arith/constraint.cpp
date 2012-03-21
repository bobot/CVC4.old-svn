
#include "cvc4_private.h"
#include "theory/arith/constraint.h"
#include "theory/arith/arith_utilities.h"

#include <ostream>
#include <algorithm>

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

ArithVar ValueCollection::getVariable() const{
  Assert(!empty());
  return nonNull()->getVariable();
}


const DeltaRational& ValueCollection::getValue() const{
  Assert(!empty());
  return nonNull()->getValue();
}

void ValueCollection::add(Constraint c){
  Assert(c != NullConstraint);
  Assert(c->getType() != Disequality);

  Assert(empty() || getVariable() == c->getVariable());
  Assert(empty() || getValue() == c->getValue());

  switch(c->getType()){
  case LowerBound:
    Assert(!hasLowerBound());
    d_lowerBound = c;
    break;
  case Equality:
    Assert(!hasEquality());
    d_equality = c;
    break;
  case UpperBound:
    Assert(!hasUpperBound());
    d_upperBound = c;
    break;
  default:
    Unreachable();
  }
}

void ValueCollection::remove(ConstraintType t){
  Assert(t != Disequality);

  switch(t){
  case LowerBound:
    Assert(d_lowerBound != NullConstraint);
    d_lowerBound = NullConstraint;
    break;
  case Equality:
    Assert(d_equality != NullConstraint);
    d_equality = NullConstraint;
    break;
  case UpperBound:
    Assert(d_upperBound != NullConstraint);
    d_upperBound = NullConstraint;
    break;
  default:
    Unreachable();
  }
}

bool ValueCollection::empty() const{
  return hasLowerBound() || hasUpperBound() || hasEquality();
}

Constraint ValueCollection::nonNull() const{
  if(hasLowerBound()){
    return d_lowerBound;
  }else if(hasUpperBound()){
    return d_upperBound;
  }else if(hasEquality()){
    return d_equality;
  }else {
    return NullConstraint;
  }
}

ConstraintValue::~ConstraintValue() {
  Assert(safeToGarbageCollect());

  ValueCollection& vc =  d_variablePosition->second;

  if(d_type != Disequality){
    vc.remove(d_type);

    if(vc.empty()){
      SortedConstraintMap& perVariable = d_database->getVariableSCM(getVariable());
      perVariable.erase(d_variablePosition);
    }
  }

  if(hasLiteral()){
    d_database->d_nodetoConstraintMap.erase(getLiteral());
  }

  d_database->d_constraints.erase(d_pos);
}

void ConstraintValue::setPreregistered() {
  Assert(d_preregistered = false);
  d_database->d_preregisteredWatches.push_back(PreregisteredWatch(this));
  d_preregistered = true;
}

bool ConstraintValue::isSelfExplaining() const {
  return d_proof != ProofIdSentinel && d_database->d_proofs[d_proof] == NullConstraint;
}

bool ConstraintValue::sanityChecking(Node n) const {
  Kind k = simplifiedKind(n);
  DeltaRational right = determineRightConstant(n, k);

  TNode left = getSide<true>(n, k);
  const ArithVarNodeMap& av2node = d_database->getArithVarNodeMap();

  if(av2node.hasArithVar(left) &&
     av2node.asArithVar(left) == getVariable() &&
     getValue() == right){
    switch(getType()){
    case LowerBound:
      return k == GT || k == GEQ;
    case UpperBound:
      return k == LT || k == LEQ;
    case Equality:
      return k == EQUAL;
    case Disequality:
      return k == DISTINCT;

    default:
      Unreachable();
    }
  }else{
    return false;
  }
}

ConstraintDatabase::ConstraintDatabase(context::Context* userContext, context::Context* satContext, const ArithVarNodeMap& av2nodeMap)
  : d_constraints(),
    d_toPropagate(satContext),
    d_proofs(satContext, false),
    d_proofWatches(satContext),
    d_preregisteredWatches(satContext),
    d_splitWatches(userContext),
    d_varDatabases(),
    d_av2nodeMap(av2nodeMap)
{
  d_emptyProof = d_proofs.size();
  d_proofs.push_back(NullConstraint);
}

bool ConstraintDatabase::emptyDatabase(const std::vector<PerVariableDatabase>& vec){
  std::vector<PerVariableDatabase>::const_iterator first = vec.begin();
  std::vector<PerVariableDatabase>::const_iterator last = vec.end();
  return std::find_if(first, last, PerVariableDatabase::IsEmpty) == last;
}

ConstraintDatabase::~ConstraintDatabase(){
  ConstraintListIterator i = d_constraints.begin(), end = d_constraints.end();
  for(; i != end; ++i){
    Constraint c = *i;
    delete c;
  }
  d_constraints.clear();

  Assert(d_nodetoConstraintMap.empty());
  Assert(emptyDatabase(d_varDatabases));
}

Node ConstraintValue::split(){
  Assert(isEquality() || isDisequality());

  bool isEq = isEquality();

  Constraint eq = isEq ? this : d_negation;
  Constraint diseq = isEq ? d_negation : this;

  TNode eqNode = eq->getLiteral();
  Assert(eqNode.getKind() == kind::EQUAL);
  TNode lhs = eqNode[0];
  TNode rhs = eqNode[1];

  Node ltNode = NodeBuilder<2>(kind::LT) << lhs << rhs;
  Node gtNode = NodeBuilder<2>(kind::GT) << lhs << rhs;

  Node lemma = NodeBuilder<3>(OR) << eqNode << ltNode << gtNode;

  ConstraintDatabase* db = eq->d_database;

  db->d_splitWatches.push_back(SplitWatch(diseq));
  db->d_splitWatches.push_back(SplitWatch(eq));
  eq->d_split = true;
  diseq->d_split = true;

  return lemma;
}

Constraint ConstraintDatabase::addLiteral(TNode literal, ArithVar v){
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

  Constraint posC = allocateConstraint(atom, v);
  Constraint negC = allocateConstraint(negation, v);

  posC->d_negation = negC;
  negC->d_negation = posC;

  vd.d_constraints.insert(posC);

  if(!negC->isDisequality()){
    vd.d_constraints.insert(negC);
  }

  return posC;
}




Constraint ConstraintDatabase::allocateConstraint(Node literal, ArithVar v){
  ConstraintType k = simplifiedKind(literal);
  DeltaRational value = getDeltaRationalValue(literal, k);

  Constraint c = new Constraint(k, literal, v, value);

  ConstraintListIterator iter = d_constraints.insert(d_constraints.end(), c);
  c->d_pos = iter;

  d_nodetoConstraintMap[literal] = c;

  return c;
}

Constraint ConstraintDatabase::lookup(Node literal){
  NodetoConstraintMap::iterator iter = d_nodetoConstraintMap.find(literal);
  if(iter == d_nodetoConstraintMap.end()){
    return ConstraintSentinel;
  }else{
    return iter->second;
  }
}

void ConstraintDatabase::addVariable(ArithVar v){
  Assert(v == d_varDatabases.size());
  d_varDatabases.push_back(PerVariableDatabase(v));
}



void ConstraintDatabase::addVariable(ArithVar v){
  Assert(v == d_varDatabases.size());
  d_varDatabases.push_back(PerVariableDatabase(v));
}

void ContraintValue::markAsTrue(){
  Assert(d_proof == ProofIdSentinel);
  d_proofConstraintWatchList.push_back(ProofConstraintWatch(this, d_database->d_emptyProof));
}

void ContraintValue::markAsTrue(Constraint imp){
  Assert(d_proof == ProofIdSentinel);
  d_database->d_proofs.push_back(ConstraintSentinel);
  d_database->d_proofs.push_back(imp);
  ProofId proof = d_proofs.size();
  d_database->d_proofs.push_back(this);

  d_proofConstraintWatchList.push_back(ProofConstraintWatch(this, proof));
}

void ContraintValue::markAsTrue(Constraint impA, Constraint impB){
  Assert(d_proof == ProofIdSentinel);
  d_database->d_proofs.push_back(ConstraintSentinel);
  d_database->d_proofs.push_back(impA);
  d_database->d_proofs.push_back(impB);
  ProofId proof = d_proofs.size();
  d_database->d_proofs.push_back(this);

  d_proofConstraintWatchList.push_back(ProofConstraintWatch(this, proof));
}

void ContraintValue::markAsTrue(const vector<Constraint>& a){
  Assert(d_proof == ProofIdSentinel);
  d_database->d_proofs.push_back(ConstraintSentinel);
  for(vector<Constraint>::const_iterator i = a.begin(), end = a.end(); i != end; ++i){
    Constraint c_i = *i;
    d_database->d_proofs.push_back(c_i);
  }

  ProofId proof = d_proofs.size();
  d_database->d_proofs.push_back(this);

  d_proofConstraintWatchList.push_back(ProofConstraintWatch(this, proof));
}

SortedConstraintSet& ContraintValue::constraintSet() const{
  return d_database->d_varDatabases[d_variable].d_constraints;
}

void ConstraintValue::propagateLowerboundRange(Constraint prev){
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

void ConstraintValue::propagateUpperboundRange(Constraint prev){
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

void ConstraintValue::propagateEquality(Constraint prevUB, Constraint prevLB){
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
    Constraint curr = *i;
    Assert(d_value <= curr->d_value);
    if(curr->isUpperBound()){
      d_database->internalPropagate(curr, this);
    }else if(curr->isEquality()){
      d_database->internalPropagate(curr->d_negation, this);
    }
  }
}

void ConstraintDatabase::internalPropagate(Constraint consequent, Constraint antecedent){
  if(consequent->hasProof()){
    Debug("arith::db") << "Already has proof " << consequent->d_node << endl;
  }else{
    Debug("arith::db") << "Propagating (implies " << antecedent->d_node << " " << consequent->d_node << ")"<< endl;
    consequent->markAsTrue(antecdent);
  }
}


bool Constraint::isSelfExplaining() const {
  return d_database->d_proofs[d_proof] == NULL;
}

Node ConstraintDatabase::explain(Constraint c){
  Assert(c->hasProof());

  if(c->isSelfExplaining()){
    return c->d_node;
  }else{
    ProofId p = c->d_proof;
    if(d_proofs[p-1] == NULL){
      Constraint antecedent = d_proofs[p];
      return antecedent->d_node;
    }else{
      NodeBuilder<> nb(AND);
      explain(nb, c);
      return nb;
    }
  }
}

void ConstraintValue::recExplain(NodeBuilder<>& nb, Constraint c){
  Assert(c->hasProof());

  if(c->isSelfExplaining()){
    nb << c->d_node;
  }else{
    ProofId p = c->d_proof;
    Constraint antecedent = d_proofs[p];

    for(; antecedent != NULL; actecedent = d_proofs[--p] ){
      recExplain(nb, antecedent);
    }
  }
}


bool ConstraintDatabase::containsLiteral(TNode lit) const{
  return d_nodetoConstraintMap.find(lit) != d_nodetoConstraintMap.end();
}

// Constraint ConstraintDatabase::getUpperBound(ArithVar v, const DeltaRational& b, bool strict) const{
//   ValueCollection key(d_value);
//   const SortedConstraintSet& constraints = d_varDatabases[v].d_constraints;
//   SortedConstraintSet::const_iterator bv = constraints.lower_bound(value);
//   if(constraints.end() == bv){
//     return NullConstraint;
//   }

//   //x <= b
//   //x <= c, b <= c

//   int cmp = b.cmp(*((*bv).d_value));

//   if(!strict && cmp < 0){
//     // There is no ValueCollection at this exact d_value.
//     ++bv;
//     Assert( b > (*((*bv).d_value)));
//   }else if(strict && cmp <= 0){
//     ++bv;
//   }
//   SortedConstraintSet::const_iterator end = constraints.end();

//   for(; bv != end; ++bv){
//     const ValueCollection& curr = *bv;
//     if(curr.hasUpperBound()){
//       return curr.d_upperBound;
//     }
//   }
//   return NullConstraint;
// }

// Constraint ConstraintDatabase::getLowerBound(ArithVar v, const DeltaRational& b, bool strict) const{
//   ValueCollection key(d_value);
//   const SortedConstraintSet& constraints = d_varDatabases[v].d_constraints;
//   SortedConstraintSet::const_iterator bv = constraints.lower_bound(value);
//   if(constraints.end() == bv){
//     return NullConstraint;
//   }

//   //x >= b
//   //x = c, b <= c
//   int cmp = b.cmp(*((*bv).d_value));
//   if(strict && b == *((*bv).d_value)){
//     --bv;
//   }

//   for(cmp)
// }

// Constraint ConstraintDatabase::getBestImpliedUpperBound(ArithVar v, const DeltaRational& b) const{
//   return getUpperBound(v, b, false);
// }

// Constraint ConstraintDatabase::getWeakerImpliedUpperBound(ArithVar v, const DeltaRational& b) const{
//   return getUpperBound(v, b, true);
// }


// Node ConstraintDatabase::getWeakerImpliedUpperBound(TNode upperBound) const{

// }

// Node ConstraintDatabase::getWeakerImpliedLowerBound(TNode lowerBound) const{

// }



}/* arith namespace */
}/* theory namespace */
}/* CVC4 namespace */

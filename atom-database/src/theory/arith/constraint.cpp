
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

bool ValueCollection::hasConstraintType(ConstraintType t) const{
  switch(t){
  case LowerBound:
    return hasLowerBound();
  case UpperBound:
    return hasUpperBound();
  case Equality:
    return hasEquality();
  case Disequality:
    return hasDisequality();
  default:
    Unreachable();
  }
}

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
  case Disequality:
    Assert(!hasDisequality());
    d_disequality = c;
    break;
  default:
    Unreachable();
  }
}

void ValueCollection::remove(ConstraintType t){
  switch(t){
  case LowerBound:
    Assert(hasLowerBound());
    d_lowerBound = NullConstraint;
    break;
  case Equality:
    Assert(hasEquality());
    d_equality = NullConstraint;
    break;
  case UpperBound:
    Assert(hasUpperBound());
    d_upperBound = NullConstraint;
    break;
  case Disequality:
    Assert(hasDisequality());
    d_disequality = NullConstraint;
    break;
  default:
    Unreachable();
  }
}

bool ValueCollection::empty() const{
  return hasLowerBound() || hasUpperBound() || hasEquality() || hasDisequality();
}

Constraint ValueCollection::nonNull() const{
  //This can be optimized by caching, but this is not necessary yet!
  /* "Premature optimization is the root of all evil." */
  if(hasLowerBound()){
    return d_lowerBound;
  }else if(hasUpperBound()){
    return d_upperBound;
  }else if(hasEquality()){
    return d_equality;
  }else if(hasDisequality()){
    return d_disequality;
  }else{
    return NullConstraint;
  }
}
void ConstraintValue::initialize(ConstraintDatabase* db, SortedConstraintMapIterator v, ConstraintListIterator pos, Constraint negation){
    d_database = db;
    d_variablePosition = v;
    d_pos = pos;
    d_negation = negation;
  }
ConstraintValue::~ConstraintValue() {
  Assert(safeToGarbageCollect());

  ValueCollection& vc =  d_variablePosition->second;
  vc.remove(getType());

  if(vc.empty()){
    SortedConstraintMap& perVariable = d_database->getVariableSCM(getVariable());
    perVariable.erase(d_variablePosition);
  }

  if(hasLiteral()){
    d_database->d_nodetoConstraintMap.erase(getLiteral());
  }

  d_database->d_constraints.erase(d_pos);
}

void ConstraintValue::setPreregistered() {
  Assert(!isPreregistered());
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

void ConstraintDatabase::addVariable(ArithVar v){
  Assert(v == d_varDatabases.size());
  d_varDatabases.push_back(PerVariableDatabase(v));
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

bool ConstraintDatabase::hasLiteral(TNode literal) const {
  return lookup(literal) != NullConstraint;
}

Constraint ConstraintDatabase::addLiteral(TNode literal){
  Assert(!hasLiteral(literal));
  bool isNot = (literal.getKind() == NOT);
  TNode atom = isNot ? literal[0] : literal;

  Constraint atomC = addAtom(atom);

  return isNot ? atomC->d_negation : atomC;
}

Constraint ConstraintDatabase::allocateConstraintForLiteral(ArithVar v, Node literal){
  Kind kind = simplifiedKind(literal);
  ConstraintType type = constraintTypeOfLiteral(kind);
  DeltaRational dr = determineRightConstant(literal, kind);
  return new ConstraintValue(v, type, dr);
}

Constraint ConstraintDatabase::addAtom(TNode atom){
  Assert(!hasLiteral(atom));

  ArithVar v = d_av2nodeMap.asArithVar(atom[0]);

  Node negation = atom.notNode();  

  Constraint posC = allocateConstraintForLiteral(v, atom);

  SortedConstraintMap& scm = getVariableSCM(posC->getVariable());
  pair<SortedConstraintMapIterator, bool> insertAttempt;
  insertAttempt = scm.insert(make_pair(posC->getValue(), ValueCollection()));
  
  SortedConstraintMapIterator posI = insertAttempt.first;
  // If the attempt succeeds, i points to a new empty ValueCollection
  // If the attempt fails, i points to a pre-existing ValueCollection

  if(posI->second.hasConstraintType(posC->getType())){
    //This is the situation where the Constraint exists, but
    //the literal has not been  associated with it.
    Constraint hit = posI->second.getConstraint(posC->getType());
    delete posC;

    hit->setLiteral(atom);
    hit->d_negation->setLiteral(negation);
    return hit;
  }else{
    Constraint negC = allocateConstraintForLiteral(v, negation);

    ConstraintListIterator posIter = d_constraints.insert(d_constraints.end(), posC);
    ConstraintListIterator negIter = d_constraints.insert(d_constraints.end(), negC);

    SortedConstraintMapIterator negI;

    if(posC->isEquality()){
      negI = posI;
    }else{
      Assert(posC->isLowerBound() || posC->isUpperBound());

      pair<SortedConstraintMapIterator, bool> negInsertAttempt;
      negInsertAttempt = scm.insert(make_pair(negC->getValue(),
                                              ValueCollection::mkFromConstraint(negC)));
      //This should always succeed as the DeltaRational for the negation is unique!
      Assert(negInsertAttempt.second);

      negI = negInsertAttempt.first;
    }

    posC->initialize(this, posI, posIter, negC);
    negC->initialize(this, negI, negIter, posC);

    posC->setLiteral(atom);
    negC->setLiteral(negation);

    return posC;
  }
}

ConstraintType constraintTypeOfLiteral(Kind k){
  switch(k){
  case LT:
  case LEQ:
    return UpperBound;
  case GT:
  case GEQ:
    return LowerBound;
  case EQUAL:
    return Equality;
  case DISTINCT:
    return Disequality;
  default:
    Unreachable();
  }
}

Constraint ConstraintDatabase::lookup(TNode literal) const{
  NodetoConstraintMap::const_iterator iter = d_nodetoConstraintMap.find(literal);
  if(iter == d_nodetoConstraintMap.end()){
    return NullConstraint;
  }else{
    return iter->second;
  }
}


void ConstraintValue::markAsTrue(){
  Assert(truthIsUnknown());
#warning "this may be too strict"
  Assert(hasLiteral());
  Assert(isPreregistered());
  d_database->d_proofWatches.push_back(ProofWatch(this));
  d_proof = d_database->d_emptyProof;
}

void ConstraintValue::markAsTrue(Constraint imp){
  Assert(truthIsUnknown());
  Assert(imp->hasProof());

  d_database->d_proofs.push_back(NullConstraint);
  d_database->d_proofs.push_back(imp);
  ProofId proof = d_database->d_proofs.size();
  d_database->d_proofWatches.push_back(ProofWatch(this));
  d_proof = proof;
}

void ConstraintValue::markAsTrue(Constraint impA, Constraint impB){
  Assert(truthIsUnknown());
  Assert(impA->hasProof());
  Assert(impB->hasProof());

  d_database->d_proofs.push_back(NullConstraint);
  d_database->d_proofs.push_back(impA);
  d_database->d_proofs.push_back(impB);
  ProofId proof = d_database->d_proofs.size();

  d_database->d_proofWatches.push_back(ProofWatch(this));
  d_proof = proof;
}

void ConstraintValue::markAsTrue(const vector<Constraint>& a){
  Assert(truthIsUnknown());
  d_database->d_proofs.push_back(NullConstraint);
  for(vector<Constraint>::const_iterator i = a.begin(), end = a.end(); i != end; ++i){
    Constraint c_i = *i;
    Assert(c_i->hasProof());
    d_database->d_proofs.push_back(c_i);
  }

  ProofId proof = d_database->d_proofs.size();

  d_database->d_proofWatches.push_back(ProofWatch(this));
  d_proof = proof;
}

SortedConstraintMap& ConstraintValue::constraintSet(){
  Assert(d_database->variableDatabaseIsSetup(d_variable));
  return d_database->d_varDatabases[d_variable].d_constraints;
}

// void ConstraintValue::propagateLowerboundRange(Constraint prev){
//   Assert(isLowerBound());
//   Assert(prev->isLowerBound());
//   // If prev == NULL, intrepret this as x >= -infty
//   Assert(prev == NullConstraint || d_value > prev->d_value);

//   // It is now known that x >= d_value
//   // Assuming it was known that x >= prev->d_value, and d_value > prev->d_value
//   // Implies x >= c, where d_value > c > prev->d_value
//   // Implies x != c, where d_value > c

//   SortedConstraintSetIterator i = (prev == NULL) ? constraintSet().begin() : (prev->d_variablePosition)+1;
//   SortedConstraintSetIterator end = d_variablePosition;
//   for(;i != end; ++i){
//     const ValueCollection& curr = *i;

//     Assert( (*curr.d_value) < d_value);

//     if(curr.hasLowerBound()){
//       d_database->internalPropagate(curr.d_lowerBound, this);
//     }else if(curr.hasDisequality()){
//       Constraint diseq = curr.d_disequality;
//       d_database->internalPropagate(diseq, this);
//     }
//   }
// }

// void ConstraintValue::propagateUpperboundRange(Constraint prev){
//   Assert(isUpperBound());
//   Assert(prev->isUpperBound());
//   // If prev == NULL, intrepret this as x <= infty
//   Assert(prev == NULL || d_value < prev->d_value);

//   // It is now known that x <= d_value
//   // Assuming it was known that x <= prev->d_value, and d_value < prev->d_value
//   // Implies x <= c, where d_value < c < prev->d_value
//   // Implies x != c, where d_value < c

//   SortedConstraintSetIterator i = d_variablePosition+1;
//   SortedConstraintSetIterator end = (prev == NULL) ? constraintSet().end() : prev->d_variablePosition;

//   for(; i != end; ++i){
//     const ValueCollection& curr = *i;
//     Assert(d_value < *(curr.d_value));
//     if(curr.hasUpperBound()){
//       d_database->internalPropagate(curr.d_upperBound, this);
//     }else if(curr.hasEquality()){
//       Constraint diseq = (curr.d_equality)->d_negation;
//       d_database->internalPropagate(diseq, this);
//     }
//   }
// }

// void ConstraintValue::propagateEquality(Constraint prevUB, Constraint prevLB){
//   Assert(isEquality());
//   Assert(prevUB->isUpperBound());
//   Assert(prevLB->isLowerBound());

//   // If prev == NULL, intrepret this as x <= infty
//   Assert(prevLB == NULL || prevLB->d_value <= d_value);
//   Assert(prevUB == NULL || d_value <= prevUB->d_value);
//   Assert(prevLB == NULL || prevUB == NULL || prevLB->d_value <= prevUB->d_value);

//   // It is now known that x = d_value
//   // Assuming it was known that prevLB->d_value <= x <= prev->d_value
//   // Implies x >= c, where d_value >= c
//   // Implies x != c, where d_value != c

//   SortedConstraintSetIterator i = (prevLB == NULL) ? constraintSet().begin() : prevLB->d_variablePosition + 1;
//   SortedConstraintSetIterator mid = d_variablePosition;
//   SortedConstraintSetIterator end = (prevUB == NULL) ? constraintSet().end() : prevUB->d_variablePosition;

//   for(; i != mid; ++i){
//     const ConstraintValue& curr = *i;
//     Assert(d_value >= curr->d_value);
//     if(curr->isLowerBound()){
//       d_database->internalPropagate(curr, this);
//     }else if(curr->isEquality()){
//       d_database->internalPropagate(curr->d_negation, this);
//     }
//   }
//   Assert(i == mid);
//   ++i;
//   for(; i != end; ++i){
//     Constraint curr = *i;
//     Assert(d_value <= curr->d_value);
//     if(curr->isUpperBound()){
//       d_database->internalPropagate(curr, this);
//     }else if(curr->isEquality()){
//       d_database->internalPropagate(curr->d_negation, this);
//     }
//   }
// }

void ConstraintValue::internalPropagate(Constraint antecedent){
  Assert(!negationHasProof());

  if(hasProof()){
    Debug("arith::db") << "Already has proof " << this << endl;
  }else{
    markAsTrue(antecedent);
  }
}

Node ConstraintValue::explain() const{
  Assert(hasProof());

  if(isSelfExplaining()){
    return getLiteral();
  }else{
    if(d_database->d_proofs[d_proof-1] == NullConstraint){
      Constraint antecedent = d_database->d_proofs[d_proof];
      return antecedent->explain();
    }else{
      NodeBuilder<> nb(AND);
      recExplain(nb, this);
      return nb;
    }
  }
}

void ConstraintValue::recExplain(NodeBuilder<>& nb, const ConstraintValue * const c){
  Assert(c->hasProof());

  if(c->isSelfExplaining()){
    nb << c->getLiteral();
  }else{
    ProofId p = c->d_proof;
    const context::CDList<Constraint>& d_proofs = c->d_database->d_proofs;
    Constraint antecedent = d_proofs[p];
    
    for(; antecedent != NullConstraint; antecedent = d_proofs[--p] ){
      recExplain(nb, antecedent);
    }
  }
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

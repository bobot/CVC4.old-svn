
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

ConstraintValue::ConstraintValue(ArithVar x,  ConstraintType t, const DeltaRational& v)
  : d_variable(x),
    d_type(t),
    d_value(v),
    d_database(NULL),
    d_literal(Node::null()),
    d_negation(NullConstraint),
    d_canBePropagated(false),
    d_assertedToTheTheory(false),
    d_proof(ProofIdSentinel),
    d_split(false),
    d_variablePosition()
{
  Assert(!initialized());
}


std::ostream& operator<<(std::ostream& o, const Constraint c){
  return o << *c;
}

std::ostream& operator<<(std::ostream& o, const ConstraintType t){
  switch(t){
  case LowerBound:
    return o << ">=";
  case UpperBound:
    return o << "<=";
  case Equality:
    return o << "=";
  case Disequality:
    return o << "!=";
  default:
    Unreachable();
  }
}

std::ostream& operator<<(std::ostream& o, const ConstraintValue& c){
  o << c.getVariable() << ' ' << c.getType() << ' ' << c.getValue();
  if(c.hasLiteral()){
    o << "(node " << c.getLiteral() << ')';
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const ValueCollection& vc){
  o << "{";
  bool pending = false;
  if(vc.hasEquality()){
    o << "eq: " << vc.getEquality();
    pending = true;
  }
  if(vc.hasLowerBound()){
    if(pending){
      o << ", ";
    }
    o << "lb: " << vc.getLowerBound();
    pending = true;
  }
  if(vc.hasUpperBound()){
    if(pending){
      o << ", ";
    }
    o << "ub: " << vc.getUpperBound();
    pending = true;
  }
  if(vc.hasDisequality()){
    if(pending){
      o << ", ";
    }
    o << "de: " << vc.getDisequality();
  }
  return o << "}";
}

void ConstraintValue::debugPrint() const {
  cout << *this << endl;
}

void ValueCollection::push_into(std::vector<Constraint>& vec) const {
  Debug("arith::constraint") << "push_into " << *this << endl;
  if(hasEquality()){
    vec.push_back(d_equality);
  }
  if(hasLowerBound()){
    vec.push_back(d_lowerBound);
  }
  if(hasUpperBound()){
    vec.push_back(d_upperBound);
  }
  if(hasDisequality()){
    vec.push_back(d_disequality);
  }
}

ValueCollection ValueCollection::mkFromConstraint(Constraint c){
  ValueCollection ret;
  Assert(ret.empty());
  switch(c->getType()){
  case LowerBound:
    ret.d_lowerBound = c;
    break;
  case UpperBound:
    ret.d_upperBound = c;
    break;
  case Equality:
    ret.d_equality = c;
    break;
  case Disequality:
    ret.d_disequality = c;
    break;
  default:
    Unreachable();
  }
  return ret;
}

bool ValueCollection::hasConstraintOfType(ConstraintType t) const{
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

Constraint ValueCollection::getConstraintOfType(ConstraintType t) const{
  switch(t){
  case LowerBound:
    Assert(hasLowerBound());
    return d_lowerBound;
  case Equality:
    Assert(hasEquality());
    return d_equality;
  case UpperBound:
    Assert(hasUpperBound());
    return d_upperBound;
  case Disequality:
    Assert(hasDisequality());
    return d_disequality;
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
  return
    !(hasLowerBound() ||
      hasUpperBound() ||
      hasEquality() ||
      hasDisequality());
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

bool ConstraintValue::initialized() const {
  return d_database != NULL;
}

void ConstraintValue::initialize(ConstraintDatabase* db, SortedConstraintMapIterator v, Constraint negation){
  Assert(!initialized());
  d_database = db;
  d_variablePosition = v;
  d_negation = negation;
}

ConstraintValue::~ConstraintValue() {
  Assert(safeToGarbageCollect());

  if(initialized()){
    ValueCollection& vc =  d_variablePosition->second;
    Debug("arith::constraint") << "removing" << vc << endl; 

    vc.remove(getType());
  
    if(vc.empty()){
      Debug("arith::constraint") << "erasing" << vc << endl; 
      SortedConstraintMap& perVariable = d_database->getVariableSCM(getVariable());
      perVariable.erase(d_variablePosition);
    }

    if(hasLiteral()){
      d_database->d_nodetoConstraintMap.erase(getLiteral());
    }
  }
}

const ValueCollection& ConstraintValue::getValueCollection() const{
  return d_variablePosition->second;
}

Constraint ConstraintValue::getCeiling() {
  Debug("getCeiling") << "ConstraintValue::getCeiling on " << *this << endl;
  Assert(getValue().getInfinitesimalPart().sgn() > 0);

  DeltaRational ceiling(getValue().ceiling());

#warning "Optimize via the iterator"
  return d_database->getConstraint(getVariable(), getType(), ceiling);
}

Constraint ConstraintValue::getFloor() {
  Assert(getValue().getInfinitesimalPart().sgn() < 0);

  DeltaRational floor(Rational(getValue().floor()));

#warning "Optimize via the iterator"
  return d_database->getConstraint(getVariable(), getType(), floor);
}

void ConstraintValue::setCanBePropagated() {
  Assert(!canBePropagated());
  d_database->pushCanBePropagatedWatch(this);
}

void ConstraintValue::setAssertedToTheTheory() {
  Assert(hasLiteral());
  Assert(!assertedToTheTheory());
  Assert(!d_negation->assertedToTheTheory());
  d_database->pushAssertedToTheTheoryWatch(this);
}

bool ConstraintValue::isSelfExplaining() const {
  return d_proof == d_database->d_selfExplainingProof;
}

bool ConstraintValue::hasEqualityEngineProof() const {
  return d_proof == d_database->d_equalityEngineProof;
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

Constraint ConstraintValue::makeNegation(ArithVar v, ConstraintType t, const DeltaRational& r){
  switch(t){
  case LowerBound:
    {
      Assert(r.infinitesimalSgn() >= 0);
      if(r.infinitesimalSgn() > 0){
        Assert(r.getInfinitesimalPart() == 1);
        // make (not (v > r)), which is (v <= r)
        DeltaRational dropInf(r.getNoninfinitesimalPart(), 0);
        return new ConstraintValue(v, UpperBound, dropInf);
      }else{
        Assert(r.infinitesimalSgn() == 0);
        // make (not (v >= r)), which is (v < r)
        DeltaRational addInf(r.getNoninfinitesimalPart(), -1);
        return new ConstraintValue(v, UpperBound, addInf);
      }
    }
  case UpperBound:
    {
      Assert(r.infinitesimalSgn() <= 0);
      if(r.infinitesimalSgn() < 0){
        Assert(r.getInfinitesimalPart() == -1);
        // make (not (v < r)), which is (v >= r)
        DeltaRational dropInf(r.getNoninfinitesimalPart(), 0);
        return new ConstraintValue(v, LowerBound, dropInf);
      }else{
        Assert(r.infinitesimalSgn() == 0);
        // make (not (v <= r)), which is (v > r)
        DeltaRational addInf(r.getNoninfinitesimalPart(), 1);
        return new ConstraintValue(v, LowerBound, addInf);
      }
    }
  case Equality:
    return new ConstraintValue(v, Disequality, r);
  case Disequality:
    return new ConstraintValue(v, Equality, r);
  default:
    Unreachable();
    return NullConstraint;
  }
}

ConstraintDatabase::ConstraintDatabase(context::Context* satContext, context::Context* userContext, const ArithVarNodeMap& av2nodeMap,
                                       DifferenceManager& dm)
  : d_varDatabases(),
    d_toPropagate(satContext),
    d_proofs(satContext, false),
    d_watches(new Watches(satContext, userContext)),
    d_av2nodeMap(av2nodeMap),
    d_differenceManager(dm),
    d_satContext(satContext),
    d_satAllocationLevel(d_satContext->getLevel())
{
  d_selfExplainingProof = d_proofs.size();
  d_proofs.push_back(NullConstraint);

  d_equalityEngineProof = d_proofs.size();
  d_proofs.push_back(NullConstraint);
}

Constraint ConstraintDatabase::getConstraint(ArithVar v, ConstraintType t, const DeltaRational& r){
  //This must always return a constraint.

  SortedConstraintMap& scm = getVariableSCM(v);
  pair<SortedConstraintMapIterator, bool> insertAttempt;
  insertAttempt = scm.insert(make_pair(r, ValueCollection()));

  SortedConstraintMapIterator pos = insertAttempt.first;
  ValueCollection& vc = pos->second;
  if(vc.hasConstraintOfType(t)){
    return vc.getConstraintOfType(t);
  }else{
    Constraint c = new ConstraintValue(v, t, r);
    Constraint negC = ConstraintValue::makeNegation(v, t, r);

    SortedConstraintMapIterator negPos;
    if(t == Equality || t == Disequality){
      negPos = pos;
    }else{
      pair<SortedConstraintMapIterator, bool> negInsertAttempt;
      negInsertAttempt = scm.insert(make_pair(negC->getValue(), ValueCollection()));
      Assert(negInsertAttempt.second);
      negPos = negInsertAttempt.first;
    }

    c->initialize(this, pos, negC);
    negC->initialize(this, negPos, c);

    vc.add(c);
    negPos->second.add(negC);

    return c;
  }
}
bool ConstraintDatabase::emptyDatabase(const std::vector<PerVariableDatabase>& vec){
  std::vector<PerVariableDatabase>::const_iterator first = vec.begin();
  std::vector<PerVariableDatabase>::const_iterator last = vec.end();
  return std::find_if(first, last, PerVariableDatabase::IsEmpty) == last;
}

ConstraintDatabase::~ConstraintDatabase(){
  Assert(d_satAllocationLevel <= d_satContext->getLevel());

  delete d_watches;

  std::vector<Constraint> constraintList;

  while(!d_varDatabases.empty()){
    PerVariableDatabase* back = d_varDatabases.back();

    SortedConstraintMap& scm = back->d_constraints;
    SortedConstraintMapIterator i = scm.begin(), i_end = scm.end();
    for(; i != i_end; ++i){
      (i->second).push_into(constraintList);
    }
    while(!constraintList.empty()){
      Constraint c = constraintList.back();
      constraintList.pop_back();
      delete c;
    }
    Assert(scm.empty());
    d_varDatabases.pop_back();
    delete back;
  }

  Assert(d_nodetoConstraintMap.empty());
}

void ConstraintDatabase::addVariable(ArithVar v){
  Assert(v == d_varDatabases.size());
  d_varDatabases.push_back(new PerVariableDatabase(v));
}

bool ConstraintValue::safeToGarbageCollect() const{
  return !isSplit()
    && !canBePropagated()
    && !hasProof()
    && !assertedToTheTheory();
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


  eq->d_database->pushSplitWatch(eq);
  diseq->d_database->pushSplitWatch(diseq);

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
  Debug("arith::constraint") << "allocateConstraintForLiteral(" << v << ", "<< literal <<")" << endl;
  Kind kind = simplifiedKind(literal);
  ConstraintType type = constraintTypeOfLiteral(kind);
  DeltaRational dr = determineRightConstant(literal, kind);
  return new ConstraintValue(v, type, dr);
}

Constraint ConstraintDatabase::addAtom(TNode atom){
  Assert(!hasLiteral(atom));

  Debug("arith::constraint") << "addAtom(" << atom << ")" << endl;
  ArithVar v = d_av2nodeMap.asArithVar(atom[0]);

  Node negation = atom.notNode();

  Constraint posC = allocateConstraintForLiteral(v, atom);

  SortedConstraintMap& scm = getVariableSCM(posC->getVariable());
  pair<SortedConstraintMapIterator, bool> insertAttempt;
  insertAttempt = scm.insert(make_pair(posC->getValue(), ValueCollection()));

  SortedConstraintMapIterator posI = insertAttempt.first;
  // If the attempt succeeds, i points to a new empty ValueCollection
  // If the attempt fails, i points to a pre-existing ValueCollection

  if(posI->second.hasConstraintOfType(posC->getType())){
    //This is the situation where the Constraint exists, but
    //the literal has not been  associated with it.
    Constraint hit = posI->second.getConstraintOfType(posC->getType());
    Debug("arith::constraint") << "hit " << hit << endl;
    Debug("arith::constraint") << "posC " << posC << endl;

    delete posC;

    hit->setLiteral(atom);
    hit->d_negation->setLiteral(negation);
    return hit;
  }else{

    Constraint negC = allocateConstraintForLiteral(v, negation);

    SortedConstraintMapIterator negI;

    if(posC->isEquality()){
      negI = posI;
    }else{
      Assert(posC->isLowerBound() || posC->isUpperBound());

      pair<SortedConstraintMapIterator, bool> negInsertAttempt;
      negInsertAttempt = scm.insert(make_pair(negC->getValue(), ValueCollection()));

      //This should always succeed as the DeltaRational for the negation is unique!
      Assert(negInsertAttempt.second);

      negI = negInsertAttempt.first;
    }

    (posI->second).add(posC);
    (negI->second).add(negC);

    posC->initialize(this, posI, negC);
    negC->initialize(this, negI, posC);

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

void ConstraintValue::selfExplaining(){
  markAsTrue();
}

void ConstraintValue::propagate(){
  Assert(hasProof());
  Assert(canBePropagated());
  Assert(!assertedToTheTheory());
  Assert(!isSelfExplaining());

  d_database->d_toPropagate.push(this);
}

void ConstraintValue::propagate(Constraint a){
  markAsTrue(a);
  propagate();
}

void ConstraintValue::propagate(Constraint a, Constraint b){
  markAsTrue(a);
  propagate();
}

void ConstraintValue::propagate(const std::vector<Constraint>& b){
  markAsTrue(b);
  propagate();
}


void ConstraintValue::setEqualityEngineProof(){
  Assert(truthIsUnknown());
  Assert(hasLiteral());
  d_database->pushProofWatch(this, d_database->d_equalityEngineProof);
}

void ConstraintValue::markAsTrue(){
  Assert(truthIsUnknown());
  Assert(hasLiteral());
  Assert(assertedToTheTheory());
  d_database->pushProofWatch(this, d_database->d_selfExplainingProof);
}

void ConstraintValue::markAsTrue(Constraint imp){
  Assert(truthIsUnknown());
  Assert(imp->hasProof());

  d_database->d_proofs.push_back(NullConstraint);
  d_database->d_proofs.push_back(imp);
  ProofId proof = d_database->d_proofs.size() - 1;
  d_database->pushProofWatch(this, proof);
}

void ConstraintValue::markAsTrue(Constraint impA, Constraint impB){
  Assert(truthIsUnknown());
  Assert(impA->hasProof());
  Assert(impB->hasProof());

  d_database->d_proofs.push_back(NullConstraint);
  d_database->d_proofs.push_back(impA);
  d_database->d_proofs.push_back(impB);
  ProofId proof = d_database->d_proofs.size() - 1;

  d_database->pushProofWatch(this, proof);
}

void ConstraintValue::markAsTrue(const vector<Constraint>& a){
  Assert(truthIsUnknown());
  Assert(a.size() >= 1);
  d_database->d_proofs.push_back(NullConstraint);
  for(vector<Constraint>::const_iterator i = a.begin(), end = a.end(); i != end; ++i){
    Constraint c_i = *i;
    Assert(c_i->hasProof());
    d_database->d_proofs.push_back(c_i);
  }

  ProofId proof = d_database->d_proofs.size() - 1;

  d_database->pushProofWatch(this, proof);
}

SortedConstraintMap& ConstraintValue::constraintSet() const{
  Assert(d_database->variableDatabaseIsSetup(d_variable));
  return (d_database->d_varDatabases[d_variable])->d_constraints;
}

void ConstraintValue::internalPropagate(Constraint antecedent){
  Assert(!negationHasProof());

  if(hasProof()){
    Debug("arith::db") << "Already has proof " << this << endl;
  }else{
    markAsTrue(antecedent);
  }
}

bool ConstraintValue::proofIsEmpty() const{
  Assert(hasProof());
  bool result = d_database->d_proofs[d_proof] == NullConstraint;
  Assert((!result) || isSelfExplaining() || hasEqualityEngineProof());
  return result;
}

Node ConstraintValue::explainForConflict() const{
  Assert(hasProof());
  Assert(!isSelfExplaining() || assertedToTheTheory());

  if(assertedToTheTheory()){
    return getLiteral();
  }else if(hasEqualityEngineProof()){
    return d_database->eeExplain(this);
  }else{
    Assert(!isSelfExplaining());
    Assert(!proofIsEmpty());
    if(d_database->d_proofs[d_proof-1] == NullConstraint){
      Constraint antecedent = d_database->d_proofs[d_proof];
      return antecedent->explainForConflict();
    }else{
      NodeBuilder<> nb(AND);
      explainInto(nb);
      return nb;
    }
  }
}

void ConstraintValue::explainInto(NodeBuilder<>& nb) const{
  Assert(hasProof());
  Assert(!isSelfExplaining() || assertedToTheTheory());

  if(assertedToTheTheory()){
    nb << getLiteral();
  }else if(hasEqualityEngineProof()){
    d_database->eeExplain(this, nb);
  }else{
    Assert(!isSelfExplaining());
    ProofId p = d_proof;
    Constraint antecedent = d_database->d_proofs[p];

    for(; antecedent != NullConstraint; antecedent = d_database->d_proofs[--p] ){
      antecedent->explainInto(nb);
    }
  }
}

Node ConstraintValue::explainForPropagation() const{
  Assert(hasProof());
  Assert(!isSelfExplaining());

  if(hasEqualityEngineProof()){
    return d_database->eeExplain(this);
  }else{
    Assert(!proofIsEmpty());
    //Force the selection of the layer above if the node is assertedToTheTheory()!
    if(d_database->d_proofs[d_proof-1] == NullConstraint){
      Constraint antecedent = d_database->d_proofs[d_proof];
      return antecedent->explainForConflict();
    }else{
      NodeBuilder<> nb(kind::AND);
      Assert(!isSelfExplaining());

      ProofId p = d_proof;
      Constraint antecedent = d_database->d_proofs[p];
      for(; antecedent != NullConstraint; antecedent = d_database->d_proofs[--p] ){
        antecedent->explainInto(nb);
      }
      return nb;
    }
  }
}

Node ConstraintValue::explainConjunction(Constraint a, Constraint b){
  NodeBuilder<> nb(kind::AND);
  a->explainInto(nb);
  b->explainInto(nb);
  return nb;
}

Node ConstraintValue::explainConjunction(Constraint a, Constraint b, Constraint c){
  NodeBuilder<> nb(kind::AND);
  a->explainInto(nb);
  b->explainInto(nb);
  c->explainInto(nb);
  return nb;
}

Constraint ConstraintValue::getStrictlyWeakerLowerBound(bool asserted) const {
  Assert(initialized());

  SortedConstraintMapConstIterator i = d_variablePosition;
  const SortedConstraintMap& scm = constraintSet();
  SortedConstraintMapConstIterator i_begin = scm.begin();
  while(i != i_begin){
    --i;
    const ValueCollection& vc = i->second;
    if(vc.hasLowerBound()){
      Constraint weaker = vc.getLowerBound();
      if(!asserted || weaker->assertedToTheTheory()){
        return weaker;
      }
    }
  }
  return NullConstraint;
}

Constraint ConstraintValue::getStrictlyWeakerUpperBound(bool asserted) const {
  SortedConstraintMapConstIterator i = d_variablePosition;
  const SortedConstraintMap& scm = constraintSet();
  SortedConstraintMapConstIterator i_end = scm.end();

  ++i;
  for(; i != i_end; ++i){
    const ValueCollection& vc = i->second;
    if(vc.hasUpperBound()){
      Constraint weaker = vc.getUpperBound();
      if(!asserted || weaker->assertedToTheTheory()){
        return weaker;
      }
    }
  }

  return NullConstraint;
}

Node ConstraintDatabase::eeExplain(const ConstraintValue* const c) const{
  Assert(c->hasLiteral());
  return d_differenceManager.explain(c->getLiteral());
}

void ConstraintDatabase::eeExplain(const ConstraintValue* const c, NodeBuilder<>& nb) const{
  Assert(c->hasLiteral());
  d_differenceManager.explain(c->getLiteral(), nb);
}

bool ConstraintDatabase::variableDatabaseIsSetup(ArithVar v) const {
  return v < d_varDatabases.size();
}


ConstraintDatabase::Watches::Watches(context::Context* satContext, context::Context* userContext):
  d_proofWatches(satContext),
  d_canBePropagatedWatches(satContext),
  d_assertedToTheTheoryWatches(satContext),
  d_splitWatches(userContext)
{}


void ConstraintValue::setLiteral(Node n) {
  Assert(!hasLiteral());
  Assert(sanityChecking(n));
  d_literal = n;
  NodetoConstraintMap& map = d_database->d_nodetoConstraintMap;
  Assert(map.find(n) == map.end());
  map.insert(make_pair(d_literal, this));
}


}/* arith namespace */
}/* theory namespace */
}/* CVC4 namespace */

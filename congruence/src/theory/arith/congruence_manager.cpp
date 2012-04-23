#include "theory/arith/congruence_manager.h"
#include "theory/uf/equality_engine_impl.h"

#include "theory/arith/constraint.h"
#include "theory/arith/arith_utilities.h"

namespace CVC4 {
namespace theory {
namespace arith {

  ArithCongruenceManager::ArithCongruenceManager(context::Context* c, ConstraintDatabase& cd, TNodeCallBack& setup, const ArithVarNodeMap& av2Node)
  : d_conflict(c),
    d_notify(*this),
    d_keepAlive(c),
    d_propagatations(c),
    d_explanationMap(c),
    d_constraintDatabase(cd),
    d_setupLiteral(setup),
    d_av2Node(av2Node),
    d_ee(d_notify, c, "theory::arith::ArithCongruenceManager"),
    d_false(mkBoolNode(false))
{}

void ArithCongruenceManager::watchedVariableIsZero(Constraint lb, Constraint ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());
  Assert(lb->getValue().sgn() == 0);
  Assert(ub->getValue().sgn() == 0);

  ArithVar s = lb->getVariable();
  Node reason = ConstraintValue::explainConflict(lb,ub);

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(true, s, reason);
}

void ArithCongruenceManager::watchedVariableIsZero(Constraint eq){
  Assert(eq->isEquality());
  Assert(eq->getValue().sgn() == 0);

  ArithVar s = eq->getVariable();

  //Explain for conflict is correct as these proofs are generated
  //and stored eagerly
  //These will be safe for propagation later as well
  Node reason = eq->explainForConflict();

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(true, s, reason);
}

void ArithCongruenceManager::watchedVariableCannotBeZero(Constraint c){
  ArithVar s = c->getVariable();

  //Explain for conflict is correct as these proofs are generated and stored eagerly
  //These will be safe for propagation later as well
  Node reason = c->explainForConflict();
  
  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(false, s, reason);
}


bool ArithCongruenceManager::propagate(TNode x){
  Debug("arith::differenceManager")<< "ArithCongruenceManager::propagate("<<x<<")"<<std::endl;
  if(inConflict()){
    return true;
  }

  Node rewritten = Rewriter::rewrite(x);

  //Need to still propagate this!
  if(rewritten.getKind() == kind::CONST_BOOLEAN){
    pushBack(x);

    if(rewritten.getConst<bool>()){
      return true;
    }else{
      Node conf = explainInternal(x);
      d_conflict.set(conf);
      std::cout << "rewritten to false " << conf << std::endl;
      return false;
    }
  }

  Assert(rewritten.getKind() != kind::CONST_BOOLEAN);

  Constraint c = d_constraintDatabase.lookup(rewritten);
  if(c == NullConstraint){
    //using setup as there may not be a corresponding difference literal yet
    d_setupLiteral(rewritten);
    c = d_constraintDatabase.lookup(rewritten);
    Assert(c != NullConstraint);
    //c = d_constraintDatabase.addLiteral(rewritten);
  }

  Debug("arith::differenceManager")<< "x is "
                                   <<  c->hasProof() << " "
                                   << (x == rewritten) << " "
                                   << c->canBePropagated() << " "
                                   << c->negationHasProof() << std::endl;

  if(c->negationHasProof()){
    Node expC = explainInternal(x);
    Node neg = c->getNegation()->explainForConflict();
    Node conf = expC.andNode(neg);
    Node final = flattenAnd(conf);

    d_conflict.set(final);
    Debug("arith::differenceManager") << "differenceManager found a conflict " << final << std::endl;
    return false;
  }

  // Cases for propagation
  // C : c has a proof
  // S : x == rewritten
  // P : c can be propagated
  //
  // CSP
  // 000 : propagate x, and mark C it as being explained
  // 001 : propagate x, and propagate c after marking it as being explained
  // 01* : propagate x, mark c but do not propagate c
  // 10* : propagate x, do not mark c and do not propagate c
  // 11* : drop the constraint, do not propagate x or c

  if(!c->hasProof() && x != rewritten){
    pushBack(x, rewritten);

    c->setEqualityEngineProof();
    if(c->canBePropagated() && !c->assertedToTheTheory()){
      c->propagate();
    }
  }else if(!c->hasProof() && x == rewritten){
    pushBack(x, rewritten);
    c->setEqualityEngineProof();
  }else if(c->hasProof() && x != rewritten){
    pushBack(x, rewritten);
  }else{
    Assert(c->hasProof() && x == rewritten);
  }
  return true;
}

void ArithCongruenceManager::explain(TNode literal, std::vector<TNode>& assumptions) {
  TNode lhs, rhs;
  switch (literal.getKind()) {
    case kind::EQUAL:
      lhs = literal[0];
      rhs = literal[1];
      break;
    case kind::NOT:
      lhs = literal[0];
      rhs = d_false;
      break;
    default:
      Unreachable();
  }
  d_ee.explainEquality(lhs, rhs, assumptions);
}

void ArithCongruenceManager::enqueueIntoNB(const std::set<TNode> s, NodeBuilder<>& nb){
  std::set<TNode>::const_iterator it = s.begin();
  std::set<TNode>::const_iterator it_end = s.end();
  for(; it != it_end; ++it) {
    nb << *it;
  }
}

Node ArithCongruenceManager::explainInternal(TNode internal){
  std::vector<TNode> assumptions;
  explain(internal, assumptions);

  std::set<TNode> assumptionSet;
  assumptionSet.insert(assumptions.begin(), assumptions.end());

  if (assumptionSet.size() == 1) {
    // All the same, or just one
    return assumptions[0];
  }else{
    NodeBuilder<> conjunction(kind::AND);
    enqueueIntoNB(assumptionSet, conjunction);
    return conjunction;
  }
}
Node ArithCongruenceManager::explain(TNode external){
  Node internal = externalToInternal(external);
  return explainInternal(internal);
}

void ArithCongruenceManager::explain(TNode external, NodeBuilder<>& out){
  Node internal = externalToInternal(external);

  std::vector<TNode> assumptions;
  explain(internal, assumptions);
  std::set<TNode> assumptionSet;
  assumptionSet.insert(assumptions.begin(), assumptions.end());

  enqueueIntoNB(assumptionSet, out);
}

void ArithCongruenceManager::addWatchedPair(ArithVar s, TNode x, TNode y){
  Assert(!isWatchedVariable(s));

  Debug("arith::differenceManager")
    << "addWatchedPair(" << s << ", " << x << ", " << y << ")" << std::endl;
  
  d_watchedVariables.add(s);

  Node eq = x.eqNode(y);
  d_watchedEqualities[s] = eq;
}

// void ArithCongruenceManager::addAssertionToEqualityEngine(bool eq, TNode x, TNode y, TNode reason){  
//   if(eq){
//     d_ee.addEquality(x, y, reason);
//   }else{
//     d_ee.addDisequality(x, y, reason);
//   }
// }

void ArithCongruenceManager::assertionToEqualityEngine(bool isEquality, ArithVar s, TNode reason){
  Assert(isWatchedVariable(s));

  TNode eq = d_watchedEqualities[s];
  Assert(eq.getKind() == kind::EQUAL);

  TNode x = eq[0];
  TNode y = eq[1];

  if(isEquality){
     d_ee.addEquality(x, y, reason);
   }else{
     d_ee.addDisequality(x, y, reason);
   }
}

void ArithCongruenceManager::equalsConstant(Constraint c){
  Assert(c->isEquality());

  std::cout << "equals constant " << c << std::endl;

  ArithVar x = c->getVariable();
  Node xAsNode = d_av2Node.asNode(x);
  Node asRational = mkRationalNode(c->getValue().getNoninfinitesimalPart());

  //No guarentee this is in normal form!
  Node eq = xAsNode.eqNode(asRational);
  d_keepAlive.push_back(eq);

  Node reason = c->explainForConflict();
  d_keepAlive.push_back(reason);
  
  d_ee.addEquality(xAsNode, asRational, reason);
}

void ArithCongruenceManager::equalsConstant(Constraint lb, Constraint ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());

  std::cout << "equals constant " << lb << std::endl
            << ub << std::endl;

  ArithVar x = lb->getVariable();
  Node reason = ConstraintValue::explainConflict(lb,ub);

  Node xAsNode = d_av2Node.asNode(x);
  Node asRational = mkRationalNode(lb->getValue().getNoninfinitesimalPart());

  //No guarentee this is in normal form!
  Node eq = xAsNode.eqNode(asRational);
  d_keepAlive.push_back(eq);
  d_keepAlive.push_back(reason);

  
  d_ee.addEquality(xAsNode, asRational, reason);
}

// void ArithCongruenceManager::addAssertionToEqualityEngine(bool eq, ArithVar s, TNode reason){
//   Assert(isDifferenceSlack(s));

//   TNode x = d_differences[s].x;
//   TNode y = d_differences[s].y;

//   if(eq){
//     d_ee.addEquality(x, y, reason);
//   }else{
//     d_ee.addDisequality(x, y, reason);
//   }
// }

// void ArithCongruenceManager::dequeueLiterals(){
//   Assert(d_hasSharedTerms);
//   while(!d_literalsQueue.empty() && !inConflict()){
//     const LiteralsQueueElem& front = d_literalsQueue.front();
//     d_literalsQueue.dequeue();

//     addAssertionToEqualityEngine(front.d_eq, front.d_var, front.d_reason);
//   }
// }

// void ArithCongruenceManager::enableSharedTerms(){
//   Assert(!d_hasSharedTerms);
//   d_hasSharedTerms = true;
//   dequeueLiterals();
// }

// void ArithCongruenceManager::assertLiteral(bool eq, ArithVar s, TNode reason){
//   d_literalsQueue.enqueue(LiteralsQueueElem(eq, s, reason));
//   if(d_hasSharedTerms){
//     dequeueLiterals();
//   }
// }

void ArithCongruenceManager::addSharedTerm(Node x){
  // if(!d_hasSharedTerms){
  //   enableSharedTerms();
  // }
  d_ee.addTriggerTerm(x);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

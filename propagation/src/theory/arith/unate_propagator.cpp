/*********************                                                        */
/*! \file unate_propagator.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
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

#include "theory/arith/unate_propagator.h"
#include "theory/arith/arith_utilities.h"
#include "theory/output_channel.h"

#include <list>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

using namespace CVC4::kind;

using namespace std;



ArithUnatePropagator::ArithUnatePropagator(context::Context* cxt, OutputChannel* out) :
  d_arithOut(out), d_orderedListMap()
{
  d_voc = new VectorOutputChannel();
}

ArithUnatePropagator::~ArithUnatePropagator(){
  delete d_voc;
}


bool ArithUnatePropagator::leftIsSetup(TNode left){
  return d_orderedListMap.find(left) != d_orderedListMap.end();
}

ArithUnatePropagator::OrderedSetTriple& ArithUnatePropagator::getOrderedSetTriple(TNode left){
  Assert(leftIsSetup(left));
  return d_orderedListMap[left];
}

void ArithUnatePropagator::removeAtom(Node atom){
  TNode left = atom[0];
  Assert(leftIsSetup(left));
  switch(atom.getKind()){
  case LEQ:{
    OrderedSet& leqSet = getLeqSet(left);
    Assert(leqSet.find(atom) != leqSet.end());
    leqSet.erase(atom);
    break;
  }
  case GEQ:{
    OrderedSet& geqSet = getGeqSet(left);
    Assert(geqSet.find(atom) != geqSet.end());
    geqSet.erase(atom);
    break;
  }
  default:
    Unhandled(atom.getKind());
  }
}

Node ArithUnatePropagator::impliedBound(TNode bound){

  TNode left = bound[0];
  if(!leftIsSetup(left)){
    return Node::null();
  }


  OrderedSet& geqSet = getGeqSet(left);
  OrderedSet& leqSet = getLeqSet(left);

  Node simp;
  Node neg;
  switch(bound.getKind()){
  case LT:
    neg = NodeBuilder<2>(GEQ) << bound[0] << bound[1];
    simp = NodeBuilder<1>(NOT) << neg;
    break;
  case GT:
    neg = NodeBuilder<2>(LEQ) << bound[0] << bound[1];
    simp = NodeBuilder<1>(NOT) << neg;
    break;
  case LEQ:
    simp = bound;
    neg = NodeBuilder<1>(NOT) << simp;
    break;
  case GEQ:
    simp = bound;
    neg = NodeBuilder<1>(NOT) << simp;
    break;
  default:
    Unhandled(bound.getKind());
  }
  switch(bound.getKind()){
  case LT:
    if(geqSet.find(neg) != geqSet.end()){
      return simp;
    }
    break;
  case GT:
    if(leqSet.find(neg) != leqSet.end()){
      return simp;
    }
    break;
  case LEQ:
    if(leqSet.find(simp) != leqSet.end()){
      return simp;
    }
    break;
  case GEQ:
    if(geqSet.find(simp) != geqSet.end()){
      return simp;
    }
    break;
  default:
    Unhandled(bound.getKind());
  }

  OutputChannel* savedChannel = d_arithOut;
  d_arithOut = d_voc;

  switch(bound.getKind()){
  case LT:
  case GT:
    addAtom(neg);
    removeAtom(neg);
    break;
  case LEQ:
  case GEQ:
    addAtom(simp);
    removeAtom(simp);
    break;
  default:
    Unhandled(bound.getKind());
  }

  const vector<Node>& output = d_voc->getVector();
  d_arithOut = savedChannel;

  bool min  = bound.getKind() == LEQ || bound.getKind() == LT;

  Node winner = Node::null();

  for(vector<Node>::const_iterator i = output.begin(), end = output.end();
      i != end; ++i){
    Node orNode = *i;
    Assert(orNode.getKind() == OR);
    Assert(orNode.getNumChildren() == 2);
    Node implied = Node::null();
    if(orNode[0] == neg){
      implied = orNode[1];
    }else if(orNode[1] == neg){
      implied = orNode[0];
    }
    if(!implied.isNull()){
      if(winner.isNull()){
        winner = implied;
      }else{
        Debug("propagation") << bound << winner << implied << endl;
        TNode inter1 = winner.getKind() == kind::NOT ? winner[0] : winner;
        TNode inter2 = implied.getKind() == kind::NOT ? implied[0] : implied;
        TNode rh1 = inter1[1];
        TNode rh2 = inter2[1];
        const Rational& c1 = rh1.getConst<Rational>();
        const Rational& c2 = rh2.getConst<Rational>();
        int cmpRes = c1.cmp(c2);

        if(cmpRes == 0){
          Assert(winner.getKind() == NOT || implied.getKind() == NOT);
          if(implied.getKind() == NOT){
            winner = implied;
          }
        }else if(cmpRes > 0 && min){
          winner = implied;
        }else if(cmpRes < 0 && !min){
          winner = implied;
        }
      }
      Debug("propagation") << bound << winner << endl;
    }
  }
  d_voc->clear();
  return winner;
}

OrderedSet& ArithUnatePropagator::getEqSet(TNode left){
  Assert(leftIsSetup(left));
  return getOrderedSetTriple(left).d_eqSet;
}
OrderedSet& ArithUnatePropagator::getLeqSet(TNode left){
  Assert(leftIsSetup(left));
  return getOrderedSetTriple(left).d_leqSet;
}
OrderedSet& ArithUnatePropagator::getGeqSet(TNode left){
  Assert(leftIsSetup(left));
  return getOrderedSetTriple(left).d_geqSet;
}

bool ArithUnatePropagator::hasAnyAtoms(TNode v){
  Assert(!leftIsSetup(v)
         || !(getEqSet(v)).empty()
         || !(getLeqSet(v)).empty()
         || !(getGeqSet(v)).empty());

  return leftIsSetup(v);
}

void ArithUnatePropagator::setupLefthand(TNode left){
  Assert(!leftIsSetup(left));

  d_orderedListMap[left] = OrderedSetTriple();
}

void ArithUnatePropagator::addAtom(TNode atom){
  TNode left  = atom[0];
  TNode right = atom[1];

  if(!leftIsSetup(left)){
    setupLefthand(left);
  }

  OrderedSet& eqSet = getEqSet(left);
  OrderedSet& leqSet = getLeqSet(left);
  OrderedSet& geqSet = getGeqSet(left);

  switch(atom.getKind()){
  case EQUAL:
    {
      pair<OrderedSet::iterator, bool> res = eqSet.insert(atom);
      Assert(res.second);
      addImplicationsUsingEqualityAndEqualityList(atom, eqSet);
      addImplicationsUsingEqualityAndLeqList(atom, leqSet);
      addImplicationsUsingEqualityAndGeqList(atom, geqSet);
      break;
    }
  case LEQ:
    {
      pair<OrderedSet::iterator, bool> res = leqSet.insert(atom);
      Assert(res.second);

      addImplicationsUsingLeqAndEqualityList(atom, eqSet);
      addImplicationsUsingLeqAndLeqList(atom, leqSet);
      addImplicationsUsingLeqAndGeqList(atom, geqSet);
      break;
    }
  case GEQ:
    {
      pair<OrderedSet::iterator, bool> res = geqSet.insert(atom);
      Assert(res.second);

      addImplicationsUsingGeqAndEqualityList(atom, eqSet);
      addImplicationsUsingGeqAndLeqList(atom, leqSet);
      addImplicationsUsingGeqAndGeqList(atom, geqSet);

      break;
    }
  default:
    Unreachable();
  }
}

bool rightHandRationalIsEqual(TNode a, TNode b){
  TNode secondA = a[1];
  TNode secondB = b[1];

  const Rational& qA = secondA.getConst<Rational>();
  const Rational& qB = secondB.getConst<Rational>();

  return qA == qB;
}


bool rightHandRationalIsLT(TNode a, TNode b){
  //This version is sticking around because it is easier to read!
  return RightHandRationalLT()(a,b);
}

//void addImplicationsUsingEqualityAndEqualityList(TNode eq, OrderedSet* eqSet);

void ArithUnatePropagator::addImplicationsUsingEqualityAndEqualityList(TNode atom, OrderedSet& eqSet){
  Assert(atom.getKind() == EQUAL);
  OrderedSet::iterator eqPos = eqSet.find(atom);
  Assert(eqPos != eqSet.end());
  Assert(*eqPos == atom);

  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);
  for(OrderedSet::iterator eqIter = eqSet.begin();
      eqIter != eqSet.end(); ++eqIter){
    if(eqIter == eqPos) continue;
    TNode eq = *eqIter;
    Assert(!rightHandRationalIsEqual(eq, atom));
    addImplication(eq, negation);
  }
}

void ArithUnatePropagator::addImplicationsUsingEqualityAndLeqList(TNode atom, OrderedSet& leqSet){

  Assert(atom.getKind() == EQUAL);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  OrderedSet::iterator leqIter = leqSet.lower_bound(atom);
  if(leqIter != leqSet.end()){
    TNode lowerBound = *leqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      addImplication(atom, lowerBound);  // x=b /\ b = b' => x <= b'
      if(leqIter != leqSet.begin()){
        --leqIter;
        Assert(rightHandRationalIsLT(*leqIter, atom));
        addImplication(*leqIter, negation); // x=b /\ b > b' => x > b'
      }
    }else{
      //probably wrong
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(atom, lowerBound);// x=b /\ b < b' => x <= b'

      if(leqIter != leqSet.begin()){
        --leqIter;
        Assert(rightHandRationalIsLT(*leqIter, atom));
        addImplication(*leqIter, negation);// x=b /\ b > b' => x > b'
      }
    }
  }else if(leqIter != leqSet.begin()){
    --leqIter;
    TNode strictlyLessThan = *leqIter;
    Assert(rightHandRationalIsLT(strictlyLessThan, atom));
    addImplication(*leqIter, negation); // x=b /\ b < b' => x <= b'
  }else{
    Assert(leqSet.empty());
  }
}

void ArithUnatePropagator::addImplicationsUsingEqualityAndGeqList(TNode atom, OrderedSet& geqSet){

  Assert(atom.getKind() == EQUAL);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  OrderedSet::iterator geqIter = geqSet.lower_bound(atom);
  if(geqIter != geqSet.end()){
    TNode lowerBound = *geqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      addImplication(atom, lowerBound);  // x=b /\ b = b' => x >= b'
      ++geqIter;
      if(geqIter != geqSet.end()){ // x=b /\ b < b' => x < b'
        TNode strictlyGt = *geqIter;
        Assert(rightHandRationalIsLT( atom, strictlyGt ));
        addImplication(strictlyGt, negation);
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(lowerBound, negation);// x=b /\ b < b' => x < b'
      if(geqIter != geqSet.begin()){
        --geqIter;
        TNode strictlyLessThan = *geqIter;
        Assert(rightHandRationalIsLT(strictlyLessThan, atom));
        addImplication(atom, strictlyLessThan);// x=b /\ b > b' => x >= b'
      }
    }
  }else if(geqIter != geqSet.begin()){
    --geqIter;
    TNode strictlyLT = *geqIter;
    Assert(rightHandRationalIsLT(strictlyLT, atom));
    addImplication(atom, strictlyLT);// x=b /\ b > b' => x >= b'
  }else{
    Assert(geqSet.empty());
  }
}

void ArithUnatePropagator::addImplicationsUsingLeqAndLeqList(TNode atom, OrderedSet& leqSet)
{
  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  OrderedSet::iterator atomPos = leqSet.find(atom);
  Assert(atomPos != leqSet.end());
  Assert(*atomPos == atom);

  if(atomPos != leqSet.begin()){
    --atomPos;
    TNode beforeLeq = *atomPos;
    Assert(rightHandRationalIsLT(beforeLeq, atom));
    addImplication(beforeLeq, atom);// x<=b' /\ b' < b => x <= b
    ++atomPos;
  }
  ++atomPos;
  if(atomPos != leqSet.end()){
    TNode afterLeq = *atomPos;
    Assert(rightHandRationalIsLT(atom, afterLeq));
    addImplication(atom, afterLeq);// x<=b /\ b < b' => x <= b'
  }
}
void ArithUnatePropagator::addImplicationsUsingLeqAndGeqList(TNode atom, OrderedSet& geqSet) {

  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  OrderedSet::iterator geqIter = geqSet.lower_bound(atom);
  if(geqIter != geqSet.end()){
    TNode lowerBound = *geqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      Assert(rightHandRationalIsEqual(atom, lowerBound));
      addImplication(negation, lowerBound);// (x > b) => (x >= b)
      ++geqIter;
      if(geqIter != geqSet.end()){
        TNode next = *geqIter;
        Assert(rightHandRationalIsLT(atom, next));
        addImplication(next, negation);// x>=b' /\ b' > b => x > b
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(lowerBound, negation);// x>=b' /\ b' > b => x > b
      if(geqIter != geqSet.begin()){
        --geqIter;
        TNode prev = *geqIter;
        Assert(rightHandRationalIsLT(prev, atom));
        addImplication(negation, prev);// (x>b /\ b > b') => x >= b'
      }
    }
  }else if(geqIter != geqSet.begin()){
    --geqIter;
    TNode strictlyLT = *geqIter;
    Assert(rightHandRationalIsLT(strictlyLT, atom));
    addImplication(negation, strictlyLT);// (x>b /\ b > b') => x >= b'
  }else{
    Assert(geqSet.empty());
  }
}

void ArithUnatePropagator::addImplicationsUsingLeqAndEqualityList(TNode atom, OrderedSet& eqSet) {
  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  //TODO Improve this later
  for(OrderedSet::iterator eqIter = eqSet.begin(); eqIter != eqSet.end(); ++eqIter){
    TNode eq = *eqIter;
    if(rightHandRationalIsEqual(atom, eq)){
      // (x = b' /\ b = b') =>  x <= b
      addImplication(eq, atom);
    }else if(rightHandRationalIsLT(atom, eq)){
      // (x = b' /\ b' > b) =>  x > b
      addImplication(eq, negation);
    }else{
      // (x = b' /\ b' < b) =>  x <= b
      addImplication(eq, atom);
    }
  }
}


void ArithUnatePropagator::addImplicationsUsingGeqAndGeqList(TNode atom, OrderedSet& geqSet){
  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  OrderedSet::iterator atomPos = geqSet.find(atom);
  Assert(atomPos != geqSet.end());
  Assert(*atomPos == atom);

  if(atomPos != geqSet.begin()){
    --atomPos;
    TNode beforeGeq = *atomPos;
    Assert(rightHandRationalIsLT(beforeGeq, atom));
    addImplication(atom, beforeGeq);// x>=b /\ b > b' => x >= b'
    ++atomPos;
  }
  ++atomPos;
  if(atomPos != geqSet.end()){
    TNode afterGeq = *atomPos;
    Assert(rightHandRationalIsLT(atom, afterGeq));
    addImplication(afterGeq, atom);// x>=b' /\ b' > b => x >= b
  }
}

void ArithUnatePropagator::addImplicationsUsingGeqAndLeqList(TNode atom, OrderedSet& leqSet){

  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  OrderedSet::iterator leqIter = leqSet.lower_bound(atom);
  if(leqIter != leqSet.end()){
    TNode lowerBound = *leqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      Assert(rightHandRationalIsEqual(atom, lowerBound));
      addImplication(negation, lowerBound);// (x < b) => (x <= b)

      if(leqIter != leqSet.begin()){
        --leqIter;
        TNode prev = *leqIter;
        Assert(rightHandRationalIsLT(prev, atom));
        addImplication(prev, negation);// x<=b' /\ b' < b => x < b
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(negation, lowerBound);// (x < b /\ b < b') => x <= b'
      ++leqIter;
      if(leqIter != leqSet.end()){
        TNode next = *leqIter;
        Assert(rightHandRationalIsLT(atom, next));
        addImplication(negation, next);// (x < b /\ b < b') => x <= b'
      }
    }
  }else if(leqIter != leqSet.begin()){
    --leqIter;
    TNode strictlyLT = *leqIter;
    Assert(rightHandRationalIsLT(strictlyLT, atom));
    addImplication(strictlyLT, negation);// (x <= b' /\ b' < b) => x < b
  }else{
    Assert(leqSet.empty());
  }
}
void ArithUnatePropagator::addImplicationsUsingGeqAndEqualityList(TNode atom, OrderedSet& eqSet){

  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  //TODO Improve this later
  for(OrderedSet::iterator eqIter = eqSet.begin(); eqIter != eqSet.end(); ++eqIter){
    TNode eq = *eqIter;
    if(rightHandRationalIsEqual(atom, eq)){
      // (x = b' /\ b = b') =>  x >= b
      addImplication(eq, atom);
    }else if(rightHandRationalIsLT(eq, atom)){
      // (x = b' /\ b' < b) =>  x < b
      addImplication(eq, negation);
    }else{
      // (x = b' /\ b' > b) =>  x >= b
      addImplication(eq, atom);
    }
  }
}

Node simplifiedImplication(TNode a, TNode b){
  Node negA;
  if(a.getKind() == NOT){
    negA = a[0];
  }else{
    negA = NodeBuilder<1>(NOT)<<a;
  }
  Node simpImp = NodeBuilder<2>(OR) << negA << b;
  return simpImp;
}

void ArithUnatePropagator::addImplication(TNode a, TNode b){
  Node imp = simplifiedImplication(a,b);

  Debug("arith-propagate") << "ArithUnatePropagator::addImplication";
  Debug("arith-propagate") << "(" << a << ", " << b <<")" << endl;

  d_arithOut->lemma(imp);
}

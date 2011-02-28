/*********************                                                        */
/*! \file theory_arrays.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of arrays.
 **
 ** Implementation of the theory of arrays.
 **/


#include "theory/arrays/theory_arrays.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include <map>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arrays;


TheoryArrays::TheoryArrays(Context* c, OutputChannel& out) :
  Theory(THEORY_ARRAY, c, out),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
  d_readIndicesMap(c),
  d_storesMap(c),
  d_disequalities(c),
  d_equalities(c),
  d_conflict()
{
}


TheoryArrays::~TheoryArrays() {
}


void TheoryArrays::addSharedTerm(TNode t) {
  Debug("arrays") << "TheoryArrays::addSharedTerm(): "
                  << t << endl;
}


void TheoryArrays::notifyEq(TNode lhs, TNode rhs) {
  /*
  Debug("arrays") << "TheoryArrays::notifyEq(): "
                  << lhs << " = " << rhs << endl;

  NodeManager* nm = NodeManager::currentNM();
  TNode eq = nm->mkNode(kind::EQUAL, lhs, rhs);
  d_cc.addEquality(eq);
  */
}

void TheoryArrays::notifyCongruent(TNode a, TNode b) {
  Debug("arrays") << "TheoryArrays::notifyCongruent(): "
       << a << " = " << b << endl;
  if(!d_conflict.isNull()) {
    return;
  }
  merge(a,b);
}


void TheoryArrays::check(Effort e) {
  Debug("arrays") <<"start check ";
  while(!done()) {
    Node assertion = get();
    Debug("arrays") << "TheoryArrays::check(): " << assertion << endl;

    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      d_cc.addEquality(assertion);
      if(!d_conflict.isNull()) {
        // addEquality can cause a notify congruent which calls merge
        // which can lead to a conflict
        Node conflict = constructConflict(d_conflict);
        d_conflict = Node::null();
        d_out->conflict(conflict, false);
        return;
      }
      merge(assertion[0], assertion[1]);
      break;
    case kind::NOT:
    {
      Assert(assertion[0].getKind() == kind::EQUAL ||
         assertion[0].getKind() == kind::IFF );
      Node a = assertion[0][0];
      Node b = assertion[0][1];

      addDiseq(assertion[0]);
      d_cc.addTerm(a);
      d_cc.addTerm(b);

      if(!d_conflict.isNull()) {
        // we got notified through notifyCongruent which called merge
        // after addTerm since we weren't watching a or b before
        Node conflict = constructConflict(d_conflict);
        d_conflict = Node::null();
        d_out->conflict(conflict, false);
        return;
      }
      else if(find(a) == find(b)) {
        Node conflict = constructConflict(assertion[0]);
        d_out->conflict(conflict, false);
        return;
        }
      Assert(!d_cc.areCongruent(a,b));
      // no need to call lemma generation since a disequality does now change
      // lemma application conditions?
      break;
    }
    default:
      Unhandled(assertion.getKind());
    }

  }
  // generate lemmas

  Debug("arrays") << "TheoryArrays::check(): done" << endl;
}

Node TheoryArrays::getValue(TNode n, Valuation* valuation) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( valuation->getValue(n[0]) == valuation->getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryArrays::merge(TNode a, TNode b) {
  Assert(d_conflict.isNull());

  Debug("arrays-merge")<<"TheoryArrays::merge() " << a <<" and " <<b <<endl;


  // make "a" the one with shorter diseqList
  CNodeTNodesMap::iterator deq_ia = d_disequalities.find(a);
  CNodeTNodesMap::iterator deq_ib = d_disequalities.find(b);

  if(deq_ia != d_disequalities.end()) {
    if(deq_ib == d_disequalities.end() ||
       (*deq_ia).second->size() > (*deq_ib).second->size()) {
      TNode tmp = a;
      a = b;
      b = tmp;
    }
  }
  a = find(a);
  b = find(b);

  if( a == b) {
    return;
  }

  // b becomes the canon of a
  setCanon(a, b);

  //FIXME: do i need to merge these if there is conflict?
  mergeIndices(a, b);
  mergeStores(a, b);

  deq_ia = d_disequalities.find(a);
  map<TNode, TNode> alreadyDiseqs;
  if(deq_ia != d_disequalities.end()) {
    /*
     * Collecting the disequalities of b, no need to check for conflicts
     * since the representative of b does not change and we check all the things
     * in a's class when we look at the diseq list of find(a)
     */

    CNodeTNodesMap::iterator deq_ib = d_disequalities.find(b);
    if(deq_ib != d_disequalities.end()) {
      CTNodeList* deq = (*deq_ib).second;
      for(CTNodeList::const_iterator j = deq->begin(); j!=deq->end(); j++) {
        TNode deqn = *j;
        TNode s = deqn[0];
        TNode t = deqn[1];
        TNode sp = find(s);
        TNode tp = find(t);
        Assert(sp == b || tp == b);
        if(sp == b) {
          alreadyDiseqs[tp] = deqn;
        } else {
          alreadyDiseqs[sp] = deqn;
        }
      }
    }

    /*
     * Looking for conflicts in the a disequality list. Note
     * that at this point a and b are already merged. Also has
     * the side effect that it adds them to the list of b (which
     * became the canonical representative)
     */

    CTNodeList* deqa = (*deq_ia).second;
    for(CTNodeList::const_iterator i = deqa->begin(); i!= deqa->end(); i++) {
      TNode deqn = (*i);
      Assert(deqn.getKind() == kind::EQUAL || deqn.getKind() == kind::IFF);
      TNode s = deqn[0];
      TNode t = deqn[1];
      TNode sp = find(s);
      TNode tp = find(t);

      if(find(s) == find(t)) {
        d_conflict = deqn;
        return;
      }
      Assert( sp == b || tp == b);

      // make sure not to add duplicates

      if(sp == b) {
        if(alreadyDiseqs.find(tp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs[tp] = deqn;
        }
      } else {
        if(alreadyDiseqs.find(sp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs[sp] = deqn;
        }
      }

    }
  }

}

Node TheoryArrays::constructConflict(TNode diseq) {
  Debug("arrays") << "arrays: begin constructConflict()" << endl;
  Debug("arrays") << "arrays:   using diseq == " << diseq << endl;

  // returns the reason the two terms are equal
  Node explanation = d_cc.explain(diseq[0], diseq[1]);

  NodeBuilder<> nb(kind::AND);

  if(explanation.getKind() == kind::EQUAL ||
     explanation.getKind() == kind::IFF) {
    // if the explanation is only one literal
    nb<<explanation;
  }
  else {
    Assert(explanation.getKind() == kind::AND);
    for(TNode::iterator i  = TNode(explanation).begin();
        i != TNode(explanation).end(); i++) {
      nb<<*i;
    }
  }

  nb<<diseq.notNode();
  Node conflict = nb;
  Debug("arrays") << "conflict constructed : " << conflict << endl;
  return conflict;
}


void TheoryArrays::addDiseq(TNode diseq) {
  Assert(diseq.getKind() == kind::EQUAL ||
         diseq.getKind() == kind::IFF);
  TNode a = diseq[0];
  TNode b = diseq[1];

  appendToDiseqList(find(a), diseq);
  appendToDiseqList(find(b), diseq);

}

void TheoryArrays::appendToDiseqList(TNode of, TNode eq) {
  Debug("arrays") << "appending " << eq << endl
              << "  to diseq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  CNodeTNodesMap::iterator deq_i = d_disequalities.find(of);
  CTNodeList* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) CTNodeList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }

  deq->push_back(eq);
}

void TheoryArrays::appendToEqList(TNode of, TNode eq) {
  Debug("arrays") << "appending "<< eq << endl
      << " to equality list of " << of << endl;

  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  Assert(of == debugFind(of));

  CNodeTNodesMap::iterator eq_i = d_equalities.find(of);
  CTNodeList* eql;
  if(eq_i == d_equalities.end()) {
    eql = new(getContext()->getCMM()) CTNodeList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_equalities.insertDataFromContextMemory(of, eql);
  } else {
    eql = (*eq_i).second;
  }
  eql->push_back(eq);

}

void TheoryArrays::appendIndex(TNode a, TNode index) {
  Debug("arrays::index")<<"TheoryArrays::appendIndex a       = "<<a<<" i = "<<index<<"\n";

  Assert(a.getKind() == kind::ARRAY_TYPE);
  a = find(a);

  Debug("arrays::index")<<"TheoryArrays::appendIndex find(a) = "<<a<<"\n";
  CTNodeList* ilist;
  CNodeTNodesMap::iterator it = d_readIndicesMap.find(a);
  if( it == d_readIndicesMap.end()) {
    ilist = new (getContext()->getCMM()) CTNodeList(true, getContext(), false,
                                                    ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_readIndicesMap.insertDataFromContextMemory(a, ilist);
    Debug("arrays::index")<<"TheoryArrays::appendIndex adding (find(a), [index]) entry \n";
    ilist->push_back(index);
  } else {
    ilist = (*it).second;
    // check if index already in list
    //FIXME: maybe do this lazily when merging?
    CTNodeList::const_iterator i = ilist->begin();
    for(; i!= ilist->end(); i++) {
      if((*i) == index) {
        Debug("arrays::index")<<"TheoryArrays::appendIndex index already exits \n";
        return;
      }
    }
    Debug("arrays::index")<<"TheoryArrays::appendIndex appending index to find(a) \n";
    ilist->push_back(index);

  }

}

void TheoryArrays::appendStore(TNode a, TNode store) {

}

void TheoryArrays::mergeIndices(TNode a, TNode b) {
  Assert(find(a) == find(b) && find(a) == b);
  set<TNode> aindices;
  CNodeTNodesMap::iterator ialist = d_readIndicesMap.find(a);
  CTNodeList* alist = (*ialist).second;

  // collect a indicies

  CTNodeList::const_iterator ia = alist->begin();
  for( ; ia!= alist ->end(); ia++ ) {
    aindices.insert(*ia);
  }

  // add b indices to the a list of indices if they are not already there

  CNodeTNodesMap::iterator iblist = d_readIndicesMap.find(b);
  CTNodeList* blist = (*iblist).second;
  CTNodeList::const_iterator ib = blist->begin();
    for( ; ib!= blist ->end(); ib++ ) {
      if(aindices.find(*ib) == aindices.end()) {
        alist->push_back(*ib);
      }
    }

   //TODO: remove b from map
   //


}

void TheoryArrays::mergeStores(TNode a, TNode b) {

}

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
#include "theory/theory_engine.h"
#include "expr/kind.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arrays;


TheoryArrays::TheoryArrays(int id, Context* c, OutputChannel& out) :
  Theory(id, c, out),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_unionFind(c),
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
  Debug("arrays") << "TheoryArrays::notifyEq(): "
                  << lhs << " = " << rhs << endl;
  // TODO: call the congruence rule if necessary
}

void TheoryArrays::notifyCongruent(TNode a, TNode b) {
  Debug("arrays") << "TheoryArrays::notifyCongruent(): "
       << a << " = " << b << endl;
}

void TheoryArrays::check(Effort e) {
  while(!done()) {
    Node assertion = get();
    Debug("arrays") << "TheoryArrays::check(): " << assertion << endl;


    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      d_cc.addEquality(assertion);
      break;
    case kind::NOT:
      if(assertion[0].getKind() == kind::EQUAL ||
         assertion[0].getKind() == kind::IFF ) {

        Node a = assertion[0][0];
        Node b = assertion[0][1];

        //TODO: continue
        //appendToDiseqList(assertion[0]);

        d_cc.addTerm(a);
        d_cc.addTerm(b);

      }
      break;
    default:
      Unhandled(assertion.getKind());
    }


  }
  Debug("arrays") << "TheoryArrays::check(): done" << endl;
}

Node TheoryArrays::getValue(TNode n, TheoryEngine* engine) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( engine->getValue(n[0]) == engine->getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}


void TheoryArrays::merge(TNode a, TNode b) {
  Assert(d_conflict.isNull());

  // make "a" the one with shorter diseqList
  EqLists::iterator deq_ia = d_disequalities.find(a);
  EqLists::iterator deq_ib = d_disequalities.find(b);

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

  d_unionFind.setCanon(a, b);

  EqLists::iterator deq_i = d_disequalities.find(a);

  if(deq_i != d_disequalities.end()) {
    EqList* deq = (*deq_i).second;
    for(EqList::const_iterator i = deq->begin(); i!= deq->end(); i++) {
      /*
       * Looking for conflicts in the disequality list. Note
       * that at this point a and b are already merged.
       */
      TNode deqn = (*i);
      Assert(deqn.getKind() == kind::EQUAL || deqn.getKind() == kind::IFF);
      TNode s = deqn[0];
      TNode t = deqn[1];
      if(find(s) == find(t)) {
        d_conflict = deqn;
        return;
      }

    }
  }

}



void TheoryArrays::appendToDiseqList(TNode of, TNode eq) {
  Debug("arrays") << "appending " << eq << endl
              << "  to diseq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  EqLists::iterator deq_i = d_disequalities.find(of);
  EqList* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }

  deq->push_back(eq);

}

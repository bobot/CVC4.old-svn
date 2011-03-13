/*********************                                                        */
/*! \file theory_arrays.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of arrays.
 **
 ** Theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H

#include "theory/theory.h"
#include "theory/arrays/union_find.h"
#include "util/congruence_closure.h"
#include "array_info.h"
#include "util/hash.h"
#include "util/ntuple.h"
#include <iostream>
#include <map>
namespace CVC4 {
namespace theory {
namespace arrays {

class TheoryArrays : public Theory {

private:
  class CongruenceChannel {
    TheoryArrays* d_arrays;

  public:
    CongruenceChannel(TheoryArrays* arrays) : d_arrays(arrays) {}
    void notifyCongruent(TNode a, TNode b) {
      d_arrays->notifyCongruent(a, b);
    }
  }; /* class CongruenceChannel*/
  friend class CongruenceChannel;

  /**
   * Output channel connected to the congruence closure module.
   */
  CongruenceChannel d_ccChannel;

  /**
   * Instance of the congruence closure module.
   */
  CongruenceClosure<CongruenceChannel, CONGRUENCE_OPERATORS_2
                                 (kind::SELECT, kind::STORE)> d_cc;

  /**
   * Union find for storing the equalities.
   */

  UnionFind<Node, NodeHashFunction> d_unionFind;

  /**
   * Received a notification from the congruence closure algorithm that the two nodes
   * a and b have been merged.
   */

  /**
   * set of store terms
   */
  std::set<TNode> d_stores;

  /**
   * set of select terms
   */

  std::set<TNode> d_selects;

  void notifyCongruent(TNode a, TNode b);

  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > CTNodeListAlloc;
  typedef context::CDMap<Node, CTNodeListAlloc*, NodeHashFunction> CNodeTNodesMap;

  /**
   * List of all disequalities this theory has seen.
   * Maintaints the invariant that if a is in the
   * disequality list of b, then b is in that of a.
   * */
  CNodeTNodesMap d_disequalities;

  /** List of all (potential) equalities to be propagated. */
  CNodeTNodesMap d_equalities;

  /**
   * stores the conflicting disequality (still need to call construct
   * conflict to get the actual explanation)
   */
  Node d_conflict;

  /**
   * true constant (sometimes check gets called on a CONST_BOOLEAN)
   */
  Node d_true_const;

  /**
   * Map from a congruence class canonical representative of type array to a
   * pointer to Info that stores information useful to axiom instantiation
   */
  ArrayInfo d_infoMap;

  /**
   * Ext-Lemma and RoW-lemma caches
   */
  std::hash_set<std::pair<TNode, TNode>, TNodePairHashFunction> d_extLemmaCache;
  std::hash_set<quad<TNode, TNode, TNode, TNode>, TNodeQuadHashFunction > d_RoWLemmaCache;

  /* TODO: maybe have them context dependent?
  void updateLemmaCache(TNode a, TNode b);
  void updateLemmaCache(TNode i, TNode j, TNode a, TNode b);
  */
  /**
   * Checks if any new RoW lemmas have to be generated after a ~ b.
   * Preconditions:
   *      find(a) != find(b)
   *      after this call setCanon(a,b) will be called
   *
   */

  void checkRoWLemmas(TNode a, TNode b);

    /**
     * Marking stores and reads that have been already registered
     */
    //struct ArrayTestId {};
    //typedef expr::Attribute<ArrayTestId, bool> ArrayTest;

    /*
     * Helper methods
     */

  void addDiseq(TNode diseq);
  void appendToDiseqList(TNode of, TNode eq);
  void appendToEqList(TNode of, TNode eq);
  Node constructConflict(TNode diseq);

  /**
   * Merges two congruence classes in the internal
   * union-find and checks for a conflict.
   */

  void merge(TNode a, TNode b);
  inline TNode find(TNode a);
  inline TNode debugFind(TNode a) const;

  inline void setCanon(TNode a, TNode b);
  /**
   * Add a RoW1 lemma of the form
   *    read (store(a, i, v) i) = v
   */
  void addRoW1Lemma(TNode a);

  /**
   * Adds a RoW lemma of the form:
   *    i = j OR a[j] = b [j]
   * Preconditions: ...
   */
  void addRoW2Lemma(TNode a, TNode b, TNode i, TNode j);

  /**
   * Adds a new Ext lemma of the form
   *    a = b OR a[k]!=b[k], for a new variable k
   */

  void addExtLemma(TNode a, TNode b);

  /**
   *
   */
  void checkRoWForIndex(TNode i, TNode a);

  std::set<quad<TNode, TNode, TNode, TNode> > d_RoWLemmaQueue;

  void insertInRoWLemmaQueue(TNode a, TNode b, TNode i, TNode j){
    if(i != j) {
      d_RoWLemmaQueue.insert(make_quad(a,b,i,j));
    }
  }

  void dischargeRoWLemmas() {
    std::set<quad<TNode, TNode, TNode, TNode> >::iterator it = d_RoWLemmaQueue.begin();
    for( ; it!= d_RoWLemmaQueue.end(); it++) {
      addRoW2Lemma((*it).first, (*it).second, (*it).third, (*it).fourth);
    }
    d_RoWLemmaQueue.clear();
  }

  bool isAxiom(TNode a, TNode b);

public:
  TheoryArrays(context::Context* c, OutputChannel& out);
  ~TheoryArrays();

  void preRegisterTerm(TNode n) {
    Debug("arrays-preregister")<<"Arrays::preRegisterTerm "<<n<<"\n";

    switch(n.getKind()) {
    case kind::SELECT:
      Debug("arrays-preregister")<<"n[0]"<<n[0]<<" "<<n[1]<<"\n";
      d_infoMap.addIndex(n[0], n[1]);
      break;

    case kind::STORE:
    {
      d_infoMap.addEqStore(n, n);
      d_infoMap.addInStore(n[0], n);

      TNode i = n[1];
      TNode v = n[2];

      NodeManager* nm = NodeManager::currentNM();
      Node ni = nm->mkNode(kind::SELECT, n, i);
      Node eq = nm->mkNode(kind::EQUAL, ni, v);

      d_infoMap.addIndex(n, i);

      d_cc.addEquality(eq);
      //d_out->lemma(eq);
      break;
    }
    case kind::VARIABLE: {
      // adding each term of type array to the
      if(n.getType().isArray()) {
        d_infoMap.addEmptyEntry(n);
      }
    }
    default:
      Debug("darrays")<<"Arrays::preRegisterTerm \n";
    }
  }

  void registerTerm(TNode n) {
    Debug("arrays-register")<<"Arrays::registerTerm "<<n<<"\n";

    if(n.getKind() == kind::STORE && find(n) == n) {
      const CTNodeList* is = d_infoMap.getIndices(n);
      for(CTNodeList::const_iterator it = is->begin(); it != is->end(); it++) {
        TNode i = (*it);
        addRoW2Lemma(n, n[0],n[1],i);
      }

    }
  }

  void presolve() { Debug("arrays")<<"Presolving \n";}

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void check(Effort e);
  void propagate(Effort e) { }
  void explain(TNode n) { }
  Node getValue(TNode n, Valuation* valuation);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryArrays"); }

};/* class TheoryArrays */

inline void TheoryArrays::setCanon(TNode a, TNode b) {
  d_unionFind.setCanon(a, b);
}

inline TNode TheoryArrays::find(TNode a) {
  return d_unionFind.find(a);
}

inline TNode TheoryArrays::debugFind(TNode a) const {
  return d_unionFind.debugFind(a);
}



}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H */

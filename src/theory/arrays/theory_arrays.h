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
#include "util/congruence_closure.h"
#include "theory/arrays/union_find.h"

#include <ext/hash_set>
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

  struct ArrayRoWId {};
  typedef expr::Attribute<ArrayRoWId, bool> ArrayRoW;

  struct ArrayInStoreId {};
  typedef expr::Attribute<ArrayInStoreId, bool> ArrayInStore;

  struct ArrayInSelectId {};
  typedef expr::Attribute<ArrayInSelectId, bool> ArrayInSelect;

  const static int mode = 1;

  /**
   * Output channel connected to the congruence closure module.
   */
  CongruenceChannel d_ccChannel;

  /**
   * Instance of the congruence closure module.
   */
  CongruenceClosure<CongruenceChannel, CONGRUENCE_OPERATORS_2 (kind::SELECT, kind::STORE)> d_cc;

  /**
   * Union find for storing the equalities.
   */

  UnionFind<Node, NodeHashFunction> d_unionFind;

  /**
   * Union find over the relation "two arrays differ on finitely many indices"
   * note that this includes the first union find
   */
  UnionFind<Node, NodeHashFunction> d_unionFindI;

  /**
   * Received a notification from the congruence closure algorithm that the two nodes
   * a and b have been merged.
   */
  void notifyCongruent(TNode a, TNode b);

  /**
   * set of array read terms we care about a[i]
   */
  std::set<TNode> proxied;

  /**
   * set of terms of array type at initialization
   */
  std::set<TNode> array_terms;

  /**
   * set of the store terms at initialization
   */
  std::set<TNode> store_terms; //FIXME: stored twice

  /**
   * map from node to all the indices it is read at
   */

  map<TNode, std::set<TNode> > index_map;

  /**
   * map from an array a to all arrays it differs from on
   * only one position
   */

  map<TNode, std::set<TNode> > store_map;

  /**
   * store the lemmas already learned to make sure not to add duplicates
   */
  std::set<TNode> lemma_cache;

  /**
   * cache of values the Ext rule was called on to make
   * sure we don't generate multiple lemmas for the same arrays
   */

  std::set<std::pair<TNode,TNode> > ext_cache;

  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > EqList;
  typedef context::CDMap<Node, EqList*, NodeHashFunction> EqLists;

  /**
   * List of all disequalities this theory has seen.
   * Maintaints the invariant that if a is in the
   * disequality list of b, then b is in that of a.
   * */
  EqLists d_disequalities;

  /** List of all (potential) equalities to be propagated. */
  EqLists d_equalities;

  /**
   * stores the conflicting disequality (still need to call construct
   * conflict to get the actual explanation)
   */
  Node d_conflict;

  /*
   * Helper methods
   */

  void addDiseq(TNode diseq);
  void appendToDiseqList(TNode of, TNode eq);
  void appendToEqList(TNode of, TNode eq);
  Node constructConflict(TNode diseq);

  void generateLemmas(TNode a, TNode b);

  void addProxy(TNode n);
  void addRoWLemma(TNode n);
  void addExtLemma(TNode a, TNode b);
  bool condRoW(TNode a, TNode b, TNode i);
  bool condExt(TNode a, TNode b);

  bool condRoW0(TNode a, TNode b, TNode i);
  bool condExt0(TNode a, TNode b);

  bool condRoW1(TNode a, TNode b, TNode i);
  bool condExt1(TNode a, TNode b);

  void setupStore(TNode n);
  void setupSelect(TNode n);

  bool hasExtLemma(TNode a, TNode b);

  void generateLemmas();

public:
  TheoryArrays(int id, context::Context* c, OutputChannel& out);
  ~TheoryArrays();
  void preRegisterTerm(TNode n) {
    Debug("arrays-register") << "pre-registering "<< n <<std::endl;

    switch(n.getKind()) {
    case kind::SELECT: {
      setupSelect(n);
      break;
    }
    case kind::STORE: {
      setupStore(n);
      break;
    }
    case kind::VARIABLE: {
      if(n.getType().isArray()) {
        array_terms.insert(n);
      }
      break;
    }
    case kind::EQUAL:
      break;
    default:
      Unhandled("arrays: Unknown kind in preregistration. \n");
    }

    d_cc.addTerm(n);
  }

  void registerTerm(TNode n) {
    Debug("arrays-register") << "registering "<< n << std::endl;

    if(mode != 0)
          return;

    if( n.getKind() == kind::SELECT) {
      addRoWLemma(n);
    }

    if( n.getKind() == kind::STORE ||
        (n.getKind() == kind::VARIABLE && n.getType().isArray())) {

      for(std::set<TNode>::iterator it = array_terms.begin(); it != array_terms.end(); it++) {
        // check that the arrays are of the same type
        if(*it != n && (*it).getType() == n.getType()) {
          addExtLemma(n, (*it));
        }
      }
    }

  }

  RewriteResponse preRewrite(TNode in, bool topLevel) {
    Debug("arrays-rewrite") << "pre-rewriting " << in
                            << " topLevel==" << topLevel << std::endl;
    return RewriteComplete(in);
  }

  RewriteResponse postRewrite(TNode in, bool topLevel) {
    Debug("arrays-rewrite") << "post-rewriting " << in
                            << " topLevel==" << topLevel << std::endl;
    return RewriteComplete(in);
  }

  void presolve() {
    Unimplemented();
  }

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void check(Effort e);
  void propagate(Effort e) { }
  void explain(TNode n, Effort e) { }
  Node getValue(TNode n, TheoryEngine* engine);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryArrays"); }

  /**
   * Merges two congruence classes in the internal
   * union-find and checks for a conflict.
   */

  void merge(TNode a, TNode b);
  inline TNode find(TNode a);
  inline TNode debugFind(TNode a) const;

  inline TNode findI(TNode a);
  inline TNode debugFindI(TNode a) const;

  inline void setCanon(TNode a, TNode b);




};/* class TheoryArrays */

inline void TheoryArrays::setCanon(TNode a, TNode b) {
  d_unionFind.setCanon(a, b);

  if(mode> 0) {
    d_unionFindI.setCanon(findI(a), findI(b));
  }
}

inline TNode TheoryArrays::find(TNode a) {
  return d_unionFind.find(a);
}

inline TNode TheoryArrays::debugFind(TNode a) const {
  return d_unionFind.debugFind(a);
}

inline TNode TheoryArrays::findI(TNode a) {
  return d_unionFindI.find(a);
}

inline TNode TheoryArrays::debugFindI(TNode a) const {
  return d_unionFindI.debugFind(a);
}


inline bool TheoryArrays::condRoW(TNode b, TNode c, TNode i) {
  switch(mode){
  case 0: {
    return condRoW0(b, c, i);
    break;
  }
  case 1: {
    return condRoW1(b, c, i);
    break;
  }
  default:
    Unhandled("Unknown arrays mode \n");
  }

}


inline bool TheoryArrays::condExt(TNode a, TNode b) {
  switch(mode){
  case 0: {
    return condExt0(a, b);
    break;
  }
  case 1: {
    return condExt1(a, b);
    break;
  }
  default:
    Unhandled("Unknown arrays mode \n");
  }

}


inline void TheoryArrays::setupStore(TNode n) {
  Assert(n.getKind() == kind::STORE);
  if(store_map.find(n) == store_map.end()) {
    std::set<TNode> ss;
    ss.insert(n[0]);
    store_map[n] = ss;
  }
  else {
    std::set<TNode> ss = store_map[n];
    ss.insert(n[0]);
    store_map[n] = ss;
  }

  store_terms.insert(n);
  n[0].setAttribute(ArrayInStore(), true);
  if(mode > 0) {
    TNode n1 = n[0];
    n1 = findI(n1);
    n = findI(n);
    d_unionFindI.setCanon(n, n1);
  }
  array_terms.insert(n);

}

inline void TheoryArrays::setupSelect(TNode n) {
  Assert(n.getKind()== kind::SELECT);
  if(index_map.find(n) == index_map.end()) {
    std::set<TNode> is;
    is.insert(n[1]);
    index_map[n] = is;
  }
  else {
    std::set<TNode> is = index_map[n];
    is.insert(n[1]);
    index_map[n] = is;
  }

  proxied.insert(n);
  n[0].setAttribute(ArrayInSelect(), true);
}


}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H */

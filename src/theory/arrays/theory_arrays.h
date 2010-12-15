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

  struct ArrayExt0Id {};
  typedef expr::Attribute<ArrayExt0Id, bool> ArrayExt0;

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
   * store the lemmas already learned to make sure not to add duplicates
   */
  std::set<TNode> lemma_cache;

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

  void addProxy(TNode n);
  void addRoW0Lemma(TNode n);
  void addExt0Lemma(TNode a, TNode b);

public:
  TheoryArrays(int id, context::Context* c, OutputChannel& out);
  ~TheoryArrays();
  void preRegisterTerm(TNode n) {
    Debug("arrays-register") << "pre-registering "<< n <<std::endl;
    if(n.getKind() == kind::SELECT) {
      addProxy(n);
    }

    if(n.getKind() == kind::STORE || n.getKind() == kind::VARIABLE) {
      // store all the terms of type ARRAY
      if(n.getKind() == kind::STORE) {
        store_terms.insert(n);
      }
      array_terms.insert(n);
    }
  }

  void registerTerm(TNode n) {
    Debug("arrays-register") << "registering "<< n << std::endl;

    if( n.getKind() == kind::STORE ||
        (n.getKind() == kind::VARIABLE && n.getType().isArray())) {

      for(std::set<TNode>::iterator it = array_terms.begin(); it != array_terms.end(); it++) {
        // check that the arrays are of the same type
        if(*it != n && (*it).getType() == n.getType()) {
          addExt0Lemma(n, (*it));
        }
      }
      //n.setAttribute(ArrayExt0(), true);
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




};/* class TheoryArrays */


inline TNode TheoryArrays::find(TNode a) {
  return d_unionFind.find(a);
}

inline TNode TheoryArrays::debugFind(TNode a) const {
  return d_unionFind.debugFind(a);
}

inline void TheoryArrays::addProxy(TNode n) {
  Assert(n.getKind() == kind::SELECT);
  if(proxied.find(n) != proxied.end()) {
    Debug("arrays-proxy")<<"addProxy " <<  n << "already proxied \n";
    return;
  }

  Debug("arrays-proxy")<<"addProxy " <<  n << "\n";
  proxied.insert(n);
  addRoW0Lemma(n);
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H */

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

  Node d_conflict;

  void appendToDiseqList(TNode of, TNode eq);

public:
  TheoryArrays(int id, context::Context* c, OutputChannel& out);
  ~TheoryArrays();
  void preRegisterTerm(TNode n) {
    Debug("arrays-register") << "pre-registering "<< n << std::endl;
    if(n.getKind() == kind::SELECT) {
      proxied.insert(n);
    }

    if(n.getKind() == kind::STORE || n.getKind() == kind::VARIABLE) {
      // store all the terms of type ARRAY
      array_terms.insert(n);
    }
  }

  void registerTerm(TNode n) {
    Debug("arrays-register") << "registering "<< n << std::endl;
    if(n.getKind() == kind::STORE || n.getKind() == kind::VARIABLE) {

      for(std::set<TNode>::iterator it = array_terms.begin(); it != array_terms.end(); it++) {
        // check that the arrays are of the same type
        if(*it != n && (*it).getType() == n.getType()) {
          // add the Ext0 lemma
          //    for all two arrays a, b of the same type add a != b => a[i]!= b[i]
          //    for a new variable i.

          NodeManager* nm = NodeManager::currentNM();
          Node neq1 = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, n, *it));
          Node new_var = nm->mkVar(n.getType()[0]);
          Node select0 = nm->mkNode(kind::SELECT, n, new_var);
          Node select1 = nm->mkNode(kind::SELECT, *it, new_var);
          Node neq2 = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, select0, select1));
          Node impl = nm->mkNode(kind::IMPLIES, neq1, neq2);

          d_out->lemma(impl);
          Debug("arrays-lemma") << "array-lemma "<< impl << std::endl;
          // add the new terms a[i], b[i] to the list of proxied variables
          proxied.insert(select0);
          proxied.insert(select1);
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

};/* class TheoryArrays */


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

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
 ** TODO: add summary of rules implemented RoW1, RoW2, ext etc with the implemented
 **
 ** Theory of arrays.
 **/

/*
Overview of decision procedure

Preliminary notation:
  Stores(a)  = {t | a ~ t and t = store( _ _ _ ) or t = store (a _ _) }
  Indices(a) = {i | there exists a term a[i]}
  ~ represents the equivalence relation based on the asserted equalities in the
  current context.

The rules implemented are the following:
            store(b i v)
    RoW1 -------------------
         store(b i v)[i] = v

          store(b i v)  a'[j]
    RoW2 ---------------------- [ a' ~ store(b i v) or a' ~ b ]
          i = j OR a[j] = b[j]

         a  b same kind arrays
    Ext ------------------------ [ a!= b in current context, k new var]
          a = b OR a[k] != b[k]


 The RoW1 one rule is implemented implicitly as follows:
    - for each store(b i v) term add the following equality to the congruence
      closure store(b i v)[i] = v
    - if one of the literals in a conflict is of the form store(b i v)[i] = v
      remove it from the conflict

 Because new store terms are not created, we need to check if we need to
 instantiate a new RoW2 axiom in the following cases:
    1. the congruence relation changes (i.e. two terms get merged)
        - when a new equality between array terms a = b is asserted we check if
          we can instantiate a RoW2 lemma for all pairs of indices i where a is
          being read and stores
        - this is only done during full effort check
    2. a new read term is created either as a consequences of an Ext lemma or a
       RoW2 lemma
        - this is implemented in the checkRoWForIndex method which is called
          when preregistering a term of the form a[i].
        - as a consequence lemmas are instantiated even before full effort check

 The Ext axiom is instantiated when a disequality is asserted during full effort
 check. Ext lemmas are stored in a cache to prevent instantiating essentially
 the same lemma multiple times.

 */

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H

#include "theory/theory.h"
#include "theory/arrays/union_find.h"
#include "util/congruence_closure.h"
#include "array_info.h"
#include "util/hash.h"
#include "util/ntuple.h"
#include "util/stats.h"
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
   * Received a notification from the congruence closure algorithm that the two
   * nodes a and b have become congruent.
   */

  void notifyCongruent(TNode a, TNode b);


  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > CTNodeListAlloc;
  typedef context::CDMap<Node, CTNodeListAlloc*, NodeHashFunction> CNodeTNodesMap;

  /**
   * List of all disequalities this theory has seen. Maintains the invariant that
   * if a is in the disequality list of b, then b is in that of a.
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
   * Context dependent map from a congruence class canonical representative of
   * type array to an Info pointer that keeps track of information useful to axiom
   * instantiation
   */

  ArrayInfo d_infoMap;

  /**
   * Extensionality lemma cache which stores the array pair (a,b) for which
   * a lemma of the form (a = b OR a[k]!= b[k]) has been added to the SAT solver.
   */
  std::hash_set<std::pair<TNode, TNode>, TNodePairHashFunction> d_extLemmaCache;

  /**
   * Read-over-write lemma cache storing a quadruple (a,b,i,j) for which a
   * the lemma (i = j OR a[j] = b[j]) has been added to the SAT solver. Needed
   * to prevent infinite recursion in addRoW2Lemma.
   */
  std::hash_set<quad<TNode, TNode, TNode, TNode>, TNodeQuadHashFunction > d_RoWLemmaCache;

  /*
   * Congruence helper methods
   */

  void addDiseq(TNode diseq);
  void appendToDiseqList(TNode of, TNode eq);
  void appendToEqList(TNode of, TNode eq);
  Node constructConflict(TNode diseq);

  /**
   * Merges two congruence classes in the internal union-find and checks for a
   * conflict.
   */

  void merge(TNode a, TNode b);
  inline TNode find(TNode a);
  inline TNode debugFind(TNode a) const;

  inline void setCanon(TNode a, TNode b);

  /**
   * Adds a RoW2 lemma of the form:
   *    i = j OR a[j] = b[j]
   */
  void addRoW2Lemma(TNode a, TNode b, TNode i, TNode j);

  /**
   * Adds a new Ext lemma of the form
   *    a = b OR a[k]!=b[k], for a new variable k
   */
  void addExtLemma(TNode a, TNode b);

  /**
   * Because RoW1 axioms of the form (store a i v) [i] = v are not added as
   * explicitly but are kept track of internally, is axiom recognizez an axiom
   * of the above form given the two terms in the equality.
   */
  bool isAxiom(TNode lhs, TNode rhs);

  /**
   * Checks if any new RoW lemmas need to be generated after merging arrays a
   * and b; called after setCanon.
   */
  void checkRoWLemmas(TNode a, TNode b);

  /**
   * Called after a new select term a[i] is created to check whether new RoW2
   * lemmas need to be instantiated.
   */
  void checkRoWForIndex(TNode i, TNode a);

  /**
   * Lemma helper functions to prevent changing the list we are iterating through.
   */

  void insertInQuadQueue(std::set<quad<TNode, TNode, TNode, TNode> >& queue, TNode a, TNode b, TNode i, TNode j){
    if(i != j) {
      queue.insert(make_quad(a,b,i,j));
    }
  }

  void dischargeRoWLemmas(std::set<quad<TNode, TNode, TNode, TNode> >& queue ) {
    std::set<quad<TNode, TNode, TNode, TNode> >::const_iterator it = queue.begin();
    for( ; it!= queue.end(); it++) {
      addRoW2Lemma((*it).first, (*it).second, (*it).third, (*it).fourth);
    }
    queue.clear();
  }

  /*
   * === STATISTICS ===
   */

  /** number of RoW2 lemmas */
  IntStat d_numRoW2;
  /** number of Ext lemmas */
  IntStat d_numExt;

  /** time spent in check() */
  TimerStat d_checkTimer;

  /** time spent in preregisterTerm() */
  TimerStat d_preregisterTimer;

public:
  TheoryArrays(context::Context* c, OutputChannel& out);
  ~TheoryArrays();

  /**
   * Stores in d_infoMap the following information for each term a of type array:
   *
   *    - all i, such that there exists a term a[i] or a = store(b i v)
   *      (i.e. all indices it is being read atl; store(b i v) is implicitly read at
   *      position i due to the implicit axiom store(b i v)[i] = v )
   *
   *    - all the stores a is congruent to (this information is context dependent)
   *
   *    - all store terms of the form store (a i v) (i.e. in which a appears
   *      directly; this is invariant because no new store terms are created)
   *
   * Note: completeness depends on having pre-register called on all the input
   *       terms before starting to instantiate lemmas.
   */
  void preRegisterTerm(TNode n) {
    //TimerStat::CodeTimer codeTimer(d_preregisterTimer);
    Debug("arrays-preregister")<<"Arrays::preRegisterTerm "<<n<<"\n";

    switch(n.getKind()) {
    case kind::SELECT:
      d_infoMap.addIndex(n[0], n[1]);
      checkRoWForIndex(n[1], find(n[0]));
      break;

    case kind::STORE:
    {
      TNode a = n[0];
      TNode i = n[1];
      TNode v = n[2];

      NodeManager* nm = NodeManager::currentNM();
      Node ni = nm->mkNode(kind::SELECT, n, i);
      Node eq = nm->mkNode(kind::EQUAL, ni, v);

      d_cc.addEquality(eq);

      d_infoMap.addIndex(n, i);
      d_infoMap.addStore(n, n);
      d_infoMap.addStore(a, n);

      break;
    }
    case kind::VARIABLE: {
      // adding an empty entry for each term of type array
      if(n.getType().isArray()) {
        d_infoMap.addEmptyEntry(n);
      }
    }
    default:
      Debug("darrays")<<"Arrays::preRegisterTerm non-array term. \n";
    }
  }

  /**
   * Instantiates RoW2 lemmas for store terms which would be missed otherwise
   * because we only check for RoW2 lemmas when merging terms or when creating a
   * new read term.
   */
  void registerTerm(TNode n) {
    Debug("arrays-register")<<"Arrays::registerTerm "<<n<<"\n";
    /*
    if(n.getKind() == kind::STORE && find(n) == n) {
      const CTNodeList* is = d_infoMap.getIndices(n);
      for(CTNodeList::const_iterator it = is->begin(); it != is->end(); it++) {
        TNode i = (*it);
        //TODO: think of a way to move this from here, understand the way stuff is called!
        addRoW2Lemma(n, n[0],n[1],i);
      }

    }
    */
  }

  void presolve() {
    Debug("arrays")<<"Presolving \n";
  }

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

/*********************                                                        */
/*! \file theory_arrays.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: lianah
 ** Minor contributors (to current version): barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of arrays
 **
 ** Theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H

#include "theory/theory.h"
#include "theory/arrays/array_info.h"
#include "util/stats.h"
#include "theory/uf/equality_engine.h"
#include "context/cdhashmap.h"
#include "context/cdqueue.h"

namespace CVC4 {
namespace theory {
namespace arrays {

/**
 * Decision procedure for arrays.
 *
 * Overview of decision procedure:
 *
 * Preliminary notation:
 *   Stores(a)  = {t | a ~ t and t = store( _ _ _ )} 
 *   InStores(a) = {t | t = store (b _ _) and a ~ b }
 *   Indices(a) = {i | there exists a term b[i] such that a ~ b or store(b i v)}
 *   ~ represents the equivalence relation based on the asserted equalities in the
 *   current context.
 * 
 * The rules implemented are the following:
 *             store(b i v)
 *     Row1 -------------------
 *          store(b i v)[i] = v
 * 
 *           store(b i v)  a'[j]
 *     Row ---------------------- [ a' ~ store(b i v) or a' ~ b ]
 *           i = j OR a[j] = b[j]
 * 
 *          a  b same kind arrays
 *     Ext ------------------------ [ a!= b in current context, k new var]
 *           a = b OR a[k] != b[k]p
 * 
 * 
 *  The Row1 one rule is implemented implicitly as follows:
 *     - for each store(b i v) term add the following equality to the congruence
 *       closure store(b i v)[i] = v
 *     - if one of the literals in a conflict is of the form store(b i v)[i] = v
 *       remove it from the conflict
 * 
 *  Because new store terms are not created, we need to check if we need to
 *  instantiate a new Row axiom in the following cases:
 *     1. the congruence relation changes (i.e. two terms get merged)
 *         - when a new equality between array terms a = b is asserted we check if
 *           we can instantiate a Row lemma for all pairs of indices i where a is
 *           being read and stores
 *         - this is only done during full effort check
 *     2. a new read term is created either as a consequences of an Ext lemma or a
 *        Row lemma
 *         - this is implemented in the checkRowForIndex method which is called
 *           when preregistering a term of the form a[i].
 *         - as a consequence lemmas are instantiated even before full effort check
 * 
 *  The Ext axiom is instantiated when a disequality is asserted during full effort
 *  check. Ext lemmas are stored in a cache to prevent instantiating essentially
 *  the same lemma multiple times.
 */

static inline std::string spaces(int level)
{
  std::string indentStr(level, ' ');
  return indentStr;
}

class TheoryArrays : public Theory {

  /////////////////////////////////////////////////////////////////////////////
  // MISC
  /////////////////////////////////////////////////////////////////////////////

  private:

  /** True node for predicates = true */
  Node d_true;

  /** True node for predicates = false */
  Node d_false;

  // Statistics

  /** number of Row lemmas */
  IntStat d_numRow;
  /** number of Ext lemmas */
  IntStat d_numExt;
  /** number of propagations */
  IntStat d_numProp;
  /** number of explanations */
  IntStat d_numExplain;
  /** time spent in check() */
  TimerStat d_checkTimer;

  public:

  TheoryArrays(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation);
  ~TheoryArrays();

  std::string identify() const { return std::string("TheoryArrays"); }

  /////////////////////////////////////////////////////////////////////////////
  // PREPROCESSING
  /////////////////////////////////////////////////////////////////////////////

  private:

  // PPNotifyClass: dummy template class for d_ppEqualityEngine - notifications not used
  class PPNotifyClass {
  public:
    bool notify(TNode propagation) { return true; }
    void notify(TNode t1, TNode t2) { }
  };

  /** The notify class for d_ppEqualityEngine */
  PPNotifyClass d_ppNotify;

  /** Equaltity engine */
  uf::EqualityEngine<PPNotifyClass> d_ppEqualityEngine;

  // List of facts learned by preprocessor - needed for permanent ref for benefit of d_ppEqualityEngine
  context::CDList<Node> d_ppFacts;

  // Cache for preprocessing of atoms.
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_ppCache;

  Node preprocessTerm(TNode term);
  Node recursivePreprocessTerm(TNode term);

  public:

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);
  Node ppRewrite(TNode atom);

  /////////////////////////////////////////////////////////////////////////////
  // T-PROPAGATION / REGISTRATION
  /////////////////////////////////////////////////////////////////////////////

  private:

  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  /** Should be called to propagate the literal.  */
  bool propagate(TNode literal);

  /** Explain why this literal is true by adding assumptions */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  public:

  void preRegisterTerm(TNode n);
  void propagate(Effort e);
  Node explain(TNode n);

  /////////////////////////////////////////////////////////////////////////////
  // SHARING
  /////////////////////////////////////////////////////////////////////////////

  private:
  public:

  void addSharedTerm(TNode t);
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void computeCareGraph(CareGraph& careGraph);
  bool isShared(TNode t)
    { return (d_sharedArrays.find(t) != d_sharedArrays.end()); }


  /////////////////////////////////////////////////////////////////////////////
  // MODEL GENERATION
  /////////////////////////////////////////////////////////////////////////////

  private:
  public:

  Node getValue(TNode n);

  /////////////////////////////////////////////////////////////////////////////
  // NOTIFICATIONS
  /////////////////////////////////////////////////////////////////////////////

  private:

  context::CDO<bool> d_donePreregister;

  public:

  void presolve();
  void shutdown() { }

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER
  /////////////////////////////////////////////////////////////////////////////

  public:

  void check(Effort e);

  private:

  // NotifyClass: template helper class for d_equalityEngine - handles call-back from congruence closure module
  class NotifyClass {
    TheoryArrays& d_arrays;
  public:
    NotifyClass(TheoryArrays& uf): d_arrays(uf) {}

    bool notify(TNode propagation) {
      Debug("arrays") << spaces(d_arrays.getContext()->getLevel()) << "NotifyClass::notify(" << propagation << ")" << std::endl;
      // Just forward to arrays
      return d_arrays.propagate(propagation);
    }

    void notify(TNode t1, TNode t2) {
      Debug("arrays") << spaces(d_arrays.getContext()->getLevel()) << "NotifyClass::notify(" << t1 << ", " << t2 << ")" << std::endl;
      if (t1.getType().isArray()) {
        d_arrays.addToNotifyQueue(t1.eqNode(t2));
        if (!d_arrays.isShared(t1) || !d_arrays.isShared(t2)) {
          return;
        }
      }
      // Propagate equality between shared terms
      Node equality = Rewriter::rewriteEquality(theory::THEORY_ARRAY, t1.eqNode(t2));
      d_arrays.propagate(equality);
    }
  };


  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** Equaltity engine */
  uf::EqualityEngine<NotifyClass> d_equalityEngine;

  // Are we in conflict?
  context::CDO<bool> d_conflict;

  // Does the conflict still need to be explained?
  context::CDO<bool> d_explain;

  /** The conflict node */
  Node d_conflictNode;

  /**
   * Context dependent map from a congruence class canonical representative of
   * type array to an Info pointer that keeps track of information useful to axiom
   * instantiation
   */

  Backtracker<TNode> d_backtracker;
  ArrayInfo d_infoMap;

  typedef quad<TNode, TNode, TNode, TNode> RowLemmaType;

  //TODO: These should be CD
  std::hash_set<RowLemmaType, RowLemmaTypeHashFunction > d_RowQueue;
  std::hash_set<RowLemmaType, RowLemmaTypeHashFunction > d_RowAlreadyAdded;

  context::CDHashMap<TNode, bool, TNodeHashFunction> d_sharedArrays;
  std::hash_map<TNode, Node, TNodeHashFunction> d_diseqCache;

  // List of nodes that need permanent references in this context
  context::CDList<Node> d_permRef;

  Node mkAnd(std::vector<TNode>& conjunctions);
  void mergeArrays(TNode a, TNode b);
  void checkStore(TNode a);
  void checkRowForIndex(TNode i, TNode a);
  void checkRowLemmas(TNode a, TNode b);
  void queueRowLemma(RowLemmaType lem);
  void dischargeLemmas();


  context::CDQueue<Node> d_notifyQueue;

  void addToNotifyQueue(TNode n);

};/* class TheoryArrays */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H */

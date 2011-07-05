/*********************                                                        */
/*! \file congruence_closure.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The congruence closure module
 **
 ** The congruence closure module.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTIL__CONGRUENCE_CLOSURE_H
#define __CVC4__UTIL__CONGRUENCE_CLOSURE_H

#include <sstream>
#include <list>
#include <iterator>

#include <ext/hash_map>

#include "expr/node_manager.h"
#include "expr/node.h"
#include "expr/kind_map.h"
#include "context/context_mm.h"
#include "context/cdo.h"
#include "context/cdmap.h"
#include "context/cdset.h"
#include "context/cdlist.h"
#include "context/cdlist_context_memory.h"
#include "context/cdcirclist.h"
#include "context/stacking_vector.h"
#include "context/stacking_map.h"
#include "util/exception.h"
#include "util/stats.h"
#include "util/hash.h"
#include "util/dynamic_array.h"
#include "util/ntuple.h"

namespace CVC4 {

template <class OutputChannel>
class CongruenceClosure;

template <class OutputChannel>
std::ostream& operator<<(std::ostream& out,
                         const CongruenceClosure<OutputChannel>& cc);

/**
 * A CongruenceClosureException is thrown by
 * CongruenceClosure::explain() when that method is asked to explain a
 * congruence that doesn't exist.
 */
class CVC4_PUBLIC CongruenceClosureException : public Exception {
public:
  inline CongruenceClosureException(std::string msg) :
    Exception(std::string("Congruence closure exception: ") + msg) {}
  inline CongruenceClosureException(const char* msg) :
    Exception(std::string("Congruence closure exception: ") + msg) {}
};/* class CongruenceClosureException */

/**
 * Congruence closure module for CVC4.
 *
 * This is a service class for theories.  One uses a CongruenceClosure
 * by adding a number of relevant equality terms with registerEquality() and
 * asserted equalities with addEquality().  It then gets notified
 * (through OutputChannel, below), of new equality terms that are
 * implied by the current set of asserted (and implied) equalities.
 *
 * OutputChannel is a template argument (it's probably a thin layer,
 * and we want to avoid a virtual call hierarchy in this case, and
 * enable aggressive inlining).  It need only implement one method,
 * notifyCongruent():
 *
 *   class MyOutputChannel {
 *   public:
 *     bool notifyEntailedEquality(TNode eq) {
 *       // CongruenceClosure is notifying us that "a" is now the EC
 *       // representative for "b" in this context.  After a pop, "a"
 *       // will be its own representative again.  Note that "a" and
 *       // "b" might never have been added with registerEquality().  However,
 *       // something in their equivalence class was (for which a
 *       // previous notifyCongruent() would have notified you of
 *       // their EC representative, which is now "a" or "b").
 *       //
 *       // This call is made while the merge is being done.  If you
 *       // throw any exception here, you'll immediately exit the
 *       // CongruenceClosure call and will miss whatever pending
 *       // merges were being performed, leaving the CongruenceClosure
 *       // module in a bad state.  Therefore if you throw, you should
 *       // only do so if you are going to backjump, re-establishing a
 *       // good (former) state.  Keep this in mind if a
 *       // CVC4::Interrupted that *doesn't* lead to a backjump can
 *       // interrupt you.
 *     }
 *
 *     bool notifyDisentailedEquality(TNode eq) {
 *       // Similar, but "eq" must be false, given the set of
 *       // constraints
 *     }
 *
 *     bool notifyMerge(TNode a, TNode b) {
 *       // a (previously a representative of an equivalence class) is
 *       // now a member of b's equivalence class.  b is the
 *       // representative.
 *     }
 *   };
 */
template <class OutputChannel>
class CongruenceClosure {

  /**
   * A Cid is a "Congruence ID", and is a dense, integral
   * representation of a term.  Positive Cids are for individuals, and
   * negative Cids are for application-like things (technically: they
   * are non-nullary applications of operators we have been requested
   * to compute congruence over).
   */
  typedef uint32_t Cid;

  struct CidHashFunction {
    inline size_t operator()(Cid c) const { return c; }
  };/* struct CongruenceClosure<>::CidHashFunction */

  template <class T, class UnderlyingHashFunction = std::hash<T> >
  struct VectorHashFunction {
    inline size_t operator()(const std::vector<T>& v) const {
      UnderlyingHashFunction h;
      size_t hash = 0;
      typename std::vector<T>::const_iterator i = v.begin();
      typename std::vector<T>::const_iterator i_end = v.end();
      while(i != i_end) {
        hash ^= h(*i) + 0x9e3779b9 + (hash << 6) + (hash >> 2);
        ++i;
      }
      return hash;
    }
  };/* struct CongruenceClosure<>::VectorHashFunction<> */

  std::hash_map<TNode, Cid, TNodeHashFunction> d_cidMap;
  DynamicArray<Node> d_reverseCidMap;
  std::list< triple<Cid, Cid, Node> > d_pending;

  inline Cid cid(TNode n) {
    Cid& cid = d_cidMap[n];
    if(cid == 0) {
      cid = d_reverseCidMap.size();
      d_reverseCidMap.push_back(n);
      Debug("cc") << "new cid! " << cid << " for " << n << std::endl;

      //Assert(d_useLists[cid] == NULL);
      //d_useLists[cid] = new(true) UseList(d_context, context::ContextMemoryAllocator<Cid>(d_context->getCMM()));
      //Debug("cc") << "--allocate uselist for cid " << cid << " ==> " << d_useLists[cid] << std::endl;

      if(isCongruenceOperator(n)) {
        if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
          // make sure operator is cid-ified for lookup map
          this->cid(n.getOperator());
        }
      }

      // I would kinda like this to be in CMM, but then d_classLists[]
      // has to be context dependent (to switch back to NULL). :(
      ClassList* cl = new(true) ClassList(d_context, context::ContextMemoryAllocator<Cid>(d_context->getCMM()));
      cl->push_back(cid);
      Assert(d_classLists[cid] == NULL);
      d_classLists[cid] = cl;
    }
    return cid;
  }
  inline Cid cid(TNode n) const {
    std::hash_map<TNode, Cid, TNodeHashFunction>::const_iterator i = d_cidMap.find(n);
    Assert(i != d_cidMap.end());
    return (*i).second;
  }
  inline bool hasCid(TNode n) const {
    std::hash_map<TNode, Cid, TNodeHashFunction>::const_iterator i = d_cidMap.find(n);
    return i != d_cidMap.end();
  }
  inline TNode node(Cid cid) const {
    return d_reverseCidMap[cid];
  }

  inline bool isApplication(Cid cid) const {
    return isCongruenceOperator(node(cid));
  }

  /** The context at play. */
  context::Context* d_context;

  /** The output channel */
  OutputChannel* d_out;

  /**
   * The bitmap of Kinds over which we are computing congruence.  It
   * doesn't really make sense for this list of operators to change,
   * so we don't allow it to---plus, if it did change, we'd probably
   * have to recompute everything from scratch anyway.
   */
  const KindMap d_congruenceOperatorMap;

  // typedef all of these so that iterators are easy to define
  typedef context::StackingVector<Cid> RepresentativeMap;
  typedef context::CDCircList<Cid, context::ContextMemoryAllocator<Cid> > ClassList;
  typedef DynamicGrowingArray<ClassList*> ClassLists;
  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > UseList;
  typedef context::CDMap<TNode, UseList*, TNodeHashFunction> UseLists;
  typedef DynamicGrowingArray< std::vector<Node> > PropagateList;
  typedef context::CDMap<Node, Node, NodeHashFunction> LookupMap;

  typedef __gnu_cxx::hash_map<TNode, Node, TNodeHashFunction> EqMap;

  typedef context::CDMap<Node, Node, NodeHashFunction> ProofMap;
  typedef context::CDMap<Node, Node, NodeHashFunction> ProofLabel;

  // Simple, NON-context-dependent pending list, union find and "seen
  // set" types for constructing explanations and
  // nearestCommonAncestor(); see explain().
  typedef std::list<std::pair<Node, Node> > PendingProofList_t;
  typedef __gnu_cxx::hash_map<TNode, TNode, TNodeHashFunction> UnionFind_t;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> SeenSet_t;

  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> CareSet_t;

  RepresentativeMap d_representative;
  ClassLists d_classLists;
  PropagateList d_propagate;
  UseLists d_useList;
  LookupMap d_lookup;

  EqMap d_eqMap;
  context::CDSet<TNode, TNodeHashFunction> d_added;

  ProofMap d_proof;
  ProofLabel d_proofLabel;

  ProofMap d_proofRewrite;

  /**
   * The set of terms we care about (i.e. those that have been given
   * us with registerTerm() and their representatives).
   */
  CareSet_t d_careSet;

  // === STATISTICS ===
  AverageStat d_explanationLength;/**< average explanation length */
  IntStat d_newSkolemVars;/**< new vars created */

  inline std::vector<Node>& propagateList(Cid c) {
    return d_propagate[c];
  }

  inline const std::vector<Node>& propagateList(Cid c) const {
    return d_propagate[c];
  }

  inline ClassList& classList(Cid c) {
    return *d_classLists[c];
  }

  inline const ClassList& classList(Cid c) const {
    return *d_classLists[c];
  }

  inline bool isCongruenceOperator(TNode n) const {
    // For the datatypes theory, we've removed the invariant that
    // parameterized kinds must have at least one argument.  Consider
    // (CONSTRUCTOR nil) for instance.  So, n here can be an operator
    // that's normally checked for congruence (like CONSTRUCTOR) but
    // shouldn't be treated as a congruence operator if it only has an
    // operator and no children (like CONSTRUCTOR nil), since we can
    // treat that as a simple variable.
    return n.getNumChildren() > 0 && d_congruenceOperatorMap[n.getKind()];
  }

public:
  /** Construct a congruence closure module instance */
  CongruenceClosure(context::Context* ctxt, OutputChannel* out, KindMap kinds)
    throw(AssertionException) :
    d_cidMap(),
    d_reverseCidMap(false),
    d_context(ctxt),
    d_out(out),
    d_congruenceOperatorMap(kinds),
    d_representative(ctxt),
    d_classLists(),
    d_useList(ctxt),
    d_lookup(ctxt),
    d_added(ctxt),
    d_proof(ctxt),
    d_proofLabel(ctxt),
    d_proofRewrite(ctxt),
    d_careSet(),
    d_explanationLength("congruence_closure::AverageExplanationLength"),
    d_newSkolemVars("congruence_closure::NewSkolemVariables", 0) {
    CheckArgument(!kinds.isEmpty(), "cannot construct a CongruenceClosure with an empty KindMap");
    d_reverseCidMap.push_back(Node::null());
  }

  ~CongruenceClosure() {
    for(unsigned i = 0; i < d_classLists.size(); ++i) {
      if(d_classLists[i] != NULL) {
        ::delete d_classLists[i];
      }
    }
  }

  /**
   * Register a term (which should be a node of kind EQUAL or IFF) for
   * CC consideration, so that CC will push out a notification to its
   * output channel should the equality become implied by the current
   * state.  This set of terms is NOT context-dependent, and that's by
   * design: lemmas added at deep context levels can lead to new,
   * pre-registered terms which should still be considered for
   * propagation after that context is popped (since the lemmas, and
   * therefore their constituent terms, don't go away).
   *
   * This function calls OutputChannel::notifyCongruent() for the term
   * if the equality is already implied by the current partial
   * assignment, so it can throw anything that that function can.
   */
  void registerEquality(TNode eq);
  void registerTerm(TNode trm);

  /**
   * Add an equality literal eq into CC consideration (it should be a
   * node of kind EQUAL or IFF), asserting that this equality is now
   * true.  This assertion is context-dependent.  Calls
   * OutputChannel::notifyCongruent() to notify the client of any
   * equalities (registered using registerEquality()) that are now congruent.
   * Therefore, it can throw anything that that function can.
   *
   * Note that equalities asserted via assertEquality() need not have
   * been registered using registerEquality()---the values in those two sets
   * have no requirements---the two sets can be equal, disjoint,
   * overlapping, it doesn't matter.
   */
  void assertEquality(TNode inputEq) {
    if(Debug.isOn("cc")) {
      Debug("cc") << "CC assertEquality[" << d_context->getLevel() << "]: " << inputEq << std::endl;
    }
    Assert(inputEq.getKind() == kind::EQUAL ||
           inputEq.getKind() == kind::IFF);
    NodeBuilder<> eqb(inputEq.getKind());
    if(isCongruenceOperator(inputEq[1]) &&
       !isCongruenceOperator(inputEq[0])) {
      eqb << flatten(inputEq[1]) << inputEq[0];
    } else {
      eqb << flatten(inputEq[0]) << replace(flatten(inputEq[1]));
    }
    Node eq = eqb;
    merge(eq, inputEq);
  }

  void assertDisequality(TNode inputDiseq) {
    //Unimplemented();
  }

private:
  void merge(TNode eq, TNode inputEq);

  Node flatten(TNode t) {
    if(isCongruenceOperator(t)) {
      NodeBuilder<> appb(t.getKind());
      Assert(replace(flatten(t.getOperator())) == t.getOperator(),
             "CongruenceClosure:: bad state: higher-order term ??");
      if(t.getMetaKind() == kind::metakind::PARAMETERIZED) {
	appb << t.getOperator();
      }
      for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
        appb << replace(flatten(*i));
      }
      return Node(appb);
    } else {
      return t;
    }
  }

  Node replace(TNode t) {
    if(isCongruenceOperator(t)) {
      EqMap::iterator i = d_eqMap.find(t);
      if(i == d_eqMap.end()) {
        ++d_newSkolemVars;
        Node v = NodeManager::currentNM()->mkSkolem(t.getType());
        merge(NodeManager::currentNM()->mkNode(t.getType().isBoolean() ? kind::IFF : kind::EQUAL, t, v), TNode::null());
        d_added.insert(v);
        d_eqMap[t] = v;
        return v;
      } else {
        TNode v = (*i).second;
        if(!d_added.contains(v)) {
          merge(NodeManager::currentNM()->mkNode(t.getType().isBoolean() ? kind::IFF : kind::EQUAL, t, v), TNode::null());
          d_added.insert(v);
        }
        return v;
      }
    } else {
      return t;
    }
  }

  TNode proofRewrite(TNode pfStep) const {
    ProofMap::const_iterator i = d_proofRewrite.find(pfStep);
    if(i == d_proofRewrite.end()) {
      return pfStep;
    } else {
      return (*i).second;
    }
  }

public:
  /**
   * Inquire whether two expressions are congruent in the current
   * context.
   */
  inline bool areCongruent(TNode a, TNode b) const throw(AssertionException) {
    if(Debug.isOn("cc")) {
      Debug("cc") << "CC areCongruent? " << a << "  ==  " << b << std::endl;
      Debug("cc") << "  a  " << a << std::endl;
      Debug("cc") << "  a' " << normalize(a) << std::endl;
      Debug("cc") << "  b  " << b << std::endl;
      Debug("cc") << "  b' " << normalize(b) << std::endl;
    }

    Node ap = hasCid(a) ? node(find(cid(a))) : a;
    Node bp = hasCid(b) ? node(find(cid(b))) : b;

    // areCongruent() works fine as just find(a) == find(b) _except_
    // for terms not appearing in equalities.  For example, let's say
    // you have unary f and binary g, h, and
    //
    //   a == f(b) ; f(a) == b ; g == h
    //
    // it's clear that h(f(a),a) == g(b,a), but it's not in the
    // union-find even if you addTerm() on those two.
    //
    // we implement areCongruent() to handle more general
    // queries---i.e., to check for new congruences---but shortcut a
    // cheap & common case
    //
    return ap == bp || normalize(ap) == normalize(bp);
  }

private:
  /**
   * Find the EC representative for a term t in the current context.
   */
  inline Cid find(Cid c) const throw(AssertionException) {
    Cid p = d_representative[c];
    return p == 0 ? c : p;
  }

  void explainAlongPath(TNode a, TNode c, PendingProofList_t& pending, UnionFind_t& unionFind, std::list<Node>& pf)
    throw(AssertionException);

  Node highestNode(TNode a, UnionFind_t& unionFind) const
    throw(AssertionException);

  Node nearestCommonAncestor(TNode a, TNode b, UnionFind_t& unionFind)
    throw(AssertionException);

public:
  /**
   * Request an explanation for why a and b are in the same EC in the
   * current context.  Throws a CongruenceClosureException if they
   * aren't in the same EC.
   */
  Node explain(Node a, Node b)
    throw(CongruenceClosureException, AssertionException);

  /**
   * Request an explanation for why the lhs and rhs of this equality
   * are in the same EC.  Throws a CongruenceClosureException if they
   * aren't in the same EC.
   */
  inline Node explain(TNode eq)
    throw(CongruenceClosureException, AssertionException) {
    Assert(eq.getKind() == kind::EQUAL ||
           eq.getKind() == kind::IFF);
    return explain(eq[0], eq[1]);
  }

  /**
   * Normalization.
   */
  Node normalize(TNode t) const throw(AssertionException);

private:

  friend std::ostream& operator<< <>(std::ostream& out,
                                     const CongruenceClosure<OutputChannel>& cc);

  /**
   * Internal propagation of information.  Propagation tends to
   * cascade (this implementation uses an iterative "pending"
   * worklist), and "seed" is the "seeding" propagation to do (the
   * first one).  Calls OutputChannel::notifyCongruent() indirectly,
   * so it can throw anything that that function can.
   */
  void propagate(TNode seed);

  /**
   * Internal lookup mapping from tuples to equalities.
   */
  inline TNode lookup(TNode a) const {
    LookupMap::iterator i = d_lookup.find(a);
    if(i == d_lookup.end()) {
      return TNode::null();
    } else {
      TNode l = (*i).second;
      Assert(l.getKind() == kind::EQUAL ||
             l.getKind() == kind::IFF);
      return l;
    }
  }

  /**
   * Internal lookup mapping.
   */
  inline void setLookup(TNode a, TNode b) {
    Assert(a.getKind() == kind::TUPLE);
    Assert(b.getKind() == kind::EQUAL ||
           b.getKind() == kind::IFF);
    d_lookup[a] = b;
  }

  /**
   * Given an apply (f a1 a2...), build a TUPLE expression
   * (f', a1', a2', ...) suitable for a lookup() key.
   */
  Node buildRepresentativesOfApply(TNode apply, Kind kindToBuild = kind::TUPLE)
    throw(AssertionException);

  /**
   * Append equality "eq" to uselist of "of".
   */
  inline void appendToUseList(TNode of, TNode eq) {
    Trace("cc") << "adding " << eq << " to use list of " << of << std::endl;
    Assert(eq.getKind() == kind::EQUAL ||
           eq.getKind() == kind::IFF);
    Assert(of == node(find(cid(of))));
    UseLists::iterator usei = d_useList.find(of);
    UseList* ul;
    if(usei == d_useList.end()) {
      ul = new(d_context->getCMM()) UseList(true, d_context, false,
                                            context::ContextMemoryAllocator<TNode>(d_context->getCMM()));
      d_useList.insertDataFromContextMemory(of, ul);
    } else {
      ul = (*usei).second;
    }
    ul->push_back(eq);
  }

  /**
   * Merge equivalence class proofs.
   */
  void mergeProof(TNode a, TNode b, TNode e);

public:

  // === STATISTICS ACCESSORS ===

  /**
   * Get access to the explanation-length statistic.  Returns the
   * statistic itself so that reference-statistics can be wrapped
   * around it, useful since CongruenceClosure is a client class and
   * shouldn't be directly registered with the StatisticsRegistry.
   */
  const AverageStat& getExplanationLength() const throw() {
    return d_explanationLength;
  }

  /**
   * Get access to the new-skolem-vars statistic.  Returns the
   * statistic itself so that reference-statistics can be wrapped
   * around it, useful since CongruenceClosure is a client class and
   * shouldn't be directly registered with the StatisticsRegistry.
   */
  const IntStat& getNewSkolemVars() const throw() {
    return d_newSkolemVars;
  }

};/* class CongruenceClosure */

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::registerEquality(TNode eq) {
  Assert(eq.getKind() == kind::IFF || eq.getKind() == kind::EQUAL);

  Trace("cc") << "CC registerEquality: " << eq << std::endl;

  Node l = replace(flatten(eq[0]));
  Node r = replace(flatten(eq[1]));

  Cid cl = cid(l), cr = cid(r);

  if(areCongruent(l, r)) {
    // we take care to only notify our client once of congruences
    d_out->notifyEntailedEquality(eq);// intentionally ignore cancelation request here
  }

  propagateList(cl).push_back(eq);
  propagateList(cr).push_back(eq);
}

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::registerTerm(TNode t) {
  Node trm = replace(flatten(t));
  Node trmp = node(find(cid(trm)));

  if(Debug.isOn("cc")) {
    Debug("cc") << "CC addTerm [" << d_careSet.size() << "] " << !(d_careSet.find(t) == d_careSet.end()) << ": " << t << std::endl
                << "           [" << d_careSet.size() << "] " << !(d_careSet.find(trm) == d_careSet.end()) << ": " << trm << std::endl
                << "           [" << d_careSet.size() << "] " << !(d_careSet.find(trmp) == d_careSet.end()) << ": " << trmp << std::endl;
  }

  if(t != trm && d_careSet.find(t) == d_careSet.end()) {
    // we take care to only notify our client once of congruences
    d_out->notifyMerge(t, trm);
    d_careSet.insert(t);
  }

  if(d_careSet.find(trm) == d_careSet.end()) {
    if(trm != trmp) {
      // if part of an equivalence class headed by another node,
      // notify the client of this merge that's already been
      // performed..
      d_out->notifyMerge(trm, trmp);
    }

    // add its representative to the care set
    d_careSet.insert(trmp);
  }
}

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__CONGRUENCE_CLOSURE_H */

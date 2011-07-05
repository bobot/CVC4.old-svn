/*********************                                                        */
/*! \file congruence_closure.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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
#include "context/cdcirclist.h"
#include "context/stacking_vector.h"
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

      Assert(d_useLists[cid] == NULL);
      d_useLists[cid] = new(true) UseList(d_context, context::ContextMemoryAllocator<Cid>(d_context->getCMM()));
      Debug("cc") << "--allocate uselist for cid " << cid << " ==> " << d_useLists[cid] << std::endl;

      if(isCongruenceOperator(n)) {
        if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
          // make sure operator is cid-ified for lookup map
          this->cid(n.getOperator());
        }
        /*
        for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
          Trace("cc") << "adding " << n << "(" << cid << ") to use list of " << *i << "(" << this->cid(*i) << ")" << std::endl;
          Cid ic = this->cid(*i);
          Debug("cc") << " == under-cid ic " << ic << " uselist is " << d_useLists[ic] << std::endl;
          useList(ic).push_back(cid);
          if(d_context->getLevel() > 0) {
            installUseListAdditionHook(ic, cid);
          }
        }
        */
        /*
        Node rewritten = rewriteWithRepresentatives(n);
        Trace("cc") << "rewrote " << n << " to " << rewritten << std::endl;
        if(n != rewritten) {
          Node eq = NodeManager::currentNM()->mkNode(kind::TUPLE, n, rewritten);
          d_pending.push_back(make_triple(cid, this->cid(rewritten), eq));
        }
        */
      }

      // I would kinda like this to be in CMM, but then d_classLists[]
      // has to be context dependent (to switch back to NULL). :(
      ClassList* cl = new(true) ClassList(d_context, context::ContextMemoryAllocator<Cid>(d_context->getCMM()));
      cl->push_back(cid);
      Assert(d_classLists[cid] == NULL);
      d_classLists[cid] = cl;
      /*
      if(Debug.isOn("cc:detail")) {
        debug();
      }
      */
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

  /**
   * The output channel, used for notifying the client of new
   * congruences.  Only terms registered with registerEquality() will
   * generate notifications.
   */
  OutputChannel* d_out;

  /**
   * The bitmap of Kinds over which we are computing congruence.  It
   * doesn't really make sense for this list of operators to change,
   * so we don't allow it to---plus, if it did change, we'd probably
   * have to recompute everything from scratch anyway.
   */
  const KindMap d_congruenceOperatorMap;

  // typedef all of these so that iterators are easy to define, and so
  // experiments can be run easily with different data structures
  typedef context::StackingVector<Cid> RepresentativeMap;
  typedef context::CDCircList<Cid, context::ContextMemoryAllocator<Cid> > ClassList;
  typedef DynamicGrowingArray<ClassList*> ClassLists;
  typedef context::CDCircList<std::pair<Node, Node>, context::ContextMemoryAllocator<std::pair<Node, Node> > > UseList;
  typedef DynamicGrowingArray<UseList*> UseLists;
  typedef DynamicGrowingArray< std::vector<Node> > PropagateList;
  typedef context::CDMap<std::vector<Cid>, std::pair<Node, Cid>, VectorHashFunction<Cid, CidHashFunction> > LookupMap;

  typedef context::StackingVector<Cid> ProofMap;
  typedef context::StackingVector<Node> ProofLabel;

  // Simple, NON-context-dependent pending list, union find and "seen
  // set" types for constructing explanations and
  // nearestCommonAncestor(); see explain().
  typedef std::list<std::pair<Cid, Cid> > PendingProofList_t;
  typedef __gnu_cxx::hash_map<Cid, Cid> UnionFind_t;
  typedef __gnu_cxx::hash_set<Cid> SeenSet_t;

  typedef __gnu_cxx::hash_set<Cid> CareSet_t;

  RepresentativeMap d_representative;
  ClassLists d_classLists;
  PropagateList d_propagate, d_dispropagate;
  UseLists d_useLists;
  LookupMap d_lookup;

  ProofMap d_proof;
  ProofLabel d_proofLabel;

  CareSet_t d_careTerms;

  // === STATISTICS ===
  AverageStat d_explanationLength;/**< average explanation length */

  inline std::vector<Node>& propagateList(Cid c) {
    return d_propagate[c];
  }

  inline const std::vector<Node>& propagateList(Cid c) const {
    return d_propagate[c];
  }

  inline std::vector<Node>& dispropagateList(Cid c) {
    return d_dispropagate[c];
  }

  inline const std::vector<Node>& dispropagateList(Cid c) const {
    return d_dispropagate[c];
  }

  inline ClassList& classList(Cid c) {
    return *d_classLists[c];
  }

  inline const ClassList& classList(Cid c) const {
    return *d_classLists[c];
  }

  inline UseList& useList(Cid c) {
    return *d_useLists[c];
  }

  inline const UseList& useList(Cid c) const {
    return *d_useLists[c];
  }

  inline void concatUseLists(Cid a, Cid b) {
    useList(a).concat(useList(b));
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
    d_propagate(true),
    d_dispropagate(true),
    d_useLists(true),
    d_lookup(ctxt),
    d_proof(ctxt),
    d_proofLabel(ctxt),
    //d_proofRewrite(ctxt),
    d_explanationLength("congruence_closure::AverageExplanationLength") {
    CheckArgument(!kinds.isEmpty(), "cannot construct a CongruenceClosure with an empty KindMap");
    d_reverseCidMap.push_back(Node::null());
  }

  ~CongruenceClosure() {
    for(unsigned i = 0; i < d_classLists.size(); ++i) {
      if(d_classLists[i] != NULL) {
        ::delete d_classLists[i];
      }
    }
    for(unsigned i = 0; i < d_useLists.size(); ++i) {
      if(d_useLists[i] != NULL) {
        ::delete d_useLists[i];
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
    Debug("cc") << "CC assertEquality[" << d_context->getLevel() << "]: "
                << inputEq << std::endl;
    AssertArgument(inputEq.getKind() == kind::EQUAL ||
                   inputEq.getKind() == kind::IFF, inputEq);

    if(isCongruenceOperator(inputEq[0])) {
      merge(inputEq[0], cid(inputEq[1]), inputEq);
    } else if(isCongruenceOperator(inputEq[1])) {
      merge(inputEq[1], cid(inputEq[0]), inputEq);
    } else {
      merge(cid(inputEq[0]), cid(inputEq[1]), inputEq);
    }
  }

  void assertDisequality(TNode inputDiseq) {
    Debug("cc") << "CC assertDisequality[" << d_context->getLevel() << "]: "
                << inputDiseq << std::endl;
    AssertArgument(inputDiseq.getKind() == kind::EQUAL ||
                   inputDiseq.getKind() == kind::IFF, inputDiseq);
    Assert(!areCongruent(inputDiseq[0], inputDiseq[1]));

    TNode l = inputDiseq[0], r = inputDiseq[1];
    Cid s = cid(l), t = cid(r);
    dispropagateList(s).push_back(r);
    dispropagateList(t).push_back(l);
  }

private:
  void merge(Cid a, Cid b, TNode inputEq);
  void merge(TNode a, Cid b, TNode inputEq);

public:
  /**
   * Inquire whether two expressions are congruent in the current
   * context.
   */
  bool areCongruent(TNode a, TNode b) throw(AssertionException);

  // FIXME probably this isn't sufficient as a canonizer
  Node normalize(TNode n) const;

private:
  /**
   * Find the EC representative for a term t in the current context.
   */
  inline Cid find(Cid c) const throw(AssertionException) {
    Cid p = d_representative[c];
    return p == 0 ? c : p;
  }

  void debugProof(const std::list<Node>& pf, TNode a, TNode b) const throw(AssertionException);

  void explainAlongPath(Cid a, Cid c, PendingProofList_t& pending, UnionFind_t& unionFind, std::list<Node>& pf)
    throw(AssertionException);

  Cid highestNode(Cid a, UnionFind_t& unionFind) const
    throw(AssertionException);

  Cid nearestCommonAncestor(Cid a, Cid b, UnionFind_t& unionFind)
    throw(AssertionException);

  Node rewriteWithRepresentatives(TNode in) const {
    NodeBuilder<> nb(in.getKind());
    if(in.getMetaKind() == kind::metakind::PARAMETERIZED) {
      nb << in.getOperator();
    }
    for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
      if(hasCid(*i)) {
        nb << normalize(*i);
      } else {
        nb << *i;
      }
    }

    return Node(nb);
  }

public:

  /*
  void debug() const {
    if(Debug.isOn("cc:detail") && d_reverseCidMap.size() > 152) {
      Cid i = find(152);
      Debug("cc:detail") << "parent of 152 (" << node(152) << ") is " << i << " (" << node(i) << ")" << std::endl;
      typename ClassList::const_iterator it = classList(152).begin();
      if(it != classList(152).end()) {
        Debug("cc:detail") << "[" << d_context->getLevel() << "] cl of 152 is " << node(*it);
        if(++it == classList(152).end()) {
          Debug("cc:detail") << "xxx" << std::endl;
        } else {
          Debug("cc:detail") << " and " << node(*it) << ")" << std::endl;
        }
        Debug("cc:detail") << "  " << node(i) << " =>" << std::endl;
        const ClassList& cl = classList(i);
        for(typename ClassList::const_iterator j = cl.begin(); j != cl.end(); ++j) {
          Debug("cc:detail") << "      " << node(*j) << " ==> " << node(find(*j)) << std::endl;
        }
        cl.debugCheck();
      } else {
        Debug("cc:detail") << "[" << d_context->getLevel() << "] cl of 152 is EMPTY" << std::endl;
      }
    }
  }
  */

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
    AssertArgument(eq.getKind() == kind::EQUAL ||
                   eq.getKind() == kind::IFF, eq);
    return explain(eq[0], eq[1]);
  }

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
  void propagate();

  /**
   * Internal lookup mapping from tuples to equalities.
   */
  inline Cid lookup(const std::vector<Cid>& a) const {
    typename LookupMap::const_iterator i = d_lookup.find(a);
    if(i == d_lookup.end()) {
      return 0;
    } else {
      return (*i).second.second;
    }
  }

  Cid lookup(Cid a) const {
    Assert(isApplication(a));
    TNode n = node(a);
    std::vector<Cid> v;
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      v.push_back(/*find(*/cid(n.getOperator())/*)*/);
    }
    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      v.push_back(find(cid(*i)));
    }
    return lookup(v);
  }

  /**
   * Internal lookup mapping from tuples to equalities.
   */
  inline TNode lookupReason(const std::vector<Cid>& a) const {
    typename LookupMap::const_iterator i = d_lookup.find(a);
    if(i == d_lookup.end()) {
      return TNode::null();
    } else {
      return (*i).second.first;
    }
  }

  TNode lookupReason(Cid a) const {
    Assert(isApplication(a));
    TNode n = node(a);
    std::vector<Cid> v;
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      v.push_back(/*find(*/cid(n.getOperator())/*)*/);
    }
    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      v.push_back(find(cid(*i)));
    }
    return lookupReason(v);
  }

  /**
   * Internal lookup mapping.
   */
  void setLookup(const std::vector<Cid>& a, TNode b, Cid c);

  void setLookup(Cid a, TNode b, Cid c) {
    Assert(isApplication(a));
    TNode n = node(a);
    std::vector<Cid> v;
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      v.push_back(/*find(*/cid(n.getOperator())/*)*/);
    }
    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      v.push_back(find(cid(*i)));
    }
    setLookup(v, b, c);
  }

  // When we have the special transitivity reasons in CC, we have
  // something of the form u = v /\ v = w /\ w = x /\ x = y /\ y = z,
  // so it's simple to return the pair (u,z) here, since we can just
  // scan the conjunction once, from left to right.  This is only
  // complicated by the fact that we can group conjunctions together
  // (i.e., it's not necessarily a flat conjunction), and each
  // equality can be oriented in either direction.
  std::pair<TNode, TNode> whatIsProvenWithTransitivity(TNode n) const {
    if(n.getKind() == kind::IFF || n.getKind() == kind::EQUAL) {
      return std::make_pair(n[0], n[1]);
    }

    Assert(n.getKind() == kind::AND);
    TNode::iterator ni = n.begin();
    Debug("cc-wip") << "CC whatIsProvenWithTransitivity: looking at " << *ni << std::endl;
    std::pair<TNode, TNode> pr = whatIsProvenWithTransitivity(*ni);
    Assert(pr.first != pr.second);
    while(++ni != n.end()) {
      Debug("cc-wip") << "CC whatIsProvenWithTransitivity: already have that " << pr.first << " == " << pr.second << std::endl;
      Debug("cc-wip") << "CC whatIsProvenWithTransitivity: looking at " << *ni << std::endl;
      std::pair<TNode, TNode> pr2 = whatIsProvenWithTransitivity(*ni);
      if(pr.first == pr2.first) {
        pr.first = pr2.second;
      } else if(pr.first == pr2.second) {
        pr.first = pr2.first;
      } else if(pr.second == pr2.first) {
        pr.second = pr2.second;
      } else {
        Assert(pr.second == pr2.second);
        pr.second = pr2.first;
      }
      // transitivity shouldn't ever reduce to reflexivity
      Assert(pr.first != pr.second);
    }
    Debug("cc-wip") << "CC whatIsProvenWithTransitivity: final result is that " << pr.first << " == " << pr.second << std::endl;
    return pr;
  }

  void mergeProof(Cid a, Cid b, TNode e);

  void breakLookupCycle(Cid ind, Cid app, TNode inputEq);

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

};/* class CongruenceClosure */

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::registerEquality(TNode t) {
  AssertArgument(t.getKind() == kind::EQUAL || t.getKind() == kind::IFF,
                 t, "expected an EQUAL or IFF, got: %s", t.toString().c_str());
  TNode a = t[0];
  TNode b = t[1];

  Debug("cc") << "CC registerEquality " << t << std::endl;

  Cid ca = cid(a), cb = cid(b);

  if(areCongruent(a, b)) {
    // we take care to only notify our client once of congruences
    d_out->notifyEntailedEquality(t);// intentionally ignore cancelation request here
  }

  propagateList(ca).push_back(t);
  propagateList(cb).push_back(t);
}

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::registerTerm(TNode t) {
  AssertArgument(t.getKind() != kind::EQUAL && t.getKind() != kind::IFF,
                 t, "expected something other than EQUAL or IFF, got: %s", t.toString().c_str());
  Debug("cc") << "CC registerTerm " << t << std::endl;

  Cid c = cid(t);
  Cid p = find(c);

  if(c != p) {
    d_out->notifyMerge(t, node(p));
    d_careTerms.insert(p);
  } else {
    d_careTerms.insert(c);
  }
}

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__CONGRUENCE_CLOSURE_H */

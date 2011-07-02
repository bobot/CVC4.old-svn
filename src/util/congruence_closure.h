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
      if(isCongruenceOperator(n)) {
        for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
          Trace("cc") << "adding " << n << "(" << cid << ") to use list of " << *i << "(" << this->cid(*i) << ")" << std::endl;
          useList(this->cid(*i)).push_back(cid);
        }
        Node rewritten = rewriteWithRepresentatives(n);
        Trace("cc") << "rewrote " << n << " to " << rewritten << std::endl;
        if(n != rewritten) {
          Node eq = NodeManager::currentNM()->mkNode(kind::TUPLE, n, rewritten);
          d_pending.push_back(make_triple(cid, this->cid(rewritten), eq));
        }
      }

      // I would kinda like this to be in CMM, but then d_classLists[]
      // has to be context dependent (to switch back to NULL). :(
      ClassList* cl = new(true) ClassList(d_context, context::ContextMemoryAllocator<Cid>(d_context->getCMM()));
      cl->push_back(cid);
      d_classLists[cid] = cl;
      if(Debug.isOn("cc:detail")) {
        debug();
      }
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
  typedef std::vector<Cid> UseList;
  typedef DynamicGrowingArray<UseList> UseLists;
  typedef DynamicGrowingArray< std::vector<Node> > PropagateList;
  //typedef context::CDMap<std::vector<Cid>, Node, VectorHashFunction<Cid, CidHashFunction> > LookupMap;

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
  //LookupMap d_lookup;

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
    return d_useLists[c];
  }

  inline const UseList& useList(Cid c) const {
    return d_useLists[c];
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
    d_useLists(true),
    //d_lookup(ctxt),
    d_proof(ctxt),
    d_proofLabel(ctxt),
    //d_proofRewrite(ctxt),
    d_explanationLength("congruence_closure::AverageExplanationLength") {
    CheckArgument(!kinds.isEmpty(), "cannot construct a CongruenceClosure with an empty KindMap");
    d_reverseCidMap.push_back(Node::null());
  }

  ~CongruenceClosure() {}

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

    merge(cid(inputEq[0]), cid(inputEq[1]), inputEq);
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

    propagate();
  }

private:
  void merge(Cid a, Cid b, TNode inputEq);

public:
  /**
   * Inquire whether two expressions are congruent in the current
   * context.
   */
  inline bool areCongruent(TNode a, TNode b) throw(AssertionException) {
    Assert(hasCid(a));
    Assert(hasCid(b));

    if(Debug.isOn("cc:ac")) {
      Debug("cc:ac") << "CC areCongruent? " << a << "  ==  " << b << std::endl;
      Debug("cc:ac") << "  a   " << a << std::endl;
      Debug("cc:ac") << "  a'  " << node(find(cid(a))) << std::endl;
      Debug("cc:ac") << "  b   " << b << std::endl;
      Debug("cc:ac") << "  b'  " << node(find(cid(b))) << std::endl;
    }

    Cid ap = find(cid(a)), bp = find(cid(b));

    return ap == bp;
  }

  // FIXME probably this isn't sufficient as a canonizer
  inline Node normalize(TNode n) const {
    if(hasCid(n)) {
      return node(find(cid(n)));
    } else {
      return rewriteWithRepresentatives(n);
    }
  }

private:
  /**
   * Find the EC representative for a term t in the current context.
   */
  inline Cid find(Cid c) const throw(AssertionException) {
    Cid p = d_representative[c];
    return p == 0 ? c : p;
  }

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
        nb << node(find(cid(*i)));
      } else {
        nb << *i;
      }
    }

    return Node(nb);
  }

public:

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
  /*
  inline TNode lookup(const std::vector<Cid>& a) const {
    typename LookupMap::const_iterator i = d_lookup.find(a);
    if(i == d_lookup.end()) {
      return TNode::null();
    } else {
      TNode l = (*i).second;
      Assert(l.getKind() == kind::EQUAL ||
             l.getKind() == kind::IFF);
      return l;
    }
  }
  */

  /**
   * Internal lookup mapping.
   */
  /*
  inline void setLookup(const std::vector<Cid>& a, TNode b) {
    Assert(b.getKind() == kind::EQUAL ||
           b.getKind() == kind::IFF);
    d_lookup[a] = b;
  }
  */

  void mergeProof(Cid a, Cid b, TNode e);

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

  propagate();
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

/* From [Nieuwenhuis & Oliveras]
1. Procedure Merge(s=t)
2.   If s and t are constants a and b Then
3.     add a=b to Pending
4.     Propagate()
5.   Else ** s=t is of the form f(a1, a2)=a **
6.     If Lookup(a1', a2') is some f(b1, b2)=b Then
7.       add ( f(a1, a2)=a, f(b1, b2)=b ) to Pending
8.       Propagate()
9.     Else
10.      set Lookup(a1', a2') to f(a1, a2)=a
11.      add f(a1, a2)=a to UseList(a1') and to UseList(a2')
*/

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::merge(Cid s, Cid t, TNode inputEq) {

  Trace("cc") << "CC merge[" << d_context->getLevel() << "]: " << inputEq << std::endl;

  Assert(inputEq.getKind() == kind::EQUAL || inputEq.getKind() == kind::IFF);

  if(find(s) == find(t)) {
    // redundant
    return;
  }

  d_pending.push_back(make_triple(s, t, Node(inputEq)));

  propagate();

}/* merge() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::propagate() {
  Debug("cc:detail") << *this;

  while(!d_pending.empty()) {
    bool cancel = false;

    triple<Cid, Cid, Node> tr = d_pending.front();
    d_pending.pop_front();

    Cid s = tr.first;
    Cid t = tr.second;
    Node e = tr.third;

    Trace("cc") << "=== top of propagate loop ===" << std::endl
                << "=== e is " << s << " == " << t << " ===" << std::endl
                << "=== e is " << node(s) << " == " << node(t) << " ===" << std::endl
                << "=== eq is " << e << " ===" << std::endl;

    if(Trace.isOn("cc:detail")) {
      Trace("cc:detail") << "=====at start=====" << std::endl
                         << "a          :" << node(s) << std::endl
                         << "b          :" << node(t) << std::endl
                         << "alreadyCongruent?:" << areCongruent(node(s), node(t)) << std::endl;
    }
    if(Debug.isOn("cc:detail")) {
      debug();
    }

    Cid ap = find(s), bp = find(t);
    if(ap != bp) {

      Trace("cc:detail") << "EC[a] == " << node(ap) << std::endl
                         << "EC[b] == " << node(bp) << std::endl;

      // prop list

      Trace("cc:detail") << "going through propagation list of " << node(bp) << std::endl;
      ClassList& cl = classList(bp);

      if(cl.empty()) {
        // An empty class list means it's the single-entry class list
        // containing the thing itself.  So we patch it up, here.
        //
        // This can happen since we lazily create the single-entry
        // class listss, but they're context-dependent: once we pop
        // above that level, the list is cleared out.
        cl.push_back(bp);
        Trace("cc:detail") << "bp was nullified, fixed" << std::endl;
      }

      for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
        Trace("cc:detail") << "==> at node " << node(*cli) << " in class list of " << node(bp) << std::endl;
        Assert(find(*cli) == bp);
        std::vector<Node>& plist = propagateList(*cli);
        for(std::vector<Node>::iterator i = plist.begin(); i != plist.end(); ++i) {
          Assert((*i).getKind() == kind::EQUAL || (*i).getKind() == kind::IFF);
          Trace("cc:detail") << "    ==> considering " << *i << std::endl;
          Cid c = find(cid((*i)[0]));
          if(c == ap) {
            // the *i != e is so that we don't notify the user of
            // something they notified US of.
            if(find(cid((*i)[1])) == bp && *i != e) {
              Trace("cc:detail") << "        HIT!! ECs are " << node(ap) << " and " << node(bp) << std::endl;
              if(d_out->notifyEntailedEquality(*i)) {
                Trace("cc:detail") << "        in conflict, will CANCEL further propagation" << std::endl;
                cancel = true;
                d_pending.clear();
                goto reps;
              }
            }
          } else if(c == bp && find(cid((*i)[1])) == ap && *i != e) {
            Trace("cc:detail") << "        HIT!! ECs are " << node(bp) << " and " << node(ap) << std::endl;
            if(d_out->notifyEntailedEquality(*i)) {
              Trace("cc:detail") << "        in conflict, CANCELING further propagation" << std::endl;
              cancel = true;
              d_pending.clear();
              goto reps;
            }
          }
        }
      }

    reps:

      // rep mapping

      Trace("cc:detail") << "going through representatives of " << node(bp) << std::endl;

      for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
        Assert(find(*cli) == bp);
        d_representative.set(*cli, ap);
      }

      if(!cancel) {
        // use lists

        Trace("cc:detail") << "going through use list of " << node(bp) << std::endl;

        for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
          Assert(find(*cli) == ap);
          UseList& ul = useList(*cli);
          Trace("cc:detail") << "CC  -- useList: [" << node(*cli) << "(" << *cli << ":" << *cli << ")]: " << ul.size() << std::endl;
          for(UseList::const_iterator i = ul.begin(); i != ul.end(); ++i) {
            Trace("cc:detail") << "CC  -- useList: [" << node(*cli) << "(" << *cli << ")] " << node(*i) << "(" << *i << ")" << std::endl;

            TNode ni = node(*i);
            Node rewritten = rewriteWithRepresentatives(ni);
            if(ni != rewritten) {
              Node eq = NodeManager::currentNM()->mkNode(kind::TUPLE, ni, rewritten);

              Cid c = cid(rewritten);
              Trace("cc:detail") << "    -- rewritten to " << rewritten << "(" << c << ")" << std::endl;

              d_pending.push_back(make_triple(*i, c, eq));
            } else {
              Trace("cc:detail") << "    -- rewritten to self" << std::endl;
            }
          }
        }
        Trace("cc:detail") << "CC in prop done with useList of " << ap << std::endl;

        // finally, notify client if bp was cared about, and care about ap
        if(d_careTerms.find(bp) != d_careTerms.end()) {
          d_out->notifyMerge(node(bp), node(ap));
          d_careTerms.insert(ap);
        }
      }

      Assert(&classList(ap) != &classList(bp));
      if(Trace.isOn("cc:detail")) {
        {
          Trace("cc:detail") << "class list of " << node(ap) << " is:" << std::endl;
          ClassList& cl = classList(ap);
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }

        {
          Trace("cc:detail") << "class list of " << node(bp) << " is:" << std::endl;
          ClassList& cl = classList(bp);
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }
      }

      Debug("cc:detail") << "concat class lists of " << node(ap) << " and " << node(bp) << std::endl;
      // hack to get around the fact that lists empty themselves on
      // backtrack (but should always contain themselves)
      ClassList& clap = classList(ap);
      ClassList& clbp = classList(bp);
      if(clap.empty()) {
        clap.push_back(ap);
        Trace("cc:detail") << "ap was nullified, fixed" << std::endl;
      }
      Assert(!clbp.empty()); // should have been fixed above
      clap.concat(clbp);
      mergeProof(s, t, e);

      if(Trace.isOn("cc:detail")) {
        Trace("cc:detail") << "post-concat:::" << std::endl;
        {
          Trace("cc:detail") << "class list of " << node(ap) << " is:" << std::endl;
          ClassList& cl = classList(ap);
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }
      }

    } else {
      Trace("cc:detail") << "CCs the same ( == " << ap << "), do nothing." << std::endl;
    }

    if(Trace.isOn("cc:detail")) {
      Trace("cc:detail") << "=====at end=====" << std::endl
                         << "a          :" << node(s) << std::endl
                         << "a'         :" << node(find(s)) << std::endl
                         << "b          :" << node(t) << std::endl
                         << "b'         :" << node(find(t)) << std::endl
                         << "alreadyCongruent?:" << areCongruent(node(s), node(t)) << std::endl;
    }
    Assert(areCongruent(node(s), node(t)));
    if(Debug.isOn("cc:detail")) {
      debug();
    }
  }
}/* propagate() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::mergeProof(Cid a, Cid b, TNode e) {
  Trace("cc") << "  -- merge-proofing " << node(a) << "\n"
              << "                and " << node(b) << "\n"
              << "               with " << e << "\n";

  // proof forest gets a -> b labeled with e

  // first reverse all the edges in proof forest to root of this proof tree
  Trace("cc") << "CC PROOF reversing proof tree\n";
  // c and p are child and parent in (old) proof tree
  Cid c = a, p = d_proof[a];
  Node edgePf = d_proofLabel[a];
  // when we hit null p, we're at the (former) root
  Trace("cc") << "CC PROOF start at c == " << c << std::endl
              << "                  p == " << p << std::endl
              << "             edgePf == " << edgePf << std::endl;
  while(p != 0) {
    // in proof forest,
    // we have edge   c --edgePf-> p
    // turn it into   c <-edgePf-- p

    Cid pParSave = d_proof[p];
    Node pLabelSave = d_proofLabel[p];
    d_proof.set(p, c);
    d_proofLabel.set(p, edgePf);
    c = p;
    p = pParSave;
    edgePf = pLabelSave;
    Trace("cc") << "CC PROOF now   at c == " << c << std::endl
                << "                  p == " << p << std::endl
                << "             edgePf == " << edgePf << std::endl;
  }

  // add an edge from a to b
  d_proof.set(a, b);
  d_proofLabel.set(a, e);
}/* mergeProof() */


// This is the find() operation for the auxiliary union-find.  This
// union-find is not context-dependent, as it's used only during
// explain().  It does path compression.
template <class OutputChannel>
typename CongruenceClosure<OutputChannel>::Cid
CongruenceClosure<OutputChannel>::highestNode(Cid a, UnionFind_t& unionFind) const
  throw(AssertionException) {
  UnionFind_t::iterator i = unionFind.find(a);
  if(i == unionFind.end()) {
    return a;
  } else {
    return unionFind[a] = highestNode((*i).second, unionFind);
  }
}/* highestNode() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::explainAlongPath(Cid a, Cid c, PendingProofList_t& pending, UnionFind_t& unionFind, std::list<Node>& pf)
  throw(AssertionException) {

  a = highestNode(a, unionFind);
  Assert(c == highestNode(c, unionFind));

  while(a != c) {
    Cid b = d_proof[a];
    Node e = d_proofLabel[a];
    if(e.getKind() == kind::EQUAL ||
       e.getKind() == kind::IFF) {
      pf.push_back(e);
    } else {
      Assert(e.getKind() == kind::TUPLE);
      Assert(isCongruenceOperator(e[0]));
      Assert(isCongruenceOperator(e[1]));
      Assert(e[0].getNumChildren() == e[1].getNumChildren());
      Assert(e[0].getOperator() == e[1].getOperator(),
             "CongruenceClosure:: bad state: function symbols should be equal");
      for(int i = 0, nc = e[0].getNumChildren(); i < nc; ++i) {
        pending.push_back(std::make_pair(cid(e[0][i]), cid(e[1][i])));
      }
    }
    unionFind[a] = b;
    a = highestNode(b, unionFind);
  }
}/* explainAlongPath() */


template <class OutputChannel>
typename CongruenceClosure<OutputChannel>::Cid
CongruenceClosure<OutputChannel>::nearestCommonAncestor(Cid a, Cid b, UnionFind_t& unionFind)
  throw(AssertionException) {
  SeenSet_t seen;

  Assert(find(a) == find(b));

  do {
    a = highestNode(a, unionFind);
    seen.insert(a);
    a = d_proof[a];
  } while(a != 0);

  for(;;) {
    b = highestNode(b, unionFind);
    if(seen.find(b) != seen.end()) {
      return b;
    }
    b = d_proof[b];

    Assert(b != 0);
  }
}/* nearestCommonAncestor() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::explain(Node an, Node bn)
  throw(CongruenceClosureException, AssertionException) {

  Assert(an != bn);

  if(!areCongruent(an, bn)) {
    Debug("cc") << "explain: " << an << std::endl << " and   : " << bn << std::endl;
    throw CongruenceClosureException("asked to explain() congruence of nodes "
                                     "that aren't congruent");
  }

  Cid a = cid(an), b = cid(bn);

  PendingProofList_t pending;
  UnionFind_t unionFind;
  std::list<Node> terms;

  pending.push_back(std::make_pair(a, b));

  Trace("cc") << "CC EXPLAINING " << node(a) << " == " << node(b) << std::endl;

  do {// while(!pending.empty())
    std::pair<Cid, Cid> eq = pending.front();
    pending.pop_front();

    a = eq.first;
    b = eq.second;

    Cid c = nearestCommonAncestor(a, b, unionFind);

    explainAlongPath(a, c, pending, unionFind, terms);
    explainAlongPath(b, c, pending, unionFind, terms);
  } while(!pending.empty());

  if(Trace.isOn("cc")) {
    Trace("cc") << "CC EXPLAIN final proof has size " << terms.size() << std::endl;
  }

  NodeBuilder<> pf(kind::AND);
  while(!terms.empty()) {
    Node p = terms.front();
    terms.pop_front();
    Trace("cc") << "CC EXPLAIN " << p << std::endl;
    pf << p;
  }

  Trace("cc") << "CC EXPLAIN done" << std::endl;

  Assert(pf.getNumChildren() > 0);

  if(pf.getNumChildren() == 1) {
    d_explanationLength.addEntry(1.0);
    return pf[0];
  } else {
    d_explanationLength.addEntry(double(pf.getNumChildren()));
    return pf;
  }
}/* explain() */


template <class OutputChannel>
std::ostream& operator<<(std::ostream& out,
                         const CongruenceClosure<OutputChannel>& cc) {
  typedef typename CongruenceClosure<OutputChannel>::Cid Cid;

  if(Debug.isOn("cc:detail")) {
    cc.debug();
  }

  out << "==============================================" << std::endl;

  out << "Representatives:" << std::endl;
  for(Cid i = 1; i < cc.d_representative.size(); ++i) {
    typename CongruenceClosure<OutputChannel>::Cid p = cc.d_representative[i];
    if(p != 0) {
      out << "  " << cc.node(i) << " => " << cc.node(p) << std::endl;
    }
  }

  out << "ClassLists:" << std::endl;
  for(Cid i = 1; i < cc.d_reverseCidMap.size(); ++i) {
    if(cc.find(i) == i) {
      out << "  " << cc.node(i) << " =>" << std::endl;
      typedef typename CongruenceClosure<OutputChannel>::ClassList ClassList;
      const ClassList& cl = cc.classList(i);
      if(Debug.isOn("cc:detail")) {
        cl.debugCheck();
      }
      for(typename ClassList::const_iterator j = cl.begin(); j != cl.end(); ++j) {
        out << "      " << cc.node(*j) << std::endl;
      }
    }
  }

  out << "UseLists:" << std::endl;
  /*
  for(typename CongruenceClosure<OutputChannel>::UseLists::const_iterator i = cc.d_useList.begin(); i != cc.d_useList.end(); ++i) {
    if(cc.find((*i).first) == (*i).first) {
      out << "  " << (*i).first << " =>" << std::endl;
      for(typename CongruenceClosure<OutputChannel>::UseList::const_iterator j = (*i).second->begin(); j != (*i).second->end(); ++j) {
        out << "      " << *j << std::endl;
      }
    }
  }
  */

  out << "Care set:" << std::endl;
  for(Cid i = 1; i < cc.d_reverseCidMap.size(); ++i) {
    if(cc.d_careTerms.find(i) != cc.d_careTerms.end()) {
      out << "  " << cc.node(i) << std::endl;
    }
  }

  out << "==============================================" << std::endl;

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__CONGRUENCE_CLOSURE_H */

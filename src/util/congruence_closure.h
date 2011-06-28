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
#include "util/exception.h"
#include "theory/uf/morgan/stacking_map.h"
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
 * by adding a number of relevant equality terms with registerTerm() and
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
 *     void notifyCongruence(TNode eq) {
 *       // CongruenceClosure is notifying us that "a" is now the EC
 *       // representative for "b" in this context.  After a pop, "a"
 *       // will be its own representative again.  Note that "a" and
 *       // "b" might never have been added with registerTerm().  However,
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
  typedef int32_t Cid;

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
  DynamicArray<TNode> d_reverseCidMapIndividuals;
  DynamicArray<TNode> d_reverseCidMapApplications;
  std::list< triple<Cid, Cid, Node> > d_pending;

  inline Cid cid(TNode n) {
    Cid& cid = d_cidMap[n];
    if(cid == 0) {
      if(isCongruenceOperator(n)) {
        cid = -d_reverseCidMapApplications.size();
        d_reverseCidMapApplications.push_back(n);
        for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
          Trace("cc") << "adding " << n << "(" << cid << ") to use list of " << *i << "(" << this->cid(*i) << ":" << cidIndex(this->cid(*i)) << ")" << std::endl;
          useList(this->cid(*i)).push_back(cid);
        }
        Node rewritten = rewriteWithRepresentatives(n);
        if(n != rewritten) {
          Node eq = NodeManager::currentNM()->mkNode(kind::TUPLE, n, rewritten);
          d_pending.push_back(make_triple(cid, this->cid(rewritten), eq));
        }
      } else {
        cid = d_reverseCidMapIndividuals.size();
        d_reverseCidMapIndividuals.push_back(n);
      }

      ClassList* cl = new(d_context->getCMM()) ClassList(true, d_context, context::ContextMemoryAllocator<Cid>(d_context->getCMM()));
      cl->push_back(cid);
      d_classLists[cidIndex(cid)] = cl;
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
    return cid > 0 ?
      d_reverseCidMapIndividuals[cid] :
      d_reverseCidMapApplications[-cid];
  }
  static inline bool isApplication(Cid cid) {
    return cid < 0;
  }
  static inline bool isIndividual(Cid cid) {
    return cid > 0;
  }

  /** The context at play. */
  context::Context* d_context;

  /**
   * The output channel, used for notifying the client of new
   * congruences.  Only terms registered with registerTerm() will
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
  typedef context::CDMap<Cid, Cid> RepresentativeMap;
  typedef context::CDCircList<Cid, context::ContextMemoryAllocator<Cid> > ClassList;
  typedef DynamicGrowingArray<ClassList*> ClassLists;
  typedef std::vector<Cid> UseList;
  typedef DynamicGrowingArray<UseList> UseLists;
  typedef DynamicGrowingArray< std::vector<Node> > PropagateList;
  //typedef context::CDMap<std::vector<Cid>, Node, VectorHashFunction<Cid, CidHashFunction> > LookupMap;

# warning FIXME replace with stacking map for efficiency
  typedef context::CDMap<Cid, Cid> ProofMap;
  typedef context::CDMap<Cid, Node> ProofLabel;

  // Simple, NON-context-dependent pending list, union find and "seen
  // set" types for constructing explanations and
  // nearestCommonAncestor(); see explain().
  typedef std::list<std::pair<Cid, Cid> > PendingProofList_t;
  typedef __gnu_cxx::hash_map<Cid, Cid> UnionFind_t;
  typedef __gnu_cxx::hash_set<Cid> SeenSet_t;

  RepresentativeMap d_representative;
  ClassLists d_classLists;
  PropagateList d_propagate, d_dispropagate;
  UseLists d_useLists;
  //LookupMap d_lookup;

  ProofMap d_proof;
  ProofLabel d_proofLabel;

  //ProofMap d_proofRewrite;

  // === STATISTICS ===
  AverageStat d_explanationLength;/**< average explanation length */

  static inline Cid cidIndex(Cid c) {
    return c < 0 ? 2 * -c + 1 : 2 * c;
  }

  inline std::vector<Node>& propagateList(Cid c) {
    return d_propagate[cidIndex(c)];
  }

  inline std::vector<Node>& dispropagateList(Cid c) {
    return d_dispropagate[cidIndex(c)];
  }

  inline ClassList& classList(Cid c) {
    return *d_classLists[cidIndex(c)];
  }

  inline UseList& useList(Cid c) {
    return d_useLists[cidIndex(c)];
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
    d_reverseCidMapIndividuals(false),
    d_reverseCidMapApplications(false),
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
    d_reverseCidMapIndividuals.push_back(Node::null());
    d_reverseCidMapApplications.push_back(Node::null());
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
  void registerTerm(TNode eq);

  /**
   * Add an equality literal eq into CC consideration (it should be a
   * node of kind EQUAL or IFF), asserting that this equality is now
   * true.  This assertion is context-dependent.  Calls
   * OutputChannel::notifyCongruent() to notify the client of any
   * equalities (registered using registerTerm()) that are now congruent.
   * Therefore, it can throw anything that that function can.
   *
   * Note that equalities asserted via assertEquality() need not have
   * been registered using registerTerm()---the values in those two sets
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
  }

private:
  void merge(Cid a, Cid b, TNode inputEq);

  /*
  TNode proofRewrite(TNode pfStep) const {
    ProofMap::const_iterator i = d_proofRewrite.find(pfStep);
    if(i == d_proofRewrite.end()) {
      return pfStep;
    } else {
      return (*i).second;
    }
  }
  */

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
      Debug("cc:ac") << "  a'' " << normalize(a) << std::endl;
      Debug("cc:ac") << "  b   " << b << std::endl;
      Debug("cc:ac") << "  b'  " << node(find(cid(b))) << std::endl;
      Debug("cc:ac") << "  b'' " << normalize(b) << std::endl;
    }

    Cid ap = find(cid(a)), bp = find(cid(b));

    return ap == bp || normalize(ap) == normalize(bp);
  }

private:
  /**
   * Find the EC representative for a term t in the current context.
   */
  inline Cid find(Cid c) const throw(AssertionException) {
    RepresentativeMap::const_iterator it = d_representative.find(c);
    if(it == d_representative.end()) {
      return c;
    } else {
      return (*it).second;
    }
  }

  void explainAlongPath(Cid a, Cid c, PendingProofList_t& pending, UnionFind_t& unionFind, std::list<Node>& pf)
    throw(AssertionException);

  Cid highestNode(Cid a, UnionFind_t& unionFind) const
    throw(AssertionException);

  Cid nearestCommonAncestor(Cid a, Cid b, UnionFind_t& unionFind)
    throw(AssertionException);

  /**
   * Normalization.  Two terms are congruent iff they have the same
   * normal form.
   */
  Cid normalize(Cid c) const throw(AssertionException);

  Node rewriteWithRepresentatives(TNode in) {
    NodeBuilder<> nb(in.getKind());
    if(in.getMetaKind() == kind::metakind::PARAMETERIZED) {
      nb << in.getOperator();
    }
    for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
      nb << node(find(cid(*i)));
    }

    return Node(nb);
  }

public:

  Node normalize(TNode n) const throw(AssertionException) {
    return (d_cidMap.find(n) == d_cidMap.end()) ? n : node(normalize(cid(n)));
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

  /**
   * Merge equivalence class ec1 under ec2.  ec1's new union-find
   * representative becomes ec2.  Calls
   * OutputChannel::notifyCongruent(), so it can throw anything that
   * that function can.
   */
  //void ufmerge(TNode ec1, TNode ec2);
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
void CongruenceClosure<OutputChannel>::registerTerm(TNode t) {
  AssertArgument(t.getKind() == kind::EQUAL || t.getKind() == kind::IFF,
                 t, "expected an EQUAL or IFF, got: %s", t.toString().c_str());
  TNode a = t[0];
  TNode b = t[1];

  Debug("cc") << "CC registerTerm " << t << std::endl;

  Cid ca = cid(a), cb = cid(b);

  if(areCongruent(a, b)) {
    // we take care to only notify our client once of congruences
    d_out->notifyCongruence(t);
  }

  propagateList(ca).push_back(t);
  propagateList(cb).push_back(t);
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
  while(!d_pending.empty()) {
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
                         << "NORMALIZE a:" << normalize(node(s)) << std::endl
                         << "b          :" << node(t) << std::endl
                         << "NORMALIZE b:" << normalize(node(t)) << std::endl
                         << "alreadyCongruent?:" << areCongruent(node(s), node(t)) << std::endl;
    }

    Cid ap = find(s), bp = find(t);
    if(ap != bp) {

      Trace("cc:detail") << "EC[a] == " << node(ap) << std::endl
                         << "EC[b] == " << node(bp) << std::endl;

      { // propagation list
        Trace("cc:detail") << "going through propagation list of " << node(bp) << std::endl;
        ClassList& cl = classList(bp);

        for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
          Assert(find(*cli) == bp);
          std::vector<Node>& plist = propagateList(*cli);
          for(std::vector<Node>::iterator i = plist.begin(); i != plist.end(); ++i) {
            Assert((*i).getKind() == kind::EQUAL || (*i).getKind() == kind::IFF);
            Cid c = find(cid((*i)[0]));
            if(c == ap) {
              // the *i != e is so that we don't notify the user of
              // something they notified US of.
              if(find(cid((*i)[1])) == bp && *i != e) {
                d_out->notifyCongruence(*i);
              }
            } else if(c == bp && find(cid((*i)[1])) == ap && *i != e) {
              d_out->notifyCongruence(*i);
            }
          }
        }

        Trace("cc:detail") << "going through representatives of " << node(bp) << std::endl;

        for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
          Assert(find(*cli) == bp);
          d_representative[*cli] = ap;
        }

        Trace("cc:detail") << "going through use list of " << node(bp) << std::endl;

        for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
          Assert(find(*cli) == ap);
          UseList& ul = useList(*cli);
          Trace("cc:detail") << "CC  -- useList: [" << node(*cli) << "(" << *cli << ":" << cidIndex(*cli) << ")]: " << ul.size() << std::endl;
          for(UseList::const_iterator i = ul.begin(); i != ul.end(); ++i) {
            Trace("cc:detail") << "CC  -- useList: [" << node(*cli) << "(" << *cli << ")] " << node(*i) << "(" << *i << ")" << std::endl;

            TNode ni = node(*i);
            Node rewritten = rewriteWithRepresentatives(ni);
            if(ni != rewritten) {
              Node eq = NodeManager::currentNM()->mkNode(kind::TUPLE, ni, rewritten);

              Cid c = cid(rewritten);
              Trace("cc:detail") << "    -- rewritten to " << rewritten << "(" << c << ")" << std::endl;

#             warning FIXME don't use tuples, also make sure this doesn't blow up more than other approaches
              d_pending.push_back(make_triple(*i, c, eq));
            } else {
              Trace("cc:detail") << "    -- rewritten to self" << std::endl;
            }

#if 0

            for(int side = 0; side <= 1; ++side) {
              if(!isCongruenceOperator(eq[side])) {
                continue;
              }

              Node cp = buildRepresentativesOfApply(eq[side]);

              // if lookup(c1',c2') is some f(d1,d2)=d then
              TNode n = lookup(cp);

              Trace("cc:detail") << "CC     -- c' is " << cp << std::endl;

              if(!n.isNull()) {
                Trace("cc:detail") << "CC     -- lookup(c') is " << n << std::endl;
                // add (f(c1,c2)=c,f(d1,d2)=d) to pending
                Node tuple = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, n);
                Trace("cc") << "CC add tuple to pending: " << tuple << std::endl;
                pending.push_back(tuple);
                // remove f(c1,c2)=c from UseList(ap)
                Trace("cc:detail") << "supposed to remove " << eq << std::endl
                                   << "  from UseList of " << ap << std::endl;
                //i = ul.erase(i);// difference from paper: don't need to erase
              } else {
                Trace("cc") << "CC     -- lookup(c') is null" << std::endl;
                Trace("cc") << "CC     -- setlookup(c') to " << eq << std::endl;
                // set lookup(c1',c2') to f(c1,c2)=c
                setLookup(cp, eq);
                // move f(c1,c2)=c from UseList(ap) to UseList(b')
                //i = ul.erase(i);// difference from paper: don't need to erase

#               warning fixme
                appendToUseList(bp, eq);
              }
            }

#endif /* 0 */

          }
        }
      }/* use lists */
      Trace("cc:detail") << "CC in prop done with useList of " << ap << std::endl;

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

      classList(ap).concat(classList(bp));
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
                         << "NORMALIZE a:" << normalize(node(s)) << std::endl
                         << "b          :" << node(t) << std::endl
                         << "NORMALIZE b:" << normalize(node(t)) << std::endl
                         << "alreadyCongruent?:" << areCongruent(node(s), node(t)) << std::endl;
    }
    Assert(areCongruent(node(s), node(t)));

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
    d_proof[p] = c;
    d_proofLabel[p] = edgePf;
    c = p;
    p = pParSave;
    edgePf = pLabelSave;
    Trace("cc") << "CC PROOF now   at c == " << c << std::endl
                << "                  p == " << p << std::endl
                << "             edgePf == " << edgePf << std::endl;
  }

  // add an edge from a to b
  d_proof[a] = b;
  d_proofLabel[a] = e;
}/* mergeProof() */


template <class OutputChannel>
typename CongruenceClosure<OutputChannel>::Cid CongruenceClosure<OutputChannel>::normalize(Cid t) const
  throw(AssertionException) {
  Trace("cc:detail") << "normalize " << t << std::endl;
#if 0
  if(!isCongruenceOperator(t)) {// t is a constant
    t = find(t);
    Trace("cc:detail") << "  find " << t << std::endl;
    return t;
  } else {// t is an apply
    NodeBuilder<> apb(kind::TUPLE);
    Assert(normalize(t.getOperator()) == t.getOperator(),
           "CongruenceClosure:: bad state: "
           "function symbol merged with another");
    if(t.getMetaKind() == kind::metakind::PARAMETERIZED) {
      apb << t.getOperator();
    }
    Node n;
    bool allConstants = (!isCongruenceOperator(n));
    for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
      TNode c = *i;
      n = normalize(c);
      apb << n;
      allConstants = (allConstants && !isCongruenceOperator(n));
    }

    Node ap = apb;
    Trace("cc:detail") << "  got ap " << ap << std::endl;

    Node theLookup = lookup(ap);
    if(allConstants && !theLookup.isNull()) {
      Assert(theLookup.getKind() == kind::EQUAL ||
             theLookup.getKind() == kind::IFF);
      Assert(isCongruenceOperator(theLookup[0]));
      Assert(!isCongruenceOperator(theLookup[1]));
      return find(theLookup[1]);
    } else {
      NodeBuilder<> fa(t.getKind());
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        fa << *i;
      }
      // ensure a hard Node link exists for the return
      Node n = fa;
      return n;
    }
  }
#else /* 0 */
  return t;
#endif /* 0 */
}/* normalize() */


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
  out << "==============================================" << std::endl;

  /*out << "Representatives:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::RepresentativeMap::const_iterator i = cc.d_representative.begin(); i != cc.d_representative.end(); ++i) {
    out << "  " << (*i).first << " => " << (*i).second << std::endl;
  }*/

  out << "ClassLists:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::ClassLists::const_iterator i = cc.d_classList.begin(); i != cc.d_classList.end(); ++i) {
    if(cc.find((*i).first) == (*i).first) {
      out << "  " << (*i).first << " =>" << std::endl;
      for(typename CongruenceClosure<OutputChannel>::ClassList::const_iterator j = (*i).second->begin(); j != (*i).second->end(); ++j) {
        out << "      " << *j << std::endl;
      }
    }
  }

  out << "UseLists:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::UseLists::const_iterator i = cc.d_useList.begin(); i != cc.d_useList.end(); ++i) {
    if(cc.find((*i).first) == (*i).first) {
      out << "  " << (*i).first << " =>" << std::endl;
      for(typename CongruenceClosure<OutputChannel>::UseList::const_iterator j = (*i).second->begin(); j != (*i).second->end(); ++j) {
        out << "      " << *j << std::endl;
      }
    }
  }

  out << "Lookup:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::LookupMap::const_iterator i = cc.d_lookup.begin(); i != cc.d_lookup.end(); ++i) {
    TNode n = (*i).second;
    out << "  " << (*i).first << " => " << n << std::endl;
  }

  out << "Care set:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::CareSet::const_iterator i = cc.d_careSet.begin(); i != cc.d_careSet.end(); ++i) {
    out << "  " << *i << std::endl;
  }

  out << "==============================================" << std::endl;

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__CONGRUENCE_CLOSURE_H */

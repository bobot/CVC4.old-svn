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

#include <list>
#include <ext/hash_map>
#include <ext/hash_set>
#include <sstream>

#include "expr/node_manager.h"
#include "expr/node.h"
#include "context/context.h"
#include "context/cdmap.h"
#include "context/cdset.h"
#include "context/cdlist.h"
#include "util/exception.h"

namespace CVC4 {

template <class OutputChannel>
class CongruenceClosure;

template <class OutputChannel>
std::ostream& operator<<(std::ostream& out,
                         const CongruenceClosure<OutputChannel>& cc);

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
 * by adding a number of relevant terms with addTerm() and equalities
 * with addEquality().  It then gets notified (through OutputChannel,
 * below), of new equalities.
 *
 * OutputChannel is a template argument (it's probably a thin layer,
 * and we want to avoid a virtual call hierarchy in this case, and
 * enable aggressive inlining).  It need only implement one method,
 * notifyCongruent():
 *
 *   class MyOutputChannel {
 *   public:
 *     void notifyCongruent(TNode a, TNode b) {
 *       // CongruenceClosure is notifying us that "a" is now the EC
 *       // representative for "b" in this context.  After a pop, "a"
 *       // will be its own representative again.  Note that "a" and
 *       // "b" might never have been added with addTerm().  However,
 *       // something in their equivalence class was (for which a
 *       // previous notifyCongruent() would have notified you of
         // their EC representative, which is now "a" or "b").
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
  /** The context */
  context::Context* d_context;

  /** The output channel */
  OutputChannel* d_out;

  // typedef all of these so that iterators are easy to define
  typedef context::CDMap<Node, Node, NodeHashFunction> RepresentativeMap;
  typedef context::CDList<Node> ClassList;
  typedef context::CDMap<Node, ClassList*, NodeHashFunction> ClassLists;
  typedef context::CDList<Node> UseList;
  typedef context::CDMap<TNode, UseList*, TNodeHashFunction> UseLists;
  typedef context::CDMap<Node, Node, NodeHashFunction> LookupMap;

  //typedef context::CDMap<Node, context::CDList<Node>*, NodeHashFunction> CareClassLists;
  typedef context::CDList<Node> CareUseList;
  typedef context::CDMap<TNode, CareUseList*, TNodeHashFunction> CareUseLists;

  typedef context::CDMap<Node, Node, NodeHashFunction> ProofMap;
  typedef context::CDMap<Node, Node, NodeHashFunction> ProofLabel;

  RepresentativeMap d_representative;
  ClassLists d_classList;
  //CareClassLists d_careClassList;
  UseLists d_useList;
  UseLists d_functionUseList;
  CareUseLists d_careUseList;
  LookupMap d_lookup;

  ProofMap d_proof;
  ProofLabel d_proofLabel;

  /**
   * The set of terms we care about (i.e. those that have been given
   * us with addTerm() and their representatives).
   */
  typedef context::CDSet<Node, NodeHashFunction> CareSet;
  CareSet d_careSet;

public:
  /** Construct a congruence closure module instance */
  CongruenceClosure(context::Context* ctxt, OutputChannel* out)
    throw(AssertionException) :
    d_context(ctxt),
    d_out(out),
    d_representative(ctxt),
    d_classList(ctxt),
    //d_careClassList(ctxt),
    d_useList(ctxt),
    d_functionUseList(ctxt),
    d_careUseList(ctxt),
    d_lookup(ctxt),
    d_proof(ctxt),
    d_proofLabel(ctxt),
    d_careSet(ctxt) {
  }

  /**
   * Add a term into CC consideration.  This is context-dependent.
   * Calls OutputChannel::notifyCongruent(), so it can throw anything
   * that that function can.
   */
  void addTerm(TNode trm);

  /**
   * Add an equality literal eq into CC consideration.  This is
   * context-dependent.  Calls OutputChannel::notifyCongruent()
   * indirectly, so it can throw anything that that function can.
   */
  void addEquality(TNode eq);

  /**
   * Inquire whether two expressions are congruent in the current
   * context.
   */
  inline bool areCongruent(TNode a, TNode b) const throw(AssertionException) {
    Debug("cc") << "CC areCongruent? " << a << "  ==  " << b << std::endl;
    Debug("cc") << "  a  " << a << std::endl;
    Debug("cc") << "  a' " << normalize(a) << std::endl;
    Debug("cc") << "  b  " << b << std::endl;
    Debug("cc") << "  b' " << normalize(b) << std::endl;

    Node ap = find(a), bp = find(b);

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

  /**
   * Find the EC representative for a term t in the current context.
   */
  inline TNode find(TNode t) const throw(AssertionException) {
    context::CDMap<Node, Node, NodeHashFunction>::iterator i =
      d_representative.find(t);
    return (i == d_representative.end()) ? t : TNode((*i).second);
  }

  /**
   * Request an explanation for why a and b are in the same EC in the
   * current context.  Throws a CongruenceClosureException if they
   * aren't in the same EC.
   */
  Node explain(TNode a, TNode b)
    throw(CongruenceClosureException, AssertionException);

  /**
   * Request an explanation for why the lhs and rhs of this equality
   * are in the same EC.  Throws a CongruenceClosureException if they
   * aren't in the same EC.
   */
  inline Node explain(TNode eq)
    throw(CongruenceClosureException, AssertionException) {
    Assert(eq.getKind() == kind::EQUAL);
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
  void propagate(TNode seed);

  /**
   * Internal lookup mapping from tuples to equalities.
   */
  inline TNode lookup(TNode a) const {
    context::CDMap<Node, Node, NodeHashFunction>::iterator i = d_lookup.find(a);
    if(i == d_lookup.end()) {
      return TNode::null();
    } else {
      TNode l = (*i).second;
      Assert(l.getKind() == kind::TUPLE);
      Assert(l.getNumChildren() == 2);
      Assert((l[1] != l[0][0] || l[0][0].getKind() == kind::APPLY_UF) &&
             (l[1] != l[0][1] || l[0][1].getKind() == kind::APPLY_UF));
      Assert(l[1] == l[0][0] || l[1] == l[0][1]);
      return l;
    }
  }

  /**
   * Internal lookup mapping.
   */
  inline void setLookup(TNode a, TNode b, TNode side) {
    Assert(a.getKind() == kind::TUPLE);
    Assert(b.getKind() == kind::EQUAL);
    Assert(side == b[0] || side == b[1]);
    d_lookup[a] = NodeManager::currentNM()->mkNode(kind::TUPLE, b, side);
  }

  /**
   * Given an apply (f a1 a2...), build a TUPLE expression
   * (f', a1', a2', ...) suitable for a lookup() key.
   */
  Node buildRepresentativesOfApply(TNode apply, Kind kindToBuild = kind::TUPLE)
    throw(AssertionException);

  Node buildNormalsOfApply(TNode apply, Kind kindToBuild = kind::TUPLE)
    throw(AssertionException);

  /**
   * Append equality "eq" to uselist of "of".
   */
  inline void appendToUseList(TNode of, TNode eq) {
    Debug("cc") << "adding " << eq << " to use list of " << of << std::endl;
    Assert(eq.getKind() == kind::EQUAL);
    Assert(of == find(of));
    UseLists::iterator usei = d_useList.find(of);
    UseList* ul;
    if(usei == d_useList.end()) {
      ul = new(d_context->getCMM()) UseList(true, d_context);
      d_useList.insertDataFromContextMemory(of, ul);
    } else {
      ul = (*usei).second;
    }
    ul->push_back(eq);
  }

  /**
   * Register application "app" in its children's function-uselists
   * (and drill down recursively through applications).
   */
  void addToFunctionUseLists(TNode app) {
    if(app.getKind() == kind::APPLY_UF) {
      // intentionally don't add app to the operator's
      // function-uselist, but still handle it if it is itself an
      // application
      addToFunctionUseLists(app.getOperator());
      for(TNode::iterator c = app.begin(); c != app.end(); ++c) {
        appendToFunctionUseList(find(*c), app);
        addToFunctionUseLists(*c);
      }
    }
  }

  /**
   * Append apply "app" to function-uselist of "of".
   */
  inline void appendToFunctionUseList(TNode of, TNode app) {
    Debug("cc") << "adding " << app << " to function use list of " << of << std::endl;
    Assert(app.getKind() == kind::APPLY_UF);
    Assert(of == find(of));
    UseLists::iterator usei = d_functionUseList.find(of);
    UseList* ul;
    if(usei == d_functionUseList.end()) {
      ul = new(d_context->getCMM()) UseList(true, d_context);
      d_functionUseList.insertDataFromContextMemory(of, ul);
    } else {
      ul = (*usei).second;
    }
    ul->push_back(app);
  }

  /**
   * Append to care-uselist of "of".
   */
  inline void appendToCareUseList(TNode of, TNode n) {
    Debug("cc") << "append " << n << " to care-use-list of " << of << std::endl;
    Assert(n.getKind() != kind::EQUAL);
    Assert(of == find(of));
    CareUseLists::iterator cusei = d_careUseList.find(of);
    CareUseList* cul;
    if(cusei == d_careUseList.end()) {
      cul = new(d_context->getCMM()) CareUseList(true, d_context);
      d_careUseList.insertDataFromContextMemory(of, cul);
    } else {
      cul = (*cusei).second;
    }
    cul->push_back(n);
  }

  /**
   * Merge equivalence class ec1 under ec2.  ec1's new union-find
   * representative becomes ec2.  Calls
   * OutputChannel::notifyCongruent(), so it can throw anything that
   * that function can.
   */
  void merge(TNode ec1, TNode ec2);
  void mergeProof(TNode a, TNode b, TNode e);

  /**
   * Internal normalization.
   */
  Node normalize(TNode t) const throw(AssertionException);

  /**
   * Why is t congruent to normalize(t) ?
   */
  Node normalizeWithProof(TNode t,
                          __gnu_cxx::hash_set<Node, NodeHashFunction>& pf,
                          __gnu_cxx::hash_set<Node, NodeHashFunction>& alreadySeen)
    throw(AssertionException);

  Node normalizeWithProof(TNode t,
                          __gnu_cxx::hash_set<Node, NodeHashFunction>& pf)
    throw(AssertionException) {
    __gnu_cxx::hash_set<Node, NodeHashFunction> seen;
    return normalizeWithProof(t, pf, seen);
  }

  /**
   * Why is t equal to find(t) ?
   */
  Node findWithProof(TNode t,
                     __gnu_cxx::hash_set<Node, NodeHashFunction>& pf)
    throw(AssertionException);

  /**
   * Adds "term equalities".  "t" is assumed to be a function
   * application.  This function calls addEquality(t == t), then for
   * each child that is a function application calls
   * addTermEqualities() recursively.  Calls
   * OutputChannel::notifyCongruent() indirectly, so it can throw
   * anything that that function can.
   */
  //void addTermEqualities(TNode t);

  /**
   * Add subterms of trm to proper careUseLists and notify (through
   * OutputChannel) any new important congruences.
   */
  void addSubtermCares(TNode trm);

};/* class CongruenceClosure */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::addTerm(TNode trm) {
  Node trmp = find(trm);
  bool alreadyCaredAbout = d_careSet.contains(trm);

  Debug("cc") << "CC addTerm [" << d_careSet.size() << "]: " << trm
              << std::endl;

  if(!alreadyCaredAbout) {
    if(trm != trmp) {
      // if part of an equivalence class headed by another node,
      // notify the client of this merge that's already been
      // performed..
      d_out->notifyCongruent(trm, trmp);
    }

    // add its representative to the care set
    d_careSet.insert(trmp);

    addSubtermCares(trm);
  }
}


/*
template <class OutputChannel>
void CongruenceClosure<OutputChannel>::addTermEqualities(TNode trm) {
  addEquality(NodeManager::currentNM()->mkNode(kind::EQUAL, trm, trm));
  for(TNode::iterator i = trm.begin(); i != trm.end(); ++i) {
    TNode n = *i;
    if(n.getKind() == kind::APPLY_UF) {
      addTermEqualities(n);
    }
  }
}
*/


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::addSubtermCares(TNode trm) {
  Assert(trm.getKind() == kind::APPLY_UF);
  for(TNode::iterator i = trm.begin(); i != trm.end(); ++i) {
    TNode n = *i;
    Node np = find(n);
    if(n != np) {
      Node trm2 = buildRepresentativesOfApply(trm, kind::APPLY_UF);

      // FIXME: I _think_ this should catch all congruences _without_
      // having to look at lookup().  [same FIXME as in propagate]
      propagate(trm.eqNode(trm2));
    }
    appendToCareUseList(np, trm);
    if(n.getKind() == kind::APPLY_UF) {
      addSubtermCares(n);
    }
  }
}


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::addEquality(TNode eq) {
  Debug("cc") << "CC addEquality[" << d_context->getLevel() << "]: " << eq << std::endl;
  Assert(eq.getKind() == kind::EQUAL);
  if(areCongruent(eq[0], eq[1])) {
    Debug("cc") << "CC -- redundant, ignoring...\n";
    return;
  }

  TNode s = eq[0], t = eq[1];

  bool sIsApplication = (s.getKind() == kind::APPLY_UF);
  bool tIsApplication = (t.getKind() == kind::APPLY_UF);

  Assert(s != t);

  if(!sIsApplication && tIsApplication) {
    s = eq[1];
    t = eq[0];
    sIsApplication = !sIsApplication;
    tIsApplication = !tIsApplication;
  }

  Debug("cc:detail") << "CC        " << s << " == " << t << std::endl;

  // change from paper: do this whether or not s, t are applications
  Debug("cc:detail") << "CC        propagating the eq" << std::endl;
  propagate(eq);

  if(sIsApplication) {
    Node ap = buildNormalsOfApply(s);

    Debug("cc:detail") << "CC rewrLHS " << "op_and_args_a == " << t << std::endl;
    Debug("cc") << "CC ap is   " << ap << std::endl;

    TNode l = lookup(ap);
    Debug("cc:detail") << "CC lookup(ap): " << l << std::endl;
    if(!l.isNull()) {
      // ensure a hard Node link exists to this during the call
      Node pending = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, s, l[0], l[1]);
      Debug("cc:detail") << "pending1 " << pending << std::endl;
      propagate(pending);
    } else {
      Debug("cc") << "CC lookup(ap) setting to " << eq << std::endl;
      setLookup(ap, eq, s);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        appendToUseList(*i, eq);
      }
    }
  }

  if(tIsApplication) {
    Assert(s != t);
    // go backward, symmetrically
    Node ap = buildNormalsOfApply(t);

    Debug("cc:detail") << "CC2rewrRHS " << s << " == op_and_args_a" << std::endl;
    Debug("cc") << "CC2ap is   " << ap << std::endl;

    TNode l = lookup(ap);
    Debug("cc:detail") << "CC2lookup(ap): " << l << std::endl;
    if(!l.isNull()) {
      // ensure a hard Node link exists to this during the call
      Node pending = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, t, l[0], l[1]);
      Debug("cc:detail") << "pending3 " << pending << std::endl;
      propagate(pending);
    } else {
      Debug("cc") << "CC2lookup(ap) setting to " << eq << std::endl;
      setLookup(ap, eq, t);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        appendToUseList(*i, eq);
      }
    }
  }

  addToFunctionUseLists(s);
  addToFunctionUseLists(t);

  Debug("cc") << *this;
}/* addEquality() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::buildRepresentativesOfApply(TNode apply,
                                                              Kind kindToBuild)
  throw(AssertionException) {
  Assert(apply.getKind() == kind::APPLY_UF);
  NodeBuilder<> argspb(kindToBuild);
  argspb << find(apply.getOperator());
  for(TNode::iterator i = apply.begin(); i != apply.end(); ++i) {
    argspb << find(*i);
  }
  return argspb;
}/* buildRepresentativesOfApply() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::buildNormalsOfApply(TNode apply,
                                                           Kind kindToBuild)
  throw(AssertionException) {
  Assert(apply.getKind() == kind::APPLY_UF);
  NodeBuilder<> argspb(kindToBuild);
  argspb << normalize(apply.getOperator());
  for(TNode::iterator i = apply.begin(); i != apply.end(); ++i) {
    argspb << normalize(*i);
  }
  return argspb;
}/* buildNormalsOfApply() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::propagate(TNode seed) {
  Debug("cc:detail") << "=== doing a round of propagation ===" << std::endl
              << "the \"seed\" propagation is: " << seed << std::endl;

  std::list<Node> pending;

  Debug("cc") << "seed propagation with: " << seed << std::endl;
  pending.push_back(seed);
  do { // while(!pending.empty())
    Node e = pending.front();
    pending.pop_front();

    Debug("cc") << "=== top of propagate loop ===" << std::endl;
    Debug("cc") << "=== e is " << e << " ===" << std::endl;

    TNode a, b;
    if(e.getKind() == kind::EQUAL) {
      // e is an equality a = b (change from paper: a, b may not be consts)

      a = e[0];
      b = e[1];

      Debug("cc:detail") << "propagate equality: " << a << " == " << b << std::endl;
    } else {
      // e is a tuple ( apply f A... = a , apply f B... = b )

      Debug("cc") << "propagate tuple: " << e << "\n";

      Assert(e.getKind() == kind::TUPLE);

      if(e.getNumChildren() == 4) {
        Assert(e[0].getKind() == kind::EQUAL);
        Assert(e[1] == e[0][0] || e[1] == e[0][1]);
        Assert(e[2].getKind() == kind::EQUAL);
        Assert(e[3] == e[2][0] || e[3] == e[2][1]);
        Assert(e[1].getKind() == kind::APPLY_UF);
        Assert(e[3].getKind() == kind::APPLY_UF);
        Assert(e[1].getNumChildren() == e[3].getNumChildren());

        // tuple is (eq, eqside, lookup, lookupside)
        a = (e[1] == e[0][0] ? e[0][1] : e[0][0]);
        b = (e[3] == e[2][0] ? e[2][1] : e[2][0]);

        Debug("cc") << "                 ( " << a << " , " << b << " )" << std::endl;
      } else {
        Assert(e.getNumChildren() == 3);
        // normalizing term proof
        // a one-step normalizes to b because of input equality e
        a = e[0];
        b = e[1];
        e = e[2];
      }
    }

    Debug("cc:detail") << "=====at start=====" << std::endl
                << "a          :" << a << std::endl
                << "NORMALIZE a:" << normalize(a) << std::endl
                << "b          :" << b << std::endl
                << "NORMALIZE b:" << normalize(b) << std::endl
                << "alreadyCongruent?:" << areCongruent(a,b) << std::endl;

    // change from paper: need to normalize() here since in our
    // implementation, a and b can be applications
    Node ap = find(a), bp = find(b);
    if(ap != bp) {

      Debug("cc:detail") << "EC[a] == " << ap << std::endl
                  << "EC[b] == " << bp << std::endl;

      /* Nice optimization, but we need to merge in the direction of
       * smaller node id, or we get infinite recursion in normalize(),
       * since a node might have a find() pointer to a
       * structurally-containing node.  E.g. find(z) = (apply f z).
      // w.l.o.g., |classList ap| <= |classList bp|
      context::CDList<Node>* cl_ap_tmp = d_classList[ap];
      context::CDList<Node>* cl_bp_tmp = d_classList[bp];
      unsigned sizeA = (cl_ap_tmp == NULL ? 0 : cl_ap_tmp->size());
      unsigned sizeB = (cl_bp_tmp == NULL ? 0 : cl_bp_tmp->size());
      Debug("cc:detail") << "sizeA == " << sizeA << "  sizeB == " << sizeB << std::endl;
      if(sizeA > sizeB) {
        Debug("cc:detail") << "swapping..\n";
        TNode tmp = ap; ap = bp; bp = tmp;
        tmp = a; a = b; b = tmp;
      }
      */

      if(ap.getId() < bp.getId()) {
        TNode tmp = ap; ap = bp; bp = tmp;
        tmp = a; a = b; b = tmp;
      }

      { // class list handling
        ClassLists::iterator cl_bpi = d_classList.find(bp);
        ClassList* cl_bp;
        if(cl_bpi == d_classList.end()) {
          cl_bp = new(d_context->getCMM()) ClassList(true, d_context);
          d_classList.insertDataFromContextMemory(bp, cl_bp);
          Debug("cc:detail") << "CC in prop alloc classlist for " << bp << std::endl;
        } else {
          cl_bp = (*cl_bpi).second;
        }
        // we don't store 'ap' in its own class list; so process it here
        Debug("cc:detail") << "calling mergeproof/merge1 " << ap
                           << "   AND   " << bp << std::endl;
        mergeProof(a, b, e);
        merge(ap, bp);

        Debug("cc") << " adding ap == " << ap << std::endl
                    << "   to class list of " << bp << std::endl;
        cl_bp->push_back(ap);
        ClassLists::const_iterator cli = d_classList.find(ap);
        if(cli != d_classList.end()) {
          const ClassList* cl = (*cli).second;
          for(ClassList::const_iterator i = cl->begin();
              i != cl->end();
              ++i) {
            TNode c = *i;
            Debug("cc") << "c is " << c << "\n"
                        << " from cl of " << ap << std::endl;
            Debug("cc") << " it's find ptr is: " << find(c) << std::endl;
            Assert(find(c) == ap);
            Debug("cc:detail") << "calling merge2 " << c << bp << std::endl;
            merge(c, bp);
            // move c from classList(ap) to classlist(bp);
            //i = cl.erase(i);// FIXME do we need to?
            Debug("cc") << " adding c to class list of " << bp << std::endl;
            cl_bp->push_back(c);
          }
        }
        Debug("cc:detail") << "bottom\n";
      }

      { // use list handling
        Debug("cc:detail") << "ap is " << ap << std::endl;
        Debug("cc:detail") << "find(ap) is " << find(ap) << std::endl;
        Debug("cc:detail") << "CC in prop go through useList of " << ap << std::endl;
        UseLists::iterator usei = d_useList.find(ap);
        if(usei != d_useList.end()) {
          UseList* ul = (*usei).second;
          //for( f(c1,c2)=c in UseList(ap) )
          for(UseList::const_iterator i = ul->begin();
              i != ul->end();
              ++i) {
            TNode eq = *i;
            Debug("cc") << "CC  -- useList: " << eq << std::endl;
            Assert(eq.getKind() == kind::EQUAL);
            // change from paper
            // use list elts can have form (apply c..) = x  OR  x = (apply c..)
            Assert(eq[0].getKind() == kind::APPLY_UF || eq[1].getKind() == kind::APPLY_UF);
            // do for each side that is an application
            for(int side = 0; side <= 1; ++side) {
              if(eq[side].getKind() != kind::APPLY_UF) {
                continue;
              }

              Node cp = buildNormalsOfApply(eq[side]);

              // if lookup(c1',c2') is some f(d1,d2)=d then
              TNode n = lookup(cp);

              Debug("cc:detail") << "CC     -- c' is " << cp << std::endl;

              if(!n.isNull()) {
                Debug("cc:detail") << "CC     -- lookup(c') is " << n << std::endl;
                // add (f(c1,c2)=c,f(d1,d2)=d) to pending
                Node tuple = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, eq[side], n[0], n[1]);
                Debug("cc") << "CC add tuple to pending: " << tuple << std::endl;
                pending.push_back(tuple);
                // remove f(c1,c2)=c from UseList(ap)
                Debug("cc:detail") << "supposed to remove " << eq << std::endl
                                   << "  from UseList of " << ap << std::endl;
                //i = ul.erase(i);// FIXME do we need to?
              } else {
                Debug("cc") << "CC     -- lookup(c') is null" << std::endl;
                Debug("cc") << "CC     -- setlookup(c') to " << eq << std::endl;
                // set lookup(c1',c2') to f(c1,c2)=c
                setLookup(cp, eq, eq[side]);
                // move f(c1,c2)=c from UseList(ap) to UseList(b')
                //i = ul.erase(i);// FIXME do we need to remove from UseList(ap) ?
                appendToUseList(bp, eq);
              }
            }
          }
        }
      }/* use lists */
      Debug("cc:detail") << "CC in prop done with useList of " << ap << std::endl;

      { // function use list handling
        Debug("cc") << "CC in prop go through functionUseList of " << ap << std::endl;
        UseLists::iterator usei = d_functionUseList.find(ap);
        if(usei != d_functionUseList.end()) {
          UseList* ul = (*usei).second;
          for(UseList::const_iterator i = ul->begin();
              i != ul->end();
              ++i) {
            TNode app = *i;
            Debug("cc") << "CC  -- functionUseList: " << app << std::endl;
            Assert(app.getKind() == kind::APPLY_UF);
            Node appA = NodeManager::currentNM()->mkNode(kind::APPLY_UF, app.getOperator(), ap);
            Node appB = NodeManager::currentNM()->mkNode(kind::APPLY_UF, app.getOperator(), bp);
            Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, appA, appB);
            Debug("cc") << "CC     add pending " << eq << std::endl;
            pending.push_back(eq);
            appendToFunctionUseList(bp, app);
          }
        }

        Debug("cc") << "CC in prop go through functionUseList of " << bp << std::endl;
        usei = d_functionUseList.find(bp);
        if(usei != d_functionUseList.end()) {
          UseList* ul = (*usei).second;
          for(UseList::const_iterator i = ul->begin();
              i != ul->end();
              ++i) {
            TNode app = *i;
            Debug("cc") << "CC  -- functionUseList: " << app << std::endl;
            Assert(app.getKind() == kind::APPLY_UF);
            Node appA = NodeManager::currentNM()->mkNode(kind::APPLY_UF, app.getOperator(), ap);
            Node appB = NodeManager::currentNM()->mkNode(kind::APPLY_UF, app.getOperator(), bp);
            Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, appA, appB);
            Debug("cc") << "CC     add pending " << eq << std::endl;
            pending.push_back(eq);
          }
        }
        Debug("cc") << "CC in prop done with functionUseLists" << std::endl;
      }/* function use lists */

      { // care use list handling
        UseLists::iterator cusei = d_careUseList.find(ap);
        if(cusei != d_careUseList.end()) {
          CareUseList* cul = (*cusei).second;
          for(CareUseList::const_iterator i = cul->begin();
              i != cul->end();
              ++i) {
            TNode apply = *i;
            Debug("cc:detail") << "CC  -- careUseList: " << apply << std::endl;
            Assert(apply.getKind() == kind::APPLY_UF);

            Node apply2 = buildRepresentativesOfApply(apply, kind::APPLY_UF);

            // FIXME: I _think_ this should catch all congruences
            // _without_ having to look at lookup().
            pending.push_back(apply.eqNode(apply2));

            appendToCareUseList(bp, apply);
          }
        }
      }
    } else {
      Debug("cc:detail") << "CCs the same ( == " << ap << "), do nothing."
                  << std::endl;
    }

    Debug("cc") << "=====at end=====" << std::endl
                << "a          :" << a << std::endl
                << "NORMALIZE a:" << normalize(a) << std::endl
                << "b          :" << b << std::endl
                << "NORMALIZE b:" << normalize(b) << std::endl
                << "alreadyCongruent?:" << areCongruent(a,b) << std::endl;
    Assert(areCongruent(a, b));
  } while(!pending.empty());
}/* propagate() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::merge(TNode ec1, TNode ec2) {
  /*
  Debug("cc:detail") << "  -- merging " << ec1
                     << (d_careSet.find(ec1) == d_careSet.end() ?
                         " -- NOT in care set" : " -- IN CARE SET") << std::endl
                     << "         and " << ec2
                     << (d_careSet.find(ec2) == d_careSet.end() ?
                         " -- NOT in care set" : " -- IN CARE SET") << std::endl;
  */

  Debug("cc") << "CC setting rep of " << ec1 << std::endl;
  Debug("cc") << "CC             to " << ec2 << std::endl;

  /* can now be applications
  Assert(ec1.getKind() != kind::APPLY_UF);
  Assert(ec2.getKind() != kind::APPLY_UF);
  */

  Assert(find(ec1) != ec2);
  //Assert(find(ec1) == ec1);
  Assert(find(ec2) == ec2);
  // merge in direction of smaller node id.  otherwise we get infinite
  // recursion in normalize, since find(z) can equal (apply f z).
  Assert(ec1.getId() > ec2.getId());

  d_representative[ec1] = ec2;

  if(d_careSet.find(ec1) != d_careSet.end()) {
    d_careSet.insert(ec2);
    d_out->notifyCongruent(ec1, ec2);
  }
}/* merge() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::mergeProof(TNode a, TNode b, TNode e) {
  Debug("cc") << "  -- merge-proofing " << a << "\n"
              << "                and " << b << "\n"
              << "               with " << e << "\n";

  // proof forest gets a -> b labeled with e

  // first reverse all the edges in proof forest to root of this proof tree
  Debug("cc") << "CC PROOF reversing proof tree\n";
  // c and p are child and parent in (old) proof tree
  Node c = a, p = d_proof[a], edgePf = d_proofLabel[a];
  // when we hit null p, we're at the (former) root
  Debug("cc") << "CC PROOF start at c == " << c << std::endl
              << "                  p == " << p << std::endl
              << "             edgePf == " << edgePf << std::endl;
  while(!p.isNull()) {
    // in proof forest,
    // we have edge   c --edgePf-> p
    // turn it into   c <-edgePf-- p

    Node pParSave = d_proof[p];
    Node pLabelSave = d_proofLabel[p];
    d_proof[p] = c;
    d_proofLabel[p] = edgePf;
    c = p;
    p = pParSave;
    edgePf = pLabelSave;
    Debug("cc") << "CC PROOF now   at c == " << c << std::endl
                << "                  p == " << p << std::endl
                << "             edgePf == " << edgePf << std::endl;
  }

  // add an edge from a to b
  d_proof[a] = b;
  d_proofLabel[a] = e;
}/* mergeProof() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::normalize(TNode t) const
  throw(AssertionException) {
  // change from paper: always find()
  Debug("cc:detail") << "normalize " << t << std::endl;
  t = find(t);
  Debug("cc:detail") << "  find " << t << std::endl;
  if(t.getKind() == kind::APPLY_UF) {
    NodeBuilder<> apb(kind::TUPLE);
    TNode op = t.getOperator();
    apb << normalize(op);
    for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
      TNode c = *i;
      Debug("cc:detail") << "INF RECUR1 ?" << std::endl;
      Node n = normalize(c);
      apb << n;
    }

    Node ap = apb;
    Debug("cc:detail") << "  got ap " << ap << std::endl;

    Node theLookup = lookup(ap);
    if(!theLookup.isNull()) {
      Node theLookupSide = theLookup[1];
      theLookup = theLookup[0];

      Assert(theLookup.getKind() == kind::EQUAL);

      Assert(find(theLookup[0]) == find(theLookup[1]));

      return find(theLookup[0]);
    } else {
      NodeBuilder<> fa(kind::APPLY_UF);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        fa << *i;
        Debug("cc:detail") << "n[[" << t << "]]it :: " << *i << std::endl;
      }
      // ensure a hard Node link exists during the call
      Node n = fa;
      return find(n);
    }
  } else {
    Debug("cc:detail") << "  exit" << std::endl;
    return t;
  }
}/* normalize() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::findWithProof
  (TNode t, __gnu_cxx::hash_set<Node, NodeHashFunction>& pf)
  throw(AssertionException) {
  // why is t congruent to its class representative ?
  // output equality labels in proof tree
  Node p = t;
  do {
    Node e = d_proofLabel[p];
    Debug("cc") << "CC proof tree for a: " << p << std::endl;
    Debug("cc") << "              label: " << e << std::endl;
    //    Debug("cc:detail") << "              rep is:" << normalize(p) << std::endl;
    Assert(e.isNull() == d_proof[p].get().isNull());
    if(!e.isNull()) {
      if(e.getKind() == kind::EQUAL) {
        // e is either an EQUALity justifying the proof step...
        pf.insert(e);
      } else {
        // ...or a TUPLE describing the proof steps to make
      }
    }
  } while(!(p = d_proof[p]).isNull());

  Node rep = find(t);
  p = rep;
  do {
    Node e = d_proofLabel[p];
    Debug("cc") << "CC pf tree for rep : " << p << std::endl;
    Debug("cc") << "              label: " << e << std::endl;
    //    Debug("cc:detail") << "              rep is:" << normalize(p) << std::endl;
    Assert(e.isNull() == d_proof[p].get().isNull());
    if(!e.isNull()) {
      Assert(e.getKind() == kind::EQUAL);
      pf.insert(e);
    }
  } while(!(p = d_proof[p]).isNull());

  return rep;
}/* findWithProof() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::normalizeWithProof
  (TNode t, __gnu_cxx::hash_set<Node, NodeHashFunction>& pf,
   __gnu_cxx::hash_set<Node, NodeHashFunction>& alreadySeen)
  throw(AssertionException) {
  if(alreadySeen.find(t) != alreadySeen.end()) {
    Debug("cc") << "normalizeWithProof() has already seen: " << t << std::endl;
    return Node::null();
  } else {
    Debug("cc") << "normalizeWithProof() hasn't yet seen: " << t << std::endl;
    alreadySeen.insert(t);
  }
  // change from paper: always find()
  Debug("cc") << "find of : " << t << std::endl;
  t = findWithProof(t, pf);
  Debug("cc") << "   is   : " << t << std::endl;
  if(t.getKind() == kind::APPLY_UF) {
    NodeBuilder<> apb(kind::TUPLE);
    TNode op = t.getOperator();
    apb << (alreadySeen.find(op) == alreadySeen.end() ?
            normalizeWithProof(op, pf, alreadySeen) :
            normalize(op));
    for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
      TNode c = *i;
      Node n = (alreadySeen.find(c) == alreadySeen.end() ?
                normalizeWithProof(c, pf, alreadySeen) :
                normalize(c));
      apb << n;
    }

    Node ap = apb;
    Debug("cc:detail") << "  got ap " << ap << std::endl;

    Node theLookup = lookup(ap);
    if(!theLookup.isNull()) {
      Node theLookupSide = theLookup[1];
      theLookup = theLookup[0];

      Assert(find(theLookup[0]) == find(theLookup[1]));

      NodeBuilder<> fa(kind::APPLY_UF);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        fa << *i;
        Debug("cc") << "n[[" << t << "]]it :: " << *i << std::endl;
      }
      // ensure a hard Node link exists during the call
      Node n = fa;

      Assert(theLookup.getKind() == kind::EQUAL);
      // lookup eqs can have form (apply c..) = x  OR  x = (apply c..)
      Debug("cc") << "n[[" << t << "]]theLookup is " << theLookup << std::endl;
      // output pf that t congruent to theLookup
      Debug("cc") << "============== LOOKUP PROOF ==============\n";
      Debug("cc") << theLookup << std::endl;
      Debug("cc") << "============== LOOKUP PROOF ==============\n";
      pf.insert(theLookup);

      // we care what _side_ we came from for the lookup
      if(theLookupSide == theLookup[0]) {
        // change from paper: theLookup[1] might not be a constant in our case
        Debug("cc") << "dir >> so normalize-with-proof " << theLookup[0].getOperator() << std::endl;
        Debug("cc") << "dir >>   get " << normalize(theLookup[0].getOperator()) << std::endl;
        normalizeWithProof(theLookup[0].getOperator(), pf, alreadySeen);
        Debug("cc") << "dir >> so normalize-with-proof " << theLookup[0][0] << std::endl;
        Debug("cc") << "dir >>   get " << normalize(theLookup[0][0]) << std::endl;
        normalizeWithProof(theLookup[0][0], pf, alreadySeen);//fixme all args
        Debug("cc") << "dir >> then return find-with-proof " << theLookup[1] << std::endl;
        return findWithProof(theLookup[1], pf);
      } else {// theLookupSide == theLookup[1]
        // change from paper: theLookup[0] might not be a constant in our case
        Debug("cc") << "dir << so normalize-with-proof " << theLookup[1].getOperator() << std::endl;
        Debug("cc") << "dir <<   get " << normalize(theLookup[1].getOperator()) << std::endl;
        normalizeWithProof(theLookup[1].getOperator(), pf, alreadySeen);
        Debug("cc") << "dir << so normalize-with-proof " << theLookup[1][0] << std::endl;
        Debug("cc") << "dir <<   get " << normalize(theLookup[1][0]) << std::endl;
        normalizeWithProof(theLookup[1][0], pf, alreadySeen); //fixme all args
        Debug("cc") << "dir << then return find-with-proof " << theLookup[0] << std::endl;
        return findWithProof(theLookup[0], pf);
      }
    } else {
      NodeBuilder<> fa(kind::APPLY_UF);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        fa << *i;
        Debug("cc") << "n[[" << t << "]]it :: " << *i << std::endl;
      }
      // ensure a hard Node link exists during the call
      Node n = fa;
      return findWithProof(n, pf);
    }
  } else {
    return t;
  }
}/* normalizeWithProof() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::explain(TNode a, TNode b)
  throw(CongruenceClosureException, AssertionException) {

  Assert(a != b);

  if(!areCongruent(a, b)) {
    throw CongruenceClosureException("asked to explain() congruence of nodes "
                                     "that aren't congruent");
  }

  // why does a eq b ?
  __gnu_cxx::hash_set<Node, NodeHashFunction> terms;

  Debug("cc") << "CC EXPLAINING   " << a << "\n"
              << "                " << b << "\n"
              << "CC normalize to " << normalize(a) << "\n";

  normalizeWithProof(a, terms);
  Debug("cc") << "  after the first we have\n";
  for(__gnu_cxx::hash_set<Node, NodeHashFunction>::iterator i = terms.begin();
      i != terms.end();
      ++i) {
    Debug("cc") << "    " << *i << std::endl;
  }
  normalizeWithProof(b, terms);

  Debug("cc") << "CC EXPLAIN final proof has size " << terms.size() << std::endl;

  Assert(terms.size() > 0);

  NodeBuilder<> pf(kind::AND);
  for(__gnu_cxx::hash_set<Node, NodeHashFunction>::iterator i = terms.begin();
      i != terms.end();
      ++i) {
    pf << *i;
    Debug("cc") << "CC EXPLAIN " << *i << std::endl;
  }

  Debug("cc") << "CC EXPLAIN done" << std::endl;

  if(pf.getNumChildren() == 1) {
    return pf[0];
  } else {
    return pf;
  }
}/* explain() */


template <class OutputChannel>
std::ostream& operator<<(std::ostream& out,
                         const CongruenceClosure<OutputChannel>& cc) {
  out << "==============================================" << std::endl;

  out << "Representatives:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::RepresentativeMap::const_iterator i = cc.d_representative.begin(); i != cc.d_representative.end(); ++i) {
    out << "  " << (*i).first << " => " << (*i).second << std::endl;
  }

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

  out << "FunctionUseLists:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::UseLists::const_iterator i = cc.d_functionUseList.begin(); i != cc.d_functionUseList.end(); ++i) {
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
    out << "  " << (*i).first << " => " << n[0] << " ";
    if(n[0][0] == n[1]) {
      out << "[left]" << std::endl;
    } else {
      Assert(n[0][1] == n[1]);
      out << "[right]" << std::endl;
    }
  }

  out << "==============================================" << std::endl;

  return out;
}


}/* CVC4 namespace */

#endif /* __CVC4__UTIL__CONGRUENCE_CLOSURE_H */

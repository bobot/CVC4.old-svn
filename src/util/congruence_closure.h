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

#include "expr/node_manager.h"
#include "expr/node.h"
#include "context/context.h"
#include "context/cdmap.h"
#include "context/cdset.h"
#include "context/cdlist.h"
#include "util/exception.h"

namespace CVC4 {

class CVC4_PUBLIC CongruenceClosureException;

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
 * merge():
 *
 *   class MyOutputChannel {
 *   public:
 *     void merge(TNode a, TNode b) {
 *       // CongruenceClosure is notifying us that "a" is now the EC
 *       // representative for "b" in this context.  After a pop, "a"
 *       // will be its own representative again.  Note that "a" and
 *       // "b" might never have been added with addTerm().  However,
 *       // something in their equivalence class was (for which a
 *       // previous merge() would have notified you of their EC
 *       // representative, which is now "a" or "b").
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

  std::list<Node> d_pending;
  context::CDMap<Node, Node, NodeHashFunction> d_representative;
  __gnu_cxx::hash_map<Node, context::CDList<Node>*, NodeHashFunction> d_classList;
  __gnu_cxx::hash_map<TNode, context::CDList<Node>*, TNodeHashFunction> d_useList;
  __gnu_cxx::hash_map<TNode, context::CDList<Node>*, TNodeHashFunction> d_careUseList;
  context::CDMap<Node, Node, NodeHashFunction> d_lookup;

  /**
   * The set of terms we care about (i.e. those that have been given
   * us with addTerm() and their representatives).
   */
  context::CDSet<Node, NodeHashFunction> d_careSet;

public:
  /** Construct a congruence closure module instance */
  CongruenceClosure(context::Context* ctxt, OutputChannel* out)
    throw(AssertionException) :
    d_context(ctxt),
    d_out(out),
    d_pending(),
    d_representative(ctxt),
    d_classList(),
    d_useList(),
    d_careUseList(),
    d_lookup(ctxt),
    d_careSet(ctxt) {
  }

  /**
   * Add a term into CC consideration.  This is context-dependent.
   * Calls OutputChannel::merge(), so it can throw anything that
   * that function can.
   */
  void addTerm(TNode trm);

  /**
   * Add an equality literal eq into CC consideration.  This is
   * context-dependent.  Calls OutputChannel::merge() indirectly, so
   * it can throw anything that that function can.
   */
  void addEquality(TNode eq);

  /**
   * Inquire whether two expressions are congruent in the current
   * context.
   */
  inline bool areCongruent(TNode a, TNode b) throw(AssertionException) {
    Debug("cc") << "CC areCongruent? " << a << "  ==  " << b << std::endl;
    return normalize(a) == normalize(b);
  }

  /**
   * Find the EC representative for a term t in the current context.
   */
  inline TNode find(TNode t) throw(AssertionException) {
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

  /**
   * Internal propagation of information.  Calls OutputChannel::merge()
   * indirectly, so it can throw anything that that function can.
   */
  void propagate();

  /**
   * Internal lookup mapping from tuples to equalities.
   */
  inline TNode lookup(TNode a) {
    context::CDMap<Node, Node, NodeHashFunction>::iterator i = d_lookup.find(a);
    if(i == d_lookup.end()) {
      return TNode::null();
    } else {
      return (*i).second;
    }
  }

  /**
   * Internal lookup mapping.
   */
  inline void setLookup(TNode a, TNode b) {
    Assert(a.getKind() == kind::TUPLE);
    Assert(b.getKind() == kind::EQUAL);
    d_lookup[a] = b;
  }

  /**
   * Given an apply (f a1 a2...), build a TUPLE expression
   * (f', a1', a2', ...) suitable for a lookup() key.
   */
  Node buildRepresentativesOfApply(TNode apply) throw(AssertionException);

  /**
   * Append equality "eq" to uselist of "of".
   */
  inline void appendToUseList(TNode of, TNode eq) {
    Assert(eq.getKind() == kind::EQUAL);
    Assert(of == find(of));
    context::CDList<Node>*& ul = d_useList[of];
    if(ul == NULL) {
      ul = new(d_context->getCMM()) context::CDList<Node>(d_context, true);
    }
    ul->push_back(eq);
  }

  /**
   * Append to care-uselist of "of".
   */
  inline void appendToCareUseList(TNode of, TNode n) {
    Assert(of == find(of));
    context::CDList<Node>*& cul = d_careUseList[of];
    if(cul == NULL) {
      cul = new(d_context->getCMM()) context::CDList<Node>(d_context, true);
    }
    cul->push_back(n);
  }

  /**
   * Merge equivalence class ec1 under ec2.  ec1's new union-find
   * representative becomes ec2.  Calls OutputChannel::merge(), so it
   * can throw anything that that function can.
   */
  void merge(TNode ec1, TNode ec2);

  /**
   * Internal normalization.
   */
  Node normalize(TNode t) throw(AssertionException);

  /**
   * Adds "term equalities".  "t" is assumed to be a function
   * application.  This function calls addEquality(t == t), then for
   * each child that is a function application calls
   * addTermEqualities() recursively.  Calls OutputChannel::merge()
   * indirectly, so it can throw anything that that function can.
   */
  void addTermEqualities(TNode t);

};/* class CongruenceClosure */


class CVC4_PUBLIC CongruenceClosureException : public Exception {
public:
  inline CongruenceClosureException(std::string msg) :
    Exception(std::string("Congruence closure exception: ") + msg) {}
  inline CongruenceClosureException(const char* msg) :
    Exception(std::string("Congruence closure exception: ") + msg) {}
};/* class CongruenceClosureException */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::addTerm(TNode trm) {
  bool notAlreadyCaredAbout = d_careSet.insert(trm);

  Debug("cc") << "CC addTerm [" << d_careSet.size() << "]: " << trm
              << std::endl;

  if(notAlreadyCaredAbout) {
    TNode trmp = find(trm);
    if(trm != trmp) {
      // if part of an equivalence class headed by another node,
      // notify the client of this merge that's already been
      // performed..
      d_out->merge(trm, trmp);
      // .. and add the representative to the care set if it's not already
      d_careSet.insert(trmp);
    }
  } else {
    Debug("cc") << "  (that term is already cared about)" << std::endl;
  }

  // This is necessary since we aren't flattening input equalities and
  // introducing variables.  If we don't do this, we miss congruences.
  // For example, if someone calls addTerm[ (f (f (f (f x)))) ] and
  // addTerm[ (f (f (f (f y)))) ], then addEquality( x == y ), they
  // expect a notification that (f (f (f (f x)))) == (f (f (f (f y)))),
  // but the system will miss that unless we do something with the
  // intermediate applications.
  //
  // FIXME better way ?
  if(trm.getKind() == kind::APPLY_UF) {
    addTermEqualities(trm);
  }
}


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


/*
template <class OutputChannel>
void CongruenceClosure<OutputChannel>::addSubtermCares(TNode trm) {
  for(TNode::iterator i = trm.begin(); i != trm.end(); ++i) {
    TNode n = *i;
    appendToCareUseList(find(n), trm);
    if(n.getKind() == kind::APPLY_UF) {
      addTermEqualities(n);
    }
  }
}
*/


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::addEquality(TNode eq) {
  Debug("cc") << "CC addEquality: " << eq << std::endl;

  Assert(eq.getKind() == kind::EQUAL);

  TNode s = eq[0], t = eq[1];
  bool sIsApplication = (s.getKind() == kind::APPLY_UF);
  bool tIsApplication = (t.getKind() == kind::APPLY_UF);

  //Assert(s != t);

  if(!sIsApplication && tIsApplication) {
    s = eq[1];
    t = eq[0];
    sIsApplication = !sIsApplication;
    tIsApplication = !tIsApplication;
  }

  Debug("cc") << "CC        " << s << " == " << t << std::endl;

  if(!sIsApplication && !tIsApplication) {
    // neither are applications
    d_pending.push_back(eq);
    Debug("cc") << "CC        consts, add to pending ["
                << d_pending.size() << "]" << std::endl;
    propagate();
  } else if(sIsApplication && !tIsApplication) {
    // ensure direction of equality, establishes invariants below
    Node s_eq_t = NodeManager::currentNM()->mkNode(kind::EQUAL, s, t);

    Debug("cc") << "CC        lhs is app, rhs is const" << std::endl;

    // one application (s), one not (t)
    NodeBuilder<> ab(kind::TUPLE), apb(kind::TUPLE);
    TNode op = s.getOperator();
    ab << op;
    apb << find(op);
    for(TNode::iterator i = s.begin(); i != s.end(); ++i) {
      TNode c = *i;
      ab << c;
      apb << find(c);
    }

    Node a = ab, ap = apb;

    Debug("cc") << "CC rewrLHS " << a << " == " << t << std::endl;
    Debug("cc") << "CC ap is   " << ap << std::endl;

    TNode l = lookup(ap);
    Debug("cc") << "CC lookup(ap): " << l << std::endl;
    if(!l.isNull()) {
      d_pending.push_back(NodeManager::currentNM()->mkNode(kind::TUPLE, s_eq_t, l));
      propagate();
    } else {
      Debug("cc") << "CC lookup(ap) setting to " << s_eq_t << std::endl;
      setLookup(ap, s_eq_t);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        appendToUseList(*i, s_eq_t);
      }
    }
  } else {
    // both are applications
    bool propagateNeeded = false;

    Debug("cc") << "CC        lhs and rhs both apps" << std::endl;

    { // first go forward, like one application case
      Node ap = buildRepresentativesOfApply(s);

      Debug("cc") << "CC1rewrLHS op_and_args_a == " << t << std::endl;
      Debug("cc") << "CC1ap is   " << ap << std::endl;

      TNode l = lookup(ap);
      Debug("cc") << "CC1lookup(ap): " << l << std::endl;
      if(!l.isNull()) {
        d_pending.push_back(NodeManager::currentNM()->mkNode(kind::TUPLE, eq, l));
        propagateNeeded = true;
      } else {
        Debug("cc") << "CC1lookup(ap) setting to " << eq << std::endl;
        setLookup(ap, eq);
        for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
          appendToUseList(*i, eq);
        }
      }
    }

    if(s != t) { // then go backward, symmetrically
      Node ap = buildRepresentativesOfApply(t);

      Debug("cc") << "CC2rewrRHS " << s << " == op_and_args_a" << std::endl;
      Debug("cc") << "CC2ap is   " << ap << std::endl;

      TNode l = lookup(ap);
      Debug("cc") << "CC2lookup(ap): " << l << std::endl;
      if(!l.isNull()) {
        d_pending.push_back(NodeManager::currentNM()->mkNode(kind::TUPLE, eq, l));
        propagateNeeded = true;
      } else {
        Debug("cc") << "CC2lookup(ap) setting to " << eq << std::endl;
        setLookup(ap, eq);
        for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
          appendToUseList(*i, eq);
        }
      }
    }

    if(propagateNeeded) {
      propagate();
    }
  }
}/* CongruenceClosure<OutputChannel>::addEquality(TNode eq) */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::buildRepresentativesOfApply(TNode apply)
  throw(AssertionException) {
  Assert(apply.getKind() == kind::APPLY_UF);
  NodeBuilder<> argspb(kind::TUPLE);
  argspb << find(apply.getOperator());
  for(TNode::iterator i = apply.begin(); i != apply.end(); ++i) {
    argspb << find(*i);
  }
  return argspb;
}/* CongruenceClosure<OutputChannel>::addEquality(TNode eq) */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::propagate() {
  while(!d_pending.empty()) {
    Node e = d_pending.front();
    d_pending.pop_front();

    TNode a, b;
    if(e.getKind() == kind::EQUAL) {
      // e is an equality a = b (for consts a, b)

      a = e[0];
      b = e[1];

      Debug("cc") << "propagate equality: " << a << " == " << b << std::endl;
    } else {
      // e is a tuple ( apply f A... = a , apply f B... = b )

      Assert(e.getKind() == kind::TUPLE);
      Assert(e[0].getKind() == kind::EQUAL);
      Assert(e[1].getKind() == kind::EQUAL);

      a = e[0][1];
      b = e[1][1];

      Debug("cc") << "propagate tuple: ( " << a << " , " << b << " )"
                  << std::endl;
    }

    Debug("cc") << "=====at start=====" << std::endl
                << "a          :" << a << std::endl
                << "NORMALIZE a:" << normalize(a) << std::endl
                << "b          :" << b << std::endl
                << "NORMALIZE b:" << normalize(b) << std::endl
                << "alreadyCongruent?:" << areCongruent(a,b) << std::endl;

    TNode ap = find(a), bp = find(b);
    if(ap != bp) {

      Debug("cc") << "EC[a] == " << ap << std::endl
                  << "EC[b] == " << bp << std::endl;

      // w.l.o.g., |classList ap| <= |classList bp|

      context::CDList<Node>* cl_ap_tmp = d_classList[ap];
      context::CDList<Node>* cl_bp_tmp = d_classList[bp];
      unsigned sizeA = (cl_ap_tmp == NULL ? 0 : cl_ap_tmp->size());
      unsigned sizeB = (cl_bp_tmp == NULL ? 0 : cl_bp_tmp->size());
      Debug("cc") << "sizeA == " << sizeA << "  sizeB == " << sizeB << std::endl;
      if(sizeA > sizeB) {
        Debug("cc") << "swapping..\n";
        TNode tmp = ap; ap = bp; bp = tmp;
        tmp = a; a = b; b = tmp;
      }

      const context::CDList<Node>* cl = d_classList[ap];
      context::CDList<Node>*& cl_bp = d_classList[bp];

      if(cl_bp == NULL) {
        cl_bp = new(d_context->getCMM()) context::CDList<Node>(d_context, true);
        Debug("cc") << "CC in prop alloc classlist for " << bp << std::endl;
      }
      // we don't store 'ap' in its own class list; so process it here
      merge(ap, bp);
      cl_bp->push_back(ap);
      if(cl != NULL) {
        for(context::CDList<Node>::const_iterator i = cl->begin();
            i != cl->end();
            ++i) {
          TNode c = *i;
          merge(c, bp);
          // move c from classList(ap) to classlist(bp);
          //i = cl.erase(i);// FIXME do we need to?
          cl_bp->push_back(c);
        }
      }

      context::CDList<Node>* ul = d_useList[ap];
      Debug("cc") << "CC in prop go through useList of " << ap << std::endl;
      if(ul != NULL) {
        //for( f(c1,c2)=c in UseList(ap) )
        for(context::CDList<Node>::const_iterator i = ul->begin();
            i != ul->end();
            ++i) {
          TNode eq = *i;
          Debug("cc") << "CC  -- useList: " << eq << std::endl;
          Assert(eq.getKind() == kind::EQUAL);
          Assert(eq[0].getKind() == kind::APPLY_UF);

          // if lookup(c1',c2') is some f(d1,d2)=d then
          Node cp = buildRepresentativesOfApply(eq[0]);
          TNode n = lookup(cp);

          Debug("cc") << "CC     -- c' is " << cp << std::endl;

          if(!n.isNull()) {
            Debug("cc") << "CC     -- lookup(c') is " << n << std::endl;
            // add (f(c1,c2)=c,f(d1,d2)=d) to pending
            Node tuple = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, n);
            d_pending.push_back(tuple);
            // remove f(c1,c2)=c from UseList(ap)
            Debug("cc") << "supposed to remove " << eq << std::endl
                        << "  from UseList of " << ap << std::endl;
            //i = ul.erase(i);// FIXME do we need to?
          } else {
            Debug("cc") << "CC     -- lookup(c') is null" << std::endl;
            // set lookup(c1',c2') to f(c1,c2)=c
            setLookup(cp, eq);
            // move f(c1,c2)=c from UseList(ap) to UseList(b')
            //i = ul.erase(i);// FIXME do we need to remove from UseList(ap) ?
            cl_bp->push_back(eq);
          }
        }
      }
      Debug("cc") << "CC in prop done with useList of " << ap << std::endl;
    } else {
      Debug("cc") << "ECs the same ( == " << ap << "), do nothing."
                  << std::endl;
    }

    Debug("cc") << "=====at end=====" << std::endl
                << "a          :" << a << std::endl
                << "NORMALIZE a:" << normalize(a) << std::endl
                << "b          :" << b << std::endl
                << "NORMALIZE b:" << normalize(b) << std::endl
                << "alreadyCongruent?:" << areCongruent(a,b) << std::endl;
    Assert(areCongruent(a, b));
  }
}/* CongruenceClosure<OutputChannel>::propagate() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::merge(TNode ec1, TNode ec2) {
  Debug("cc") << "  -- merging " << ec1
              << (d_careSet.find(ec1) == d_careSet.end() ?
                  " -- NOT in care set" : " -- IN CARE SET") << std::endl
              << "         and " << ec2
              << (d_careSet.find(ec2) == d_careSet.end() ?
                  " -- NOT in care set" : " -- IN CARE SET") << std::endl;

  Assert(ec1 != ec2);
  Assert(find(ec1) == ec1);
  Assert(find(ec2) == ec2);

  d_representative[ec1] = ec2;
  if(d_careSet.find(ec1) != d_careSet.end()) {
    d_careSet.insert(ec2);
    d_out->merge(ec1, ec2);
  }
}/* CongruenceClosure<OutputChannel>::merge(TNode ec1, TNode ec2) */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::normalize(TNode t)
  throw(AssertionException) {
  if(t.getKind() == kind::APPLY_UF) {
    NodeBuilder<> ab(kind::TUPLE), apb(kind::TUPLE);
    TNode op = t.getOperator();
    ab << op;
    apb << normalize(op);
    bool allConstants = (op.getKind() != kind::APPLY_UF);
    for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
      TNode c = *i;
      ab << c;
      Node n = normalize(c);
      apb << n;
      allConstants = allConstants && (n.getKind() != kind::APPLY_UF);
    }

    Node a = ab, ap = apb;

    Node theLookup = Node::null();
    if(allConstants) {
      theLookup = lookup(ap);
    }
    if(allConstants && !theLookup.isNull()) {
      Assert(theLookup.getKind() == kind::EQUAL);
      Assert(theLookup[0].getKind() == kind::APPLY_UF);
      Debug("cc") << "n[[" << t << "]]theLookup is " << theLookup << std::endl;
      return find(theLookup[1]);
    } else {
      NodeBuilder<> fa(kind::APPLY_UF);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        fa << *i;
        Debug("cc") << "n[[" << t << "]]it :: " << *i << std::endl;
      }
      return Node(fa);
    }
  } else {
    return find(t);
  }
}/* CongruenceClosure<OutputChannel>::normalize(TNode t) */

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__CONGRUENCE_CLOSURE_H */

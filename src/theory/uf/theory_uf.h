/*********************                                                        */
/*! \file theory_uf.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is a basic implementation of the Theory of Uninterpreted Functions
 ** with Equality.
 **
 ** This is a basic implementation of the Theory of Uninterpreted Functions
 ** with Equality.  It is based on the Nelson-Oppen algorithm given in
 ** "Fast Decision Procedures Based on Congruence Closure"
 **  (http://portal.acm.org/ft_gateway.cfm?id=322198&type=pdf)
 ** This has been extended to work in a context-dependent way.
 ** This interacts heavily with the data-structures given in ecdata.h .
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__THEORY_UF_H
#define __CVC4__THEORY__UF__THEORY_UF_H

#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/theory.h"

#include "context/context.h"
#include "context/cdo.h"
#include "context/cdlist.h"
#include "util/congruence_closure.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUF : public Theory {

private:

  class CongruenceChannel {
    TheoryUF* d_uf;

  public:
    CongruenceChannel(TheoryUF* uf) : d_uf(uf) {}
    void notifyCongruent(TNode a, TNode b) {
      d_uf->notifyCongruent(a, b);
    }
  };/* class CongruenceChannel */
  friend class CongruenceChannel;

  /**
   * List of all of the non-negated literals from the assertion queue.
   * This is used only for conflict generation.
   * This differs from pending as the program generates new equalities that
   * are not in this list.
   * This will probably be phased out in future version.
   */
  context::CDList<Node> d_assertions;

  /**
   * Our channel connected to the congruence closure module.
   */
  CongruenceChannel d_ccChannel;

  /**
   * Instance of the congruence closure module.
   */
  CongruenceClosure<CongruenceChannel> d_cc;

  /** List of all disequalities this theory has seen. */
  context::CDList<Node> d_disequality;

  /**
   * List of all of the terms that are registered in the current context.
   * When registerTerm is called on a term we want to guarentee that there
   * is a hard link to the term for the duration of the context in which
   * register term is called.
   * This invariant is enough for us to use soft links where we want is the
   * current implementation as well as making ECAttr() not context dependent.
   * Soft links used both in ECData, and Link.
   */
  context::CDList<Node> d_registered;

public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUF(int id, context::Context* c, OutputChannel& out);

  /** Destructor for the TheoryUF object. */
  ~TheoryUF();

  /**
   * Registers a previously unseen [in this context] node n.
   * For TheoryUF, this sets up and maintains invaraints about
   * equivalence class data-structures.
   *
   * Overloads a void registerTerm(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void registerTerm(TNode n);

  /**
   * Currently this does nothing.
   *
   * Overloads a void preRegisterTerm(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void preRegisterTerm(TNode n);

  /**
   * Checks whether the set of literals provided to the theory is consistent.
   *
   * If this is called at any effort level, it computes the congruence closure
   * of all of the positive literals in the context.
   *
   * If this is called at full effort it checks if any of the negative literals
   * are inconsistent with the congruence closure.
   *
   * Overloads  void check(Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void check(Effort level);

  /**
   * Rewrites a node in the theory of uninterpreted functions.
   * This is fairly basic and only ensures that atoms that are
   * unsatisfiable or a valid are rewritten to false or true respectively.
   */
  RewriteResponse postRewrite(TNode n, bool topLevel);

  /**
   * Propagates theory literals.
   *
   * Overloads void propagate(Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void propagate(Effort level);

  /**
   * Explains a previously reported conflict. Currently does nothing.
   *
   * Overloads void explain(TNode n, Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void explain(TNode n, Effort level) {}

  std::string identify() const { return std::string("TheoryUF"); }

private:

  /** Constructs a conflict from an inconsistent disequality. */
  Node constructConflict(TNode diseq);

  /**
   * Receives a notification from the congruence closure module that
   * two nodes have been merged into the same congruence class.
   */
  void notifyCongruent(TNode a, TNode b);

};/* class TheoryUF */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_H */

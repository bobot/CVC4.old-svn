/*********************                                                        */
/*! \file output_channel.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory output channel interface
 **
 ** The theory output channel interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__OUTPUT_CHANNEL_H
#define __CVC4__THEORY__OUTPUT_CHANNEL_H

#include "util/Assert.h"
#include "theory/interrupted.h"

namespace CVC4 {
namespace theory {

/**
 * Generic "theory output channel" interface.
 */
class OutputChannel {
  /** Disallow copying: private constructor */
  OutputChannel(const OutputChannel&) CVC4_UNDEFINED;

  /** Disallow assignment: private operator=() */
  OutputChannel& operator=(const OutputChannel&) CVC4_UNDEFINED;

public:

  /**
   * Construct an OutputChannel.
   */
  OutputChannel() {
  }

  /**
   * Destructs an OutputChannel.  This implementation does nothing,
   * but we need a virtual destructor for safety in case subclasses
   * have a destructor.
   */
  virtual ~OutputChannel() {
  }

  /**
   * Notify the OutputChannel that a new fact has been received by
   * the theory.
   */
  virtual void newFact(TNode n) { }

  /**
   * With safePoint(), the theory signals that it is at a safe point
   * and can be interrupted.
   */
  virtual void safePoint() throw(Interrupted, AssertionException) {
  }

  /**
   * Indicate a theory conflict has arisen.
   *
   * @param n - a conflict at the current decision level.  This should
   * be an AND-kinded node of literals that are TRUE in the current
   * assignment and are in conflict (i.e., at least one must be
   * assigned false), or else a literal by itself (in the case of a
   * unit conflict) which is assigned TRUE (and T-conflicting) in the
   * current assignment.
   *
   * @param safe - whether it is safe to be interrupted
   */
  virtual void conflict(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) = 0;

  /**
   * Propagate a theory literal.
   *
   * @param n - a theory consequence at the current decision level
   * @param safe - whether it is safe to be interrupted
   */
  virtual void propagate(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) = 0;

  /**
   * Tell the core that a valid theory lemma at decision level 0 has
   * been detected.  (This requests a split.)
   *
   * @param n - a theory lemma valid at decision level 0
   * @param safe - whether it is safe to be interrupted
   */
  virtual void lemma(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) = 0;

  /**
   * Request a split on a new theory atom.  This is equivalent to
   * calling lemma({OR n (NOT n)}).
   *
   * @param n - a theory atom; must be of Boolean type
   * @param safe - whether it is safe to be interrupted
   */
  void split(TNode n, bool safe = false)
    throw(Interrupted, TypeCheckingExceptionPrivate, AssertionException) {
    lemma(n.orNode(n.notNode()));
  }

  /**
   * If a decision is made on n, it must be in the phase specified.
   *
   * @param n - a theory atom with a SAT literal assigned; must have
   * been pre-registered
   * @param phase - the phase to decide on n
   * @param safe - whether it is safe to be interrupted
   */
  virtual void requirePhase(TNode n, bool phase, bool safe = false)
    throw(Interrupted, TypeCheckingExceptionPrivate, AssertionException) = 0;

  /**
   * Tell the SAT solver that "decision" can never be decided until
   * "depends" has been assigned.  Both must have a SAT literal.
   *
   * @param depends - the literal that must be assigned
   * @param decision - the literal that cannot be decided until "depends" 
   * has an assignment
   * @param safe - whether it is safe to be interrupted
   */
  virtual void dependentDecision(TNode depends, TNode decision, bool safe = false)
    throw(Interrupted, TypeCheckingExceptionPrivate, AssertionException) = 0;

  /**
   * Flips the most recent unflipped decision to the other phase and
   * returns true.  If all decisions have been flipped, the root
   * decision is re-flipped and flipDecision() returns false.  If no
   * decisions (flipped nor unflipped) are on the decision stack, the
   * state is not affected and flipDecision() returns false.
   *
   * For example, if l1, l2, and l3 are all decision literals, and
   * have been decided in positive phase, a series of flipDecision()
   * calls has the following effects:
   *
   * l1 l2 l3 <br/>
   * l1 l2 ~l3 <br/>
   * l1 ~l2 <br/>
   * ~l1 <br/>
   * l1 (and flipDecision() returns false)
   *
   * Naturally, flipDecision() might be interleaved with search.  For example:
   *
   * l1 l2 l3 <br/>
   * flipDecision() <br/>
   * l1 l2 ~l3 <br/>
   * flipDecision() <br/>
   * l1 ~l2 <br/>
   * SAT decides l3 <br/>
   * l1 ~l2 l3 <br/>
   * flipDecision() <br/>
   * l1 ~l2 ~l3 <br/>
   * flipDecision() <br/>
   * ~l1 <br/>
   * SAT decides l2 <br/>
   * ~l1 l2 <br/>
   * flipDecision() <br/>
   * ~l1 ~l2 <br/>
   * flipDecision() returns FALSE<br/>
   * l1
   *
   * @param safe - whether it is safe to be interrupted
   * @return true if a decision was flipped; false if no decision
   * could be flipped, or if the root decision was re-flipped
   */
  virtual bool flipDecision(bool safe = false)
    throw(Interrupted, TypeCheckingExceptionPrivate, AssertionException) = 0;

  /**
   * Provide an explanation in response to an explanation request.
   *
   * @param n - an explanation
   * @param safe - whether it is safe to be interrupted
   */
  virtual void explanation(TNode n, bool safe = false)
    throw(Interrupted, AssertionException) = 0;

  /**
   * Notification from a theory that it realizes it is incomplete at
   * this context level.  If SAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setIncomplete()
    throw(Interrupted, AssertionException) = 0;

};/* class OutputChannel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__OUTPUT_CHANNEL_H */

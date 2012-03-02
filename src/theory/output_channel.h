/*********************                                                        */
/*! \file output_channel.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): taking, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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
 * A LemmaStatus, returned from OutputChannel::lemma(), provides information
 * about the lemma added.  In particular, it contains the T-rewritten lemma
 * for inspection and the user-level at which the lemma will reside.
 */
class LemmaStatus {
  Node d_rewrittenLemma;
  unsigned d_level;

public:
  LemmaStatus(TNode rewrittenLemma, unsigned level) :
    d_rewrittenLemma(rewrittenLemma),
    d_level(level) {
  }

  /** Get the T-rewritten form of the lemma. */
  TNode getRewrittenLemma() const throw() { return d_rewrittenLemma; }

  /**
   * Get the user-level at which the lemma resides.  After this user level
   * is popped, the lemma is un-asserted from the SAT layer.  This level
   * will be 0 if the lemma didn't reach the SAT layer at all.
   */
  unsigned getLevel() const throw() { return d_level; }

};/* class LemmaStatus */

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
   */
  virtual void conflict(TNode n) throw(AssertionException) = 0;

  /**
   * Propagate a theory literal.
   *
   * @param n - a theory consequence at the current decision level
   */
  virtual void propagate(TNode n) throw(AssertionException) = 0;

  /**
   * Request that the core make a decision on this atom.  The decision
   * will be "as soon as possible," but due to other propagation and
   * conflict-detection work going on internally, the request is queued
   * up and may be behind other such requests.  The request will be
   * silently dropped if the atom has a definite value at the point the
   * request would be serviced.  This request is also context-dependent
   * on the search context, meaning that it will be dropped completely
   * if a conflict is found before it is serviced.  Each request will only
   * be serviced a single time, even though the atom may become undefined
   * due to backtracking.
   *
   * @param atom the atom to decide upon (or the negation of an
   * atom---the decision will be in the phase provided); must be
   * associated to a SAT literal.
   */
  virtual void propagateAsDecision(TNode n) throw(AssertionException) = 0;

  /**
   * Tell the core that a valid theory lemma at decision level 0 has
   * been detected.  (This requests a split.)
   *
   * @param n - a theory lemma valid at decision level 0
   * @param removable - whether the lemma can be removed at any point
   * @return the "status" of the lemma, including user level at which
   * the lemma resides; the lemma will be removed when this user level pops
   */
  virtual LemmaStatus lemma(TNode n, bool removable = false)
    throw(TypeCheckingExceptionPrivate, AssertionException) = 0;

  /**
   * Request a split on a new theory atom.  This is equivalent to
   * calling lemma({OR n (NOT n)}).
   *
   * @param n - a theory atom; must be of Boolean type
   */
  LemmaStatus split(TNode n)
    throw(TypeCheckingExceptionPrivate, AssertionException) {
    return lemma(n.orNode(n.notNode()));
  }

  /**
   * If a decision is made on n, it must be in the phase specified.
   * Note that this is enforced *globally*, i.e., it is completely
   * context-INdependent.  If you ever requirePhase() on a literal,
   * it is phase-locked forever and ever.  If it is to ever have the
   * other phase as its assignment, it will be because it has been
   * propagated that way (or it's a unit, at decision level 0).
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
   * Flip the decision "lit", similar to the 0-ary flipDecision() function
   * described above.  Only ever flips "lit" though, leaving it marked as
   * "flipped"---this function never proceeds further down-stack.  If the
   * decision was already flipped, it is flipped again.  Throws an exception
   * if "lit" is not a decision literal in the SAT solver.  Note that "lit" may
   * be specified in either phase, though.  That is, if "lit" is a SAT decision,
   * flipDecision(lit) and flipDecision(negation-of-lit) are the same.
   */
  virtual void flipDecision(Node lit, bool safe = false)
    throw(Interrupted, TypeCheckingExceptionPrivate, AssertionException) = 0;

  /**
   * Flip the decision at level "level", similar to the 0-ary flipDecision()
   * function described above.  Only ever flips the decision at the given level
   * though, leaving it marked as "flipped"---this function never proceeds further
   * down-stack.  If the decision at the given level was already flipped, it is
   * flipped again.  Throws an exception if level is 0 or greater than the current
   * decision level.
   */
  virtual void flipDecision(unsigned level, bool safe = false)
    throw(Interrupted, TypeCheckingExceptionPrivate, AssertionException) = 0;

  /**
   * Notification from a theory that it realizes it is incomplete at
   * this context level.  If SAT is later determined by the
   * TheoryEngine, it should actually return an UNKNOWN result.
   */
  virtual void setIncomplete() throw(AssertionException) = 0;

  /**
   * "Spend" a "resource."  The meaning is specific to the context in
   * which the theory is operating, and may even be ignored.  The
   * intended meaning is that if the user has set a limit on the "units
   * of resource" that can be expended in a search, and that limit is
   * exceeded, then the search is terminated.  Note that the check for
   * termination occurs in the main search loop, so while theories
   * should call OutputChannel::spendResource() during particularly
   * long-running operations, they cannot rely on resource() to break
   * out of infinite or intractable computations.
   */
  virtual void spendResource() throw() {
  }

};/* class OutputChannel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__OUTPUT_CHANNEL_H */

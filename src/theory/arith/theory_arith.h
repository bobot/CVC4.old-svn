/*********************                                                        */
/*! \file theory_arith.h
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
 ** \brief Arithmetic theory.
 **
 ** Arithmetic theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__THEORY_ARITH_H
#define __CVC4__THEORY__ARITH__THEORY_ARITH_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "expr/node.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/basic.h"
#include "theory/arith/arith_activity.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/next_arith_rewriter.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/arith_propagator.h"

#include "util/stats.h"

#include <vector>
#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * Implementation of QF_LRA.
 * Based upon:
 * http://research.microsoft.com/en-us/um/people/leonardo/cav06.pdf
 */
class TheoryArith : public Theory {
private:

  /* TODO Everything in the chopping block needs to be killed. */
  /* Chopping block begins */

  std::vector<Node> d_splits;
  //This stores the eager splits sent out of the theory.

  /* Chopping block ends */

  std::vector<Node> d_variables;

  /**
   * Priority Queue of the basic variables that may be inconsistent.
   *
   * This is required to contain at least 1 instance of every inconsistent
   * basic variable. This is only required to be a superset though so its
   * contents must be checked to still be basic and inconsistent.
   */
  std::priority_queue<ArithVar> d_possiblyInconsistent;

  /** Stores system wide constants to avoid unnessecary reconstruction. */
  ArithConstants d_constants;

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   */
  ArithPartialModel d_partialModel;

  IsBasicManager d_basicManager;
  ActivityMonitor d_activityMonitor;

  /**
   * List of all of the inequalities asserted in the current context.
   */
  context::CDList<Node> d_diseq;

  /**
   * The tableau for all of the constraints seen thus far in the system.
   */
  Tableau d_tableau;

  /**
   * The rewriter module for arithmetic.
   */
  NextArithRewriter d_nextRewriter;

  ArithUnatePropagator d_propagator;

public:
  TheoryArith(int id, context::Context* c, OutputChannel& out);
  ~TheoryArith();

  /**
   * Rewriting optimizations.
   */
  RewriteResponse preRewrite(TNode n, bool topLevel);

  /**
   * Plug in old rewrite to the new (pre,post)rewrite interface.
   */
  RewriteResponse postRewrite(TNode n, bool topLevel) {
    return d_nextRewriter.postRewrite(n);
  }

  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n);

  /** CD setup for a node. Currently does nothing. */
  void registerTerm(TNode n);

  void check(Effort e);
  void propagate(Effort e);
  void explain(TNode n, Effort e);

  void shutdown(){ }

  std::string identify() const { return std::string("TheoryArith"); }

private:

  bool isTheoryLeaf(TNode x) const;

  /**
   * Assert*(n, orig) takes an bound n that is implied by orig.
   * and asserts that as a new bound if it is tighter than the current bound
   * and updates the value of a basic variable if needed.
   * If this new bound is in conflict with the other bound,
   * a conflict is created and asserted to the output channel.
   *
   * orig must be an atom in the SAT solver so that it can be used for
   * conflict analysis.
   *
   * n is of the form (x =?= c) where x is a variable,
   * c is a constant and =?= is either LT, LEQ, EQ, GEQ, or GT.
   *
   * returns true if a conflict was asserted.
   */
  bool AssertLower(TNode n, TNode orig);
  bool AssertUpper(TNode n, TNode orig);

  bool AssertEquality(TNode n, TNode orig);

  /**
   * Updates the assignment of a nonbasic variable x_i to v.
   * Also updates the assignment of basic variables accordingly.
   */
  void update(ArithVar x_i, DeltaRational& v);

  /**
   * Updates the value of a basic variable x_i to v,
   * and then pivots x_i with the nonbasic variable in its row x_j.
   * Updates the assignment of the other basic variables accordingly.
   */
  void pivotAndUpdate(ArithVar x_i, ArithVar x_j, DeltaRational& v);

  /**
   * Tries to update the assignments of variables such that all of the
   * assignments are consistent with their bounds.
   *
   * This is done by searching through the tableau.
   * If all of the variables can be made consistent with their bounds
   * Node::null() is returned. Otherwise a minimized conflict is returned.
   *
   * If a conflict is found, changes to the assignments need to be reverted.
   *
   * Tableau pivoting is performed so variables may switch from being basic to
   * nonbasic and vice versa.
   *
   * Corresponds to the "check()" procedure in [Cav06].
   */
  Node updateInconsistentVars();

  /**
   * Given the basic variable x_i,
   * this function finds the smallest nonbasic variable x_j in the row of x_i
   * in the tableau that can "take up the slack" to let x_i satisfy its bounds.
   * This returns TNode::null() if none exists.
   *
   * More formally one of the following conditions must be satisfied:
   * -  above && a_ij < 0 && assignment(x_j) < upperbound(x_j)
   * -  above && a_ij > 0 && assignment(x_j) > lowerbound(x_j)
   * - !above && a_ij > 0 && assignment(x_j) < upperbound(x_j)
   * - !above && a_ij < 0 && assignment(x_j) > lowerbound(x_j)
   */
  template <bool above>  ArithVar selectSlack(ArithVar x_i);

  ArithVar selectSlackBelow(ArithVar x_i) { return selectSlack<false>(x_i); }
  ArithVar selectSlackAbove(ArithVar x_i) { return selectSlack<true>(x_i);  }

  /**
   * Returns the smallest basic variable whose assignment is not consistent
   * with its upper and lower bounds.
   */
  ArithVar selectSmallestInconsistentVar();

  /**
   * Given a non-basic variable that is know to not be updatable
   * to a consistent value, construct and return a conflict.
   * Follows section 4.2 in the CAV06 paper.
   */
  Node generateConflictAbove(ArithVar conflictVar);
  Node generateConflictBelow(ArithVar conflictVar);


  /**
   * This requests a new unique ArithVar value for x.
   * This also does initial (not context dependent) set up for a variable,
   * except for setting up the initial.
   */
  ArithVar requestArithVar(TNode x, bool basic);

  /** Initial (not context dependent) sets up for a variable.*/
  void setupInitialValue(ArithVar x);

  /** Initial (not context dependent) sets up for a new slack variable.*/
  void setupSlack(TNode left);


  /** Computes the value of a row in the tableau using the current assignment.*/
  DeltaRational computeRowValueUsingAssignment(ArithVar x);

  /** Computes the value of a row in the tableau using the safe assignment.*/
  DeltaRational computeRowValueUsingSavedAssignment(ArithVar x);

  /** Checks to make sure the assignment is consistent with the tableau. */
  void checkTableau();

  /** Check to make sure all of the basic variables are within their bounds. */
  void checkBasicVariable(ArithVar basic);

  /**
   * Handles the case splitting for check() for a new assertion.
   * returns true if their is a conflict.
   */
  bool assertionCases(TNode original, TNode assertion);

  ArithVar findBasicRow(ArithVar variable);
  bool shouldEject(ArithVar var);
  void ejectInactiveVariables();
  void reinjectVariable(ArithVar x);

  //TODO get rid of this!
  Node simulatePreprocessing(TNode n);

  void asVectors(Polynomial& p,
                 std::vector<Rational>& coeffs,
                 std::vector<ArithVar>& variables) const;


  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statPivots, d_statUpdates, d_statAssertUpperConflicts;
    IntStat d_statAssertLowerConflicts, d_statUpdateConflicts;
    IntStat d_statUserVariables, d_statSlackVariables;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;


};/* class TheoryArith */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */

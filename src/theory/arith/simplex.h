/*********************                                                        */
/*! \file simplex.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): kshitij, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is an implementation of the Simplex Module for the Simplex for DPLL(T) decision procedure.
 **
 ** This implements the Simplex module for the Simpelx for DPLL(T) decision procedure.
 ** See the Simplex for DPLL(T) technical report for more background.(citation?)
 ** This shares with the theory a Tableau, and a PartialModel that:
 **  - satisfies the equalities in the Tableau, and
 **  - the assignment for the non-basic variables satisfies their bounds.
 ** This is required to either produce a conflict or satisifying PartialModel.
 ** Further, we require being told when a basic variable updates its value.
 **
 ** During the Simplex search we maintain a queue of variables.
 ** The queue is required to contain all of the basic variables that voilate their bounds.
 ** As elimination from the queue is more efficient to be done lazily,
 ** we do not maintain that the queue of variables needs to be only basic variables or only variables that satisfy their bounds.
 **
 ** The simplex procedure roughly follows Alberto's thesis. (citation?)
 ** There is one round of selecting using a heuristic pivoting rule. (See PreferenceFunction Documentation for the available options.)
 ** The non-basic variable is the one that appears in the fewest pivots. (Bruno says that Leonardo invented this first.)
 ** After this, Bland's pivot rule is invoked.
 **
 ** During this proccess, we periodically inspect the queue of variables to
 ** 1) remove now extraneous extries,
 ** 2) detect conflicts that are "waiting" on the queue but may not be detected by the current queue heuristics, and
 ** 3) detect multiple conflicts.
 **
 ** Conflicts are greedily slackened to use the weakest bounds that still produce the conflict.
 **
 ** Extra things tracked atm: (Subject to change at Tim's whims)
 ** - A superset of all of the newly pivoted variables.
 ** - A queue of additional conflicts that were discovered by Simplex.
 **   These are theory valid and are currently turned into lemmas
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__SIMPLEX_H
#define __CVC4__THEORY__ARITH__SIMPLEX_H

#include "theory/arith/arithvar.h"
#include "theory/arith/arith_priority_queue.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/matrix.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/linear_equality.h"

#include "context/cdlist.h"

#include "util/dense_map.h"
#include "options/options.h"
#include "util/statistics_registry.h"
#include "util/result.h"

#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

class SimplexDecisionProcedure {
private:
  ArithVar d_conflictVariable;
  DenseSet d_successes;

  /** Linear equality module. */
  LinearEqualityModule& d_linEq;

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   * Partial model matches that in LinearEqualityModule.
   */
  ArithPartialModel& d_partialModel;

  /**
   * Stores the linear equalities used by Simplex.
   * Tableau from the LinearEquality module.
   */
  Tableau& d_tableau;

  /** Contains a superset of the basic variables in violation of their bounds. */
  ArithPriorityQueue d_queue;

  /** Number of variables in the system. This is used for tuning heuristics. */
  ArithVar d_numVariables;

  /** This is the call back channel for Simplex to report conflicts. */
  NodeCallBack& d_conflictChannel;

  /** Maps a variable to how many times they have been used as a pivot in the simplex search. */
  DenseMultiset d_pivotsInRound;

  /** Stores to the DeltaRational constant 0. */
  DeltaRational d_DELTA_ZERO;

public:
  SimplexDecisionProcedure(LinearEqualityModule& linEq, NodeCallBack& conflictChannel);

  /**
   * This must be called when the value of a basic variable may now voilate one
   * of its bounds.
   */
  void updateBasic(ArithVar x){
    d_queue.enqueueIfInconsistent(x);
  }

  /**
   * Tries to update the assignments of variables such that all of the
   * assignments are consistent with their bounds.
   * This is done by a simplex search through the possible bases of the tableau.
   *
   * If all of the variables can be made consistent with their bounds
   * false is returned. Otherwise true is returned, and at least 1 conflict
   * was reported on the conflictCallback passed to the Module.
   *
   * Tableau pivoting is performed so variables may switch from being basic to
   * nonbasic and vice versa.
   *
   * Corresponds to the "check()" procedure in [Cav06].
   */
  Result::Sat findModel(bool exactResult);

private:

  /**
   * A PreferenceFunction takes a const ref to the SimplexDecisionProcedure,
   * and 2 ArithVar variables and returns one of the ArithVar variables potentially
   * using the internals of the SimplexDecisionProcedure.
   *
   * Both ArithVar must be non-basic in d_tableau.
   */
  typedef ArithVar (*PreferenceFunction)(const SimplexDecisionProcedure&, ArithVar, ArithVar);

  /**
   * minVarOrder is a PreferenceFunction for selecting the smaller of the 2 ArithVars.
   * This PreferenceFunction is used during the VarOrder stage of
   * findModel.
   */
  static ArithVar minVarOrder(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y);

  /**
   * minRowCount is a PreferenceFunction for selecting the variable with the smaller
   * row count in the tableau.
   *
   * This is a heuristic rule and should not be used
   * during the VarOrder stage of findModel.
   */
  static ArithVar minColLength(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y);

  /**
   * minBoundAndRowCount is a PreferenceFunction for preferring a variable
   * without an asserted bound over variables with an asserted bound.
   * If both have bounds or both do not have bounds,
   * the rule falls back to minRowCount(...).
   *
   * This is a heuristic rule and should not be used
   * during the VarOrder stage of findModel.
   */
  static ArithVar minBoundAndRowCount(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y);




private:
  bool searchForFeasibleSolution(uint32_t maxIterations);

  enum SearchPeriod {BeforeDiffSearch, DuringDiffSearch, AfterDiffSearch, DuringVarOrderSearch, AfterVarOrderSearch};

  bool findConflictOnTheQueue(SearchPeriod period);


  /**
   * Given the basic variable x_i,
   * this function finds the smallest nonbasic variable x_j in the row of x_i
   * in the tableau that can "take up the slack" to let x_i satisfy its bounds.
   * This returns ARITHVAR_SENTINEL if none exists.
   *
   * More formally one of the following conditions must be satisfied:
   * -  lowerBound && a_ij < 0 && assignment(x_j) < upperbound(x_j)
   * -  lowerBound && a_ij > 0 && assignment(x_j) > lowerbound(x_j)
   * - !lowerBound && a_ij > 0 && assignment(x_j) < upperbound(x_j)
   * - !lowerBound && a_ij < 0 && assignment(x_j) > lowerbound(x_j)
   *
   */
  template <bool lowerBound>  ArithVar selectSlack(ArithVar x_i, PreferenceFunction pf);
  ArithVar selectSlackLowerBound(ArithVar x_i, PreferenceFunction pf = minVarOrder) {
    return selectSlack<true>(x_i, pf);
  }
  ArithVar selectSlackUpperBound(ArithVar x_i, PreferenceFunction pf = minVarOrder) {
    return selectSlack<false>(x_i, pf);
  }
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
  Node generateConflictAboveUpperBound(ArithVar conflictVar);
  Node generateConflictBelowLowerBound(ArithVar conflictVar);

public:
  void increaseMax() {d_numVariables++;}


  void clearQueue() {
    d_queue.clear();
  }


  bool debugIsInCollectionQueue(ArithVar var) const{
    Assert(d_queue.inCollectionMode());
    return d_queue.collectionModeContains(var);
  }

  void reduceQueue(){
    d_queue.reduce();
  }

  ArithPriorityQueue::const_iterator queueBegin() const{
    return d_queue.begin();
  }

  ArithPriorityQueue::const_iterator queueEnd() const{
    return d_queue.end();
  }

private:

  /** Reports a conflict to on the output channel. */
  void reportConflict(Node conflict){
    d_conflictChannel(conflict);
    ++(d_statistics.d_simplexConflicts);
  }

  template <bool above>
  inline bool isAcceptableSlack(int sgn, ArithVar nonbasic){
    return
      ( above && sgn < 0 && d_partialModel.strictlyBelowUpperBound(nonbasic)) ||
      ( above && sgn > 0 && d_partialModel.strictlyAboveLowerBound(nonbasic)) ||
      (!above && sgn > 0 && d_partialModel.strictlyBelowUpperBound(nonbasic)) ||
      (!above && sgn < 0 && d_partialModel.strictlyAboveLowerBound(nonbasic));
  }

  /**
   * Checks a basic variable, b, to see if it is in conflict.
   * If a conflict is discovered a node summarizing the conflict is returned.
   * Otherwise, Node::null() is returned.
   */
  Node checkBasicForConflict(ArithVar b);

  Node weakenConflict(bool aboveUpper, ArithVar basicVar);
  Constraint weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v, const Rational& coeff, bool& anyWeakening, ArithVar basic);



  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statUpdateConflicts;

    TimerStat d_findConflictOnTheQueueTime;

    IntStat d_attemptBeforeDiffSearch, d_successBeforeDiffSearch;
    IntStat d_attemptAfterDiffSearch, d_successAfterDiffSearch;
    IntStat d_attemptDuringDiffSearch, d_successDuringDiffSearch;
    IntStat d_attemptDuringVarOrderSearch, d_successDuringVarOrderSearch;
    IntStat d_attemptAfterVarOrderSearch, d_successAfterVarOrderSearch;

    IntStat d_weakeningAttempts, d_weakeningSuccesses, d_weakenings;
    TimerStat d_weakenTime;


    IntStat d_simplexConflicts;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};/* class SimplexDecisionProcedure */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__SIMPLEX_H */


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
#include "context/cdset.h"
#include "expr/node.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_dense_set.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_simp.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/unate_propagator.h"
#include "theory/arith/simplex.h"
#include "theory/arith/disjoint_set_forest.h"

#include "util/stats.h"

#include <vector>
#include <set>
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

  std::vector<Node> d_splits;
  //This stores the eager splits sent out of the theory.

  std::vector<Node> d_variables;
  //This stores the variables sent to the theory.

  std::set<Node> d_simplifiedNegatations;
  //This stores the set of simplified negated atoms
  //The purpose of this set is to ensure attributes cannot be deleted,
  //and to prevent nodes from being registered a second time.

  DisjointSetForest d_preregisteredAtoms;
  /* This stores the set of atoms that have been preregistered with the theory.
   * Only atoms in this set can be returned by the theory in conflicts,
   * and propagated.
   * Two atoms are in the same equivalence class iff their rewritten,
   * and simplified form is the same thing.
   */

  /** Module for handling simplifications. */
  ArithSimp d_simplifier;

  TimeStamp d_currentTime;


  std::queue<Node> d_lemmasQueue;


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

  ArithVarDenseSet d_basicManager;
  ActivityMonitor d_activityMonitor;

  /**
   * List of all of the inequalities asserted in the current context.
   */
  context::CDSet<Node, NodeHashFunction> d_diseq;

  /**
   * The tableau for all of the constraints seen thus far in the system.
   */
  Tableau d_tableau;

  ArithUnatePropagator d_propagator;
  SimplexDecisionProcedure d_simplex;

public:
  TheoryArith(context::Context* c, OutputChannel& out);
  ~TheoryArith();

  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n);

  /** CD setup for a node. Currently does nothing. */
  void registerTerm(TNode n);

  void check(Effort e);

  void propagate(Effort e){
    while(!d_lemmasQueue.empty()){
      d_out->lemma(d_lemmasQueue.front());
      d_lemmasQueue.pop();
    }
  }
  void explain(TNode n) {} //Currently unused
  void notifyRestart() { resetInternalState(); }

  void notifyEq(TNode lhs, TNode rhs);

  Node getValue(TNode n, TheoryEngine* engine);

  void shutdown(){ }

  void presolve(){
    static int callCount = 0;
    Debug("arith::presolve") << "TheoryArith::presolve #"
                             << (callCount++) << endl;
    check(FULL_EFFORT);
  }

  std::string identify() const { return std::string("TheoryArith"); }

private:

  ArithVar determineLeftVariable(TNode assertion, Kind simpleKind);


  /**
   * This requests a new unique ArithVar value for x.
   * This also does initial (not context dependent) set up for a variable,
   * except for setting up the initial.
   */
  ArithVar requestArithVar(TNode x, bool basic);

  /** Initial (not context dependent) sets up for a variable.*/
  void setupInitialValue(ArithVar x);

  /** Initial (not context dependent) sets up for a new slack variable.*/
  void setupSlack(Polynomial left);

  /** Lazily simplify and setup as necessary. */
  Node lazySimplifyAndSetup(TNode lit);

  /** Setup the literal, atom and monomial as needed. */
  void arithRegisterLit(TNode lit);
  void arithRegisterMonomial(Monomial m);


  /** Undoes registrations. */
  void resetInternalState();

  /** TimeStamp time */
  TimeStamp currentTimeStamp();
  void incCurrentTime();

  /** Returns true if the literal can be safely ignored. */
  bool ignore(Node lit);

  /**
   * Iterates over all of the disequalities, and splits it (using a lemma)
   * if it is not satisfied.
   */
  void splitDisequalities();

  /**
   * Handles the case splitting for check() for a new assertion.
   * returns true if their is a conflict.
   */
  bool assertionCases(TNode assertion);

  ArithVar findBasicRow(ArithVar variable);

  void asVectors(Polynomial& p,
                 std::vector<Rational>& coeffs,
                 std::vector<ArithVar>& variables) const;

  /** Debug printing of the assertions. */
  void debugPrintAssertions();

  /** Debug printing of the assertions. */
  void debugPrintModel();


  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statUserVariables, d_statSlackVariables;
    IntStat d_statDisequalitySplits;
    IntStat d_statDisequalityConflicts;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;


};/* class TheoryArith */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */

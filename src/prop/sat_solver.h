/*********************                                                        */
/*! \file sat_module.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: 
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** SAT Solver.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PROP__SAT_MODULE_H
#define __CVC4__PROP__SAT_MODULE_H

#include <string>
#include <stdint.h>
#include "util/options.h"
#include "util/stats.h"
#include "context/cdlist.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {
namespace prop {

class TheoryProxy; 

enum ObjectLifespan {
  SAT_CONTEXT_STRICT, // go away on next SAT context-pop
  SAT_CONTEXT_LENIENT, // can stick around after next SAT context-pop (e.g. clause cleanup)
  USER_CONTEXT_STRICT, // go away on next user-pop
  USER_CONTEXT_LENIENT // can stick around after next user-pop (e.g. clause cleanup or later user pop)
};/* enum ObjectLifespan */

class SatSolver {

public:  

  /** Virtual destructor */
  virtual ~SatSolver() { }

  /**
   * Assert a clause in the solver.  It has the lifespan given.
   */
  virtual void addClause(SatClause& clause, ObjectLifespan lifespan) = 0;

  /**
   * Create a new boolean variable in the solver.  Lifespan as given.
   * Notify TheoryProxy on any assignment to this variable iff
   * "notify" is true.
   */
  virtual SatVariable newVar(ObjectLifespan lifespan, bool notify = false) = 0;

  /**
   * "resource" is a virtual resource budget for solving.  The actual
   * amount of resource used is implementation-dependent (it could be,
   * for example, the number of conflicts).  If the solver exceeds
   * this limit, the Resource object will throw an exception.
   *
   * This cannot be called in a re-entrant fashion.
   */
  virtual SatValue solve(Resource& resource) = 0;

  /**
   * Interrupt the solver.
   */
  virtual void interrupt() = 0;

  /**
   * Call value() to get the value of a literal, if any.
   *
   * This interface function CAN be used in a reentrant fashion (i.e.,
   * when solve() is active).  After a solve() routine that results in
   * a "satisfiable" response, then this function returns the value of
   * the literal in the satisfying assignment that was found by the
   * solver.
   */
  virtual SatValue value(SatLiteral lit) = 0;

  /**
   * Same as adding a unit clause with lifespan USER_CONTEXT_STRICT;
   * this literal is considered an assumption for purposes of
   * getUnsatCore() and explainPropagation().
   */
  virtual void addAssumption(SatLiteral lit) = 0;

  /**
   * Explains why we are currently UNSAT (must be preceded by a
   * solve() call that returns UNSAT); this explanation is in terms of
   * assumptions only (as given by addAssumption()).
   */
  virtual void explainConflict(std::vector<SatLiteral>& assumptions) = 0; 

  /**
   * Explains why lit was assigned (it must be assigned TRUE); this
   * explanation is in terms of assumptions only (as given by
   * addAssumption()).
   */
  virtual void explainPropagation(SatLiteral lit, std::vector<SatLiteral>& assumptions) = 0;

  /**
   * Do BCP; return FALSE if conflict; TRUE if no conflict.
   *
   * This interface function cannot be used in a reentrant fashion
   * (i.e., when solve() is active).
   */
  virtual bool propagate() = 0;

};/* class SatSolver */

class SatSearchController {

  /** Virtual destructor */
  virtual ~SatSolver() { }

  /**
   * Get the current decision level.
   *
   * This interface function CAN be used in a reentrant fashion (i.e.,
   * when solve() is active).
   */
  virtual unsigned getCurrentDecisionLevel() const = 0;

  /**
   * Return the decision level at which var was assigned.  Var must be
   * assigned, or an exception is thrown.
   *
   * This interface function CAN be used in a reentrant fashion (i.e.,
   * when solve() is active).
   */
  virtual unsigned getDecisionLevel(SatVariable var) const = 0;

  /**
   * If "lit" is ever decided upon, it must be decided upon in the
   * phase given.  (It can be propagated in the opposite phase,
   * though.)
   */
  virtual void requirePhasedDecision(SatLiteral lit) = 0;

  /**
   * Flip the most recent, unflipped decision.
   */
  virtual bool flipDecision() = 0;

  /**
   * Should return TRUE if the solve() routine is going to exit
   * without another state change.
   */
  virtual bool isDone() = 0;

};/* class SatSearchController */

}/* prop namespace */

inline std::ostream& operator <<(std::ostream& out, prop::SatLiteral lit) {
  out << lit.toString();
  return out;
}

inline std::ostream& operator <<(std::ostream& out, const prop::SatClause& clause) {
  out << "clause:";
  for(unsigned i = 0; i < clause.size(); ++i) {
    out << " " << clause[i];
  }
  out << ";";
  return out;
}

inline std::ostream& operator <<(std::ostream& out, prop::SatValue val) {
  std::string str;
  switch(val) {
  case prop::SAT_VALUE_UNKNOWN:
    str = "_";
    break;
  case prop::SAT_VALUE_TRUE:
    str = "1";
    break;
  case prop::SAT_VALUE_FALSE:
    str = "0";
    break;
  default:
    str = "Error";
    break;
  }

  out << str;
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__PROP__SAT_MODULE_H */

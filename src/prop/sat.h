/*********************                                                        */
/** sat.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** SAT Solver.
 **/

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

#define __CVC4_USE_MINISAT

#ifdef __CVC4_USE_MINISAT

#include "util/options.h"
#include "prop/minisat/core/Solver.h"
#include "prop/minisat/core/SolverTypes.h"

namespace CVC4 {
namespace prop {

/** The solver we are using */
typedef minisat::Solver SatSolver;

/** Type of the SAT variables */
typedef minisat::Var SatVariable;

/** Type of the Sat literals */
typedef minisat::Lit SatLiteral;

/** Type of the SAT clauses */
typedef minisat::vec<SatLiteral> SatClause;

/**
 * Returns the variable of the literal.
 * @param lit the literal
 */
inline SatVariable literalToVariable(SatLiteral lit) {
  return minisat::var(lit);
}

inline bool literalSign(SatLiteral lit) {
  return minisat::sign(lit);
}

inline std::ostream& operator << (std::ostream& out, SatLiteral lit) {
  const char * s = (literalSign(lit)) ? "~" : " ";
  out << s << literalToVariable(lit);
  return out;
}

inline std::ostream& operator << (std::ostream& out, const SatClause& clause) {
  out << "clause:";
  for(int i = 0; i < clause.size(); ++i) {
    out << " " << clause[i];
  }
  out << ";";
  return out;
}

/**
 * The proxy class that allows us to modify the internals of the SAT solver.
 * It's only accessible from the PropEngine, and should be treated with major
 * care.
 */
class SatSolverProxy {

  /** The Sat solver */
  SatSolver* d_satSolver;

  public:

    SatSolverProxy(SatSolver* satSolver, const Options* options)
    : d_satSolver(satSolver) {
      initSatSolver(options);
    }

    /**
     * Initializes the given sat solver with the given options.
     * @param options the options
     */
    inline void initSatSolver(const Options* options) {
      // Setup the verbosity
      d_satSolver->verbosity = (options->verbosity > 0) ? 1 : -1;
      // Do not delete the satisfied clauses, just the learnt ones
      d_satSolver->remove_satisfied = false;
      // Initialize the backtracking stuff to 0
      d_satSolver->d_learntBase = 0;
      d_satSolver->d_clausesBase = 0;
      d_satSolver->d_decisionLevelBase = 0;
    }

    /**
     * Backtracks the internal solver state to the first n_clauses clause
     * and sets the base level to decision_level.
     * @param clausesCount the number of problem clauses to keep
     * @param variablesCount the number of problem variables to keep
     * @param decisionLevel the decision level to pop to
     */
    inline void popTo(int clausesCount,
                             int variablesCount,
                             int decisionLevel) {
      // Pop the decision level
      d_satSolver->cancelUntil(decisionLevel);

      // Remove the problem clauses from the database
      minisat::vec<minisat::Clause*>& clauses = d_satSolver->clauses;
      for (int i = clausesCount; i < clauses.size(); ++i) {
        d_satSolver->removeClause(*clauses[i]);
      }
      clauses.shrink(clausesCount);

      // Remove the learnt clauses that are above the decision level

      // Remove the variables
    }
};



}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif


#endif /* __CVC4__PROP__SAT_H */

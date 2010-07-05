/*********************                                                        */
/*! \file sat.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, dejan, cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** SAT Solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

// Just defining this for now, since there's no other SAT solver bindings.
// Optional blocks below will be unconditionally included
#define __CVC4_USE_MINISAT

#include "util/options.h"
#include "util/stats.h"
#include "theory/theory.h"

#ifdef __CVC4_USE_MINISAT

#include "prop/minisat/core/Solver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/simp/SimpSolver.h"

#endif /* __CVC4_USE_MINISAT */

namespace CVC4 {

class TheoryEngine;

namespace prop {

class PropEngine;
class CnfStream;

/* Definitions of abstract types and conversion functions for SAT interface */

#ifdef __CVC4_USE_MINISAT

/** Type of the SAT variables */
typedef minisat::Var SatVariable;

/** Type of the Sat literals */
typedef minisat::Lit SatLiteral;

/** Type of the SAT clauses */
typedef minisat::vec<SatLiteral> SatClause;

typedef minisat::lbool SatLiteralValue;

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

static inline size_t
hashSatLiteral(const SatLiteral& literal) {
  return (size_t) minisat::toInt(literal);
}

inline std::string stringOfLiteralValue(SatLiteralValue val) {
  if( val == minisat::l_False ) {
    return "0";
  } else if (val == minisat::l_True ) {
    return "1";
  } else { // unknown
    return "_";
  }
}
#endif /* __CVC4_USE_MINISAT */

/** Interface encapsulating the "input" to the solver, e.g., from the 
 * CNF converter. 
 * 
 * TODO: Is it possible to push the typedefs of SatClause and SatVariable
 * into here, somehow?
 */
class SatInputInterface {

public:

  /**
   * Assert a clause in the solver.
   * @return the SAT id of the clause
   */
  virtual int addClause(SatClause& clause, bool lemma) = 0;

  /** Create a new boolean variable in the solver. */
  virtual SatVariable newVar(bool theoryAtom = false) = 0;

  /** This method will be called when a node is not needed anymore */
  virtual void theoryUnPreRegisterTerm(TNode node) = 0;
};

/**
 * The proxy class that allows us to modify the internals of the SAT solver.
 * It's only accessible from the PropEngine, and should be treated with major
 * care.
 */
class SatSolver : public SatInputInterface {

  /** The prop engine we are using */
  PropEngine* d_propEngine;

  /** The CNF engine we are using */
  CnfStream* d_cnfStream;

  /** The theory engine we are using */
  TheoryEngine* d_theoryEngine;

  /** Context we will be using to synchronize the sat solver */
  context::Context* d_context;

  /** Remember the options */
  Options* d_options;
  
  /* Pointer to the concrete SAT solver. Including this via the
     preprocessor saves us a level of indirection vs, e.g., defining a
     sub-class for each solver. */

#ifdef __CVC4_USE_MINISAT

  /** Minisat solver */
  minisat::SimpSolver* d_minisat;

  class Statistics {
  private:
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
  public:
    Statistics() :
      d_statStarts("sat::starts"),
      d_statDecisions("sat::decisions"),
      d_statRndDecisions("sat::rnd_decisions"),
      d_statPropagations("sat::propagations"),
      d_statConflicts("sat::conflicts"),
      d_statClausesLiterals("sat::clauses_literals"),
      d_statLearntsLiterals("sat::learnts_literals"),
      d_statMaxLiterals("sat::max_literals"),
      d_statTotLiterals("sat::tot_literals")
    {
      StatisticsRegistry::registerStat(&d_statStarts);
      StatisticsRegistry::registerStat(&d_statDecisions);
      StatisticsRegistry::registerStat(&d_statRndDecisions);
      StatisticsRegistry::registerStat(&d_statPropagations);
      StatisticsRegistry::registerStat(&d_statConflicts);
      StatisticsRegistry::registerStat(&d_statClausesLiterals);
      StatisticsRegistry::registerStat(&d_statLearntsLiterals);
      StatisticsRegistry::registerStat(&d_statMaxLiterals);
      StatisticsRegistry::registerStat(&d_statTotLiterals);
    }
    void init(minisat::SimpSolver* d_minisat){
      d_statStarts.setData(d_minisat->starts);
      d_statDecisions.setData(d_minisat->decisions);
      d_statRndDecisions.setData(d_minisat->rnd_decisions);
      d_statPropagations.setData(d_minisat->propagations);
      d_statConflicts.setData(d_minisat->conflicts);
      d_statClausesLiterals.setData(d_minisat->clauses_literals);
      d_statLearntsLiterals.setData(d_minisat->learnts_literals);
      d_statMaxLiterals.setData(d_minisat->max_literals);
      d_statTotLiterals.setData(d_minisat->tot_literals);
    }
  };
  Statistics d_statistics;

#endif /* __CVC4_USE_MINISAT */

protected:

public:
  /** Hash function for literals */
  struct SatLiteralHashFunction {
    inline size_t operator()(const SatLiteral& literal) const;
  };

  SatSolver(PropEngine* propEngine,
                   TheoryEngine* theoryEngine,
                   context::Context* context,
                   const Options* options);

  ~SatSolver();

  bool solve();

  int addClause(SatClause& clause, bool lemma);

  bool canErase(const minisat::Clause& clause);

  void theoryUnPreRegisterTerm(TNode node);

  /**
   * Sat solver notifies the CNF every time it starts using a literal so
   * that we can track the usage at CNF level.
   */
  void usingLiteral(const SatLiteral& lit);

  /**
   * Sat solver notifies the CNF every time it stops using a literal occurance
   * so that we can track the usage at the CNF level.
   * @param lit the literal to release
   * @return true if there is no more occurances of lit in the problem (it's
   *         safe to ignore it from now on)
   */
  bool releasingLiteral(const SatLiteral& lit);

  /**
   * Sat solver notifies the CNF every time it erases a clause so
   * that we can track the usage at the CNF level.
   */
  void releasingClause(int clauseId);

  SatVariable newVar(bool theoryAtom = false);

  void theoryCheck(theory::Theory::Effort effort, SatClause& conflict);

  void explainPropagation(SatLiteral l, SatClause& explanation);

  void theoryPropagate(std::vector<SatLiteral>& output);

  void clearPropagatedLiterals();

  void enqueueTheoryLiteral(const SatLiteral& l);

  void setCnfStream(CnfStream* cnfStream);

  SatLiteralValue value(SatLiteral l);
};

/* Functions that delegate to the concrete SAT solver. */

#ifdef __CVC4_USE_MINISAT

inline SatSolver::SatSolver(PropEngine* propEngine, TheoryEngine* theoryEngine,
                     context::Context* context, const Options* options) :
  d_propEngine(propEngine),
  d_cnfStream(NULL),
  d_theoryEngine(theoryEngine),
  d_context(context),
  d_statistics()
{
  // Create the solver
  d_minisat = new minisat::SimpSolver(this, d_context);
  // Setup the verbosity
  d_minisat->verbosity = (options->verbosity > 0) ? 1 : -1;
  // Do not delete the satisfied clauses, just the learnt ones
  d_minisat->remove_satisfied = false;
  // Make minisat reuse the literal values
  d_minisat->polarity_mode = minisat::SimpSolver::polarity_user;

  // No random choices
  if(Debug.isOn("no_rnd_decisions")){
    d_minisat->random_var_freq = 0;
  }

  d_statistics.init(d_minisat);
}

inline SatSolver::~SatSolver() {
  delete d_minisat;
}

inline bool SatSolver::solve() {
  return d_minisat->solve();
}

inline int SatSolver::addClause(SatClause& clause, bool lemma) {
  return d_minisat->addClause(clause, lemma ? minisat::Solver::CLAUSE_LEMMA : minisat::Solver::CLAUSE_PROBLEM);
}

inline SatVariable SatSolver::newVar(bool theoryAtom) {
  return d_minisat->newVar(true, true, theoryAtom);
}

inline SatLiteralValue SatSolver::value(SatLiteral l) {
  return d_minisat->modelValue(l);
}

#endif /* __CVC4_USE_MINISAT */

inline size_t
SatSolver::SatLiteralHashFunction::operator()(const SatLiteral& literal) const {
  return hashSatLiteral(literal);
}

}/* CVC4::prop namespace */

inline std::ostream& operator <<(std::ostream& out, prop::SatLiteral lit) {
  const char * s = (prop::literalSign(lit)) ? "~" : " ";
  out << s << prop::literalToVariable(lit);
  return out;
}

inline std::ostream& operator <<(std::ostream& out, const prop::SatClause& clause) {
  out << "clause:";
  for(int i = 0; i < clause.size(); ++i) {
    out << " " << clause[i];
  }
  out << ";";
  return out;
}

inline std::ostream& operator <<(std::ostream& out, prop::SatLiteralValue val) {
  out << prop::stringOfLiteralValue(val);
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__PROP__SAT_H */

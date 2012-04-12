/*********************                                                        */
/*! \file sat.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, cconway, dejan
 ** Minor contributors (to current version): barrett
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

#include "cvc4_private.h"

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

// Just defining this for now, since there's no other SAT solver bindings.
// Optional blocks below will be unconditionally included
#define __CVC4_USE_MINISAT

#include "theory/theory.h"
#include "util/options.h"
#include "util/stats.h"

#include "prop/sat_solver.h"

namespace CVC4 {

class TheoryEngine;

namespace prop {

class PropEngine;
class CnfStream;

/**
 * The proxy class that allows the SatSolver to communicate with the theories
 */
class TheoryProxy {

  /** The prop engine we are using */
  PropEngine* d_propEngine;

  /** The CNF engine we are using */
  CnfStream* d_cnfStream;

  /** The theory engine we are using */
  TheoryEngine* d_theoryEngine;

  /** Context we will be using to synchronzie the sat solver */
  context::Context* d_context;

  /**
   * Set of all lemmas that have been "shared" in the portfolio---i.e.,
   * all imported and exported lemmas.
   */
  std::hash_set<Node, NodeHashFunction> d_shared;

public:
  TheoryProxy(PropEngine* propEngine,
              TheoryEngine* theoryEngine,
              context::Context* context,
              CnfStream* cnfStream);

  ~TheoryProxy();

  // ideally, this output interface for SAT should only pass messages for:
  // * about-to-make-a-decision(lvl)
  // * made-decision(L, lvl)
  // * about-to-propagate-bcp
  // * propagated(L)
  // * done-propagating-bcp
  // * have-satisfying-assignment
  // * have-level-0-conflict

  void enqueueTheoryLiteral(const SatLiteral& l);

  /**
   * Check consistency with all active theories at specified effort
   * level.
   */
  void theoryCheck(theory::Theory::Effort effort);

  void theoryPropagate(SatClause& output);

  void explainPropagation(SatLiteral l, SatClause& explanation);

  /**
   * Should return: 1) an unassigned literal to use as next decision;
   * 2) lit_Undef if should fall back to SAT solver's default; or 3)
   * NO_MORE_DECISIONS.
   */
  SatLiteral getNextDecisionRequest();

  void removeClausesAboveLevel(int level);

  /**
   * Notifies of a new variable at a decision level.
   */
  void variableNotify(SatVariable var);

  void unregisterVar(SatLiteral lit);

  void renewVar(SatLiteral lit, int level = -1);

  TNode getNode(SatLiteral lit);

  void notifyRestart();

  void notifyNewLemma(SatClause& lemma);

  void logDecision(SatLiteral lit);

  void checkTime();

};/* class SatSolver */

/* Functions that delegate to the concrete SAT solver. */

inline TheoryProxy::TheoryProxy(PropEngine* propEngine,
                                TheoryEngine* theoryEngine,
                                context::Context* context,
                                CnfStream* cnfStream) :
  d_propEngine(propEngine),
  d_cnfStream(cnfStream),
  d_theoryEngine(theoryEngine),
  d_context(context)
{}

}/* CVC4::prop namespace */

}/* CVC4 namespace */

#endif /* __CVC4__PROP__SAT_H */

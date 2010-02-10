/*********************                                                        */
/** smt_engine.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** SmtEngine: the main public entry point of libcvc4.
 **/

#ifndef __CVC4__SMT_ENGINE_H
#define __CVC4__SMT_ENGINE_H

#include <vector>

#include "cvc4_config.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "util/result.h"
#include "util/model.h"
#include "util/decision_engine.h"
#include "context/context.h"

// In terms of abstraction, this is below (and provides services to)
// ValidityChecker and above (and requires the services of)
// PropEngine.

namespace CVC4 {

class Command;
class Options;
class TheoryEngine;

namespace prop {
  class PropEngine;
}

// TODO: SAT layer (esp. CNF- versus non-clausal solvers under the
// hood): use a type parameter and have check() delegate, or subclass
// SmtEngine and override check()?
//
// Probably better than that is to have a configuration object that
// indicates which passes are desired.  The configuration occurs
// elsewhere (and can even occur at runtime).  A simple "pass manager"
// of sorts determines check()'s behavior.
//
// The CNF conversion can go on in PropEngine.

class CVC4_PUBLIC SmtEngine {

public:

  /**
   * Construct an SmtEngine with the given expression manager and user options.
   */
  SmtEngine(ExprManager* em, const Options* opts) throw();

  /**
   * Destruct the SMT engine.
   */
  ~SmtEngine();

  /**
   * Execute a command.
   */
  void doCommand(Command*);

  /**
   * Asserts the given formula to the current context.
   */
  Result assertFormula(const BoolExpr& formula);

  /**
   * Check the formula for validity in the current context.
   * @param formula the formula to check for validity
   * @return the result
   */
  Result query(const BoolExpr& formula);

  /**
   * Checks the given formula for satisfiability in the the current context.
   * @param formula the formula to check for satisfiability
   */
  Result checkSat(const BoolExpr& formula);

  /**
   * Checks the current context for satisfiability.
   */
  Result checkSat();

  /**
   * Simplify a formula without doing "much" work.  Requires assist
   * from the SAT Engine.
   */
  Expr simplify(const Expr& expr);

  /**
   * Get a (counter)model (only if preceded by a SAT or INVALID query).
   */
  Model getModel();

  /**
   * Push a user-level context.
   */
  void push();

  /**
   * Pop a user-level context.  Throws an exception if nothing to pop.
   */
  void pop();

private:

  /** The context */
  context::Context d_context;

  /**
   * Pushes the internal context level.
   */
  void pushInternal();

  /**
   * Pops the internal context level to the given level.
   * @param contextLevel the target context level
   */
  void popInternal(int contextLevel);

  /** The context level to backtrack to when the user pops */
  context::CDO<int> d_backtrackContextLevel;

  /** Our expression manager */
  ExprManager* d_exprManager;

  /** Out internal expression/node manager */
  NodeManager* d_nodeManager;

  /** User-level options */
  const Options* d_options;

  /** The decision engine */
  DecisionEngine* d_decisionEngine;

  /** The decision engine */
  TheoryEngine* d_theoryEngine;

  /** The propositional engine */
  prop::PropEngine* d_propEngine;

  /**
   * Pre-process an Node.  This is expected to be highly-variable,
   * with a lot of "source-level configurability" to add multiple
   * passes over the Node.  TODO: may need to specify a LEVEL of
   * preprocessing (certain contexts need more/less ?).
   */
  Node preprocess(const Node& node);

  /**
   * Asserts the formula to the current context.
   * @param node the formula to assert
   */
  void assertFormula(const Node& node);

  /**
   * Quick check of consistency in current context: calls
   * processAssertionList() then look for inconsistency (based only on
   * that).
   */
  Result quickCheck();

};/* class SmtEngine */

}/* CVC4 namespace */

#endif /* __CVC4__SMT_ENGINE_H */

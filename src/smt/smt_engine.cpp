/*********************                                                        */
/** smt_engine.cpp
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
 **/

#include "smt/smt_engine.h"
#include "expr/command.h"
#include "expr/node_builder.h"
#include "util/output.h"
#include "util/exception.h"
#include "util/options.h"
#include "prop/prop_engine.h"

using namespace CVC4::prop;
using namespace std;

namespace CVC4 {

SmtEngine::SmtEngine(ExprManager* em, const Options* opts) throw () :
  d_context(),
  d_backtrackContextLevel(&d_context, 0),
  d_exprManager(em),
  d_nodeManager(em->getNodeManager()),
  d_options(opts)
{
  d_decisionEngine = new DecisionEngine();
  d_theoryEngine = new TheoryEngine(this);
  d_propEngine = new PropEngine(opts, d_decisionEngine,
                                d_theoryEngine, &d_context);
}

SmtEngine::~SmtEngine() {
  delete d_propEngine;
  delete d_theoryEngine;
  delete d_decisionEngine;
}

void SmtEngine::doCommand(Command* c) {
  Debug("smt") << "SmtEngine::doCommand(" << c << ")" << endl;
  NodeManagerScope nms(d_nodeManager);
  c->invoke(this);
}

Node SmtEngine::preprocess(const Node& expr) {
  Debug("smt") << "SmtEngine::preprocess(" << expr << ")" << endl;
  return expr;
}

Result SmtEngine::checkSat() {
  Debug("smt") << "SmtEngine::checkSat()" << endl;
  return d_propEngine->checkSat();
}

Result SmtEngine::checkSat(const BoolExpr& formula) {
  Debug("smt") << "SmtEngine::checkSat(" << formula << ")" << endl;
  NodeManagerScope nms(d_nodeManager);

  // Remember the current context
  int context_level = d_context.getLevel();
  pushInternal();

  // Assert the formula and check for satsfiability
  assertFormula(formula.getNode());
  Result result = checkSat().asSatisfiabilityResult();

  // If the result is UNSAT, pop the scope
  if (result.isSAT() == Result::UNSAT) {
    popInternal(context_level);
  }

  Debug("smt") << "SmtEngine::checkSat(" << formula << ") ==> " << result << endl;
  return result;
}

Result SmtEngine::quickCheck() {
  Debug("smt") << "SmtEngine::quickCheck()" << endl;
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEngine::assertFormula(const Node& formula) {
  Debug("smt") << "SmtEngine::assertFormula(" << formula << ")" << endl;
  d_propEngine->assertFormula(preprocess(formula));
}


Result SmtEngine::query(const BoolExpr& formula) {
  Debug("smt") << "SmtEngine::query(" << formula << ")" << endl;
  NodeManagerScope nms(d_nodeManager);
  Result r = checkSat(formula.notExpr()).asValidityResult();
  Debug("smt") << "SMT query(" << formula << ") ==> " << r << endl;
  return r;
}

Result SmtEngine::assertFormula(const BoolExpr& formula) {
  Debug("smt") << "SmtEngine::assertFormula(" << formula << ")" << endl;
  NodeManagerScope nms(d_nodeManager);
  assertFormula(formula.getNode());
  return quickCheck().asValidityResult();
}

Expr SmtEngine::simplify(const Expr& expr) {
  Debug("smt") << "SmtEngine::simplify(" << expr << ")" << endl;
  Expr simplify(const Expr& e);
  Unimplemented();
}

void SmtEngine::push() {
  Debug("smt") << "SmtEngine::push()" << endl;
  int currentLevel = d_context.getLevel();
  pushInternal();
  d_backtrackContextLevel = currentLevel;
}

void SmtEngine::pop() {
  Debug("smt") << "SmtEngine::push()" << endl;
  popInternal(d_backtrackContextLevel);
}

void SmtEngine::pushInternal() {
  d_context.push();
  d_propEngine->push();
}

void SmtEngine::popInternal(int contextLevel) {
  Assert(contextLevel <= d_context.getLevel(), "Given context level bigger than "
      "the current one");
  while(contextLevel != d_context.getLevel()) {
    // We need to inform the prop engine as it needs to backtrack minisat's
    // internal state
    d_propEngine->pop();
    // And we pop a context
    d_context.pop();
  }
}

}/* CVC4 namespace */

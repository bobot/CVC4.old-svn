/*********************                                                        */
/** prop_engine.cpp
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "prop/prop_engine.h"
#include "prop/cnf_stream.h"

#include "theory/theory_engine.h"
#include "util/decision_engine.h"
#include "util/Assert.h"
#include "util/output.h"
#include "util/options.h"
#include "util/result.h"

#include <utility>
#include <map>

using namespace std;
using namespace CVC4::context;

namespace CVC4 {
namespace prop {

PropEngine::PropEngine(const Options* opts, DecisionEngine* de,
                       TheoryEngine* te, Context* context) :
  d_inCheckSat(false),
  d_satBaseDecisionLevel(context, 0),
  d_satClauses(context, 0),
  d_options(opts), d_decisionEngine(de),
  d_theoryEngine(te) {
  Debug("prop") << "Constructing the PropEngine" << endl;
  d_satSolver = new SatSolver();
  SatSolverProxy::initSatSolver(d_satSolver, d_options);
  d_cnfStream = new CVC4::prop::TseitinCnfStream(d_satSolver);
}

PropEngine::~PropEngine() {
  Debug("prop") << "Destructing the PropEngine" << endl;
  delete d_cnfStream;
  delete d_satSolver;
}

void PropEngine::assertFormula(const Node& node) {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as non-removable
  d_cnfStream->convertAndAssert(node, false);
}

void PropEngine::assertLemma(const Node& node) {
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as removable
  if (d_inCheckSat)
    d_assertQueue.push(node);
  else
    d_cnfStream->convertAndAssert(node, true);
}

Result PropEngine::checkSat() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Assert(d_assertQueue.empty(), "Queue of assertion is not empty!");
  Debug("prop") << "solve()" << endl;
  // Mark that we are in the checkSat
  d_inCheckSat = true;
  // Start the satisfiability loop
  bool result = true;
  do {
    // Enqueue all the lemmas in the queue
    while (!d_assertQueue.empty()) {
      d_cnfStream->convertAndAssert(d_assertQueue.front(), true);
      d_assertQueue.pop();
    }
    // Check the problem
    result = d_satSolver->solve();
  } while (result && !d_assertQueue.empty());
  // Not in checkSat any more
  d_inCheckSat = false;
  Debug("prop") << "solve() => " << (result ? "true" : "false") << endl;
  return Result(result ? Result::SAT : Result::UNSAT);
}

void PropEngine::push() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "push()" << endl;
}

void PropEngine::pop() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "pop()" << endl;
}

}/* prop namespace */
}/* CVC4 namespace */

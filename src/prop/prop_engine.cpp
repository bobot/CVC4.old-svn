/*********************                                                        */
/** prop_engine.cpp
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

#include "sat.h"
#include "prop/prop_engine.h"

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
                       TheoryEngine* te, Context* context)
: d_inCheckSat(false),
  d_options(opts),
  d_decisionEngine(de),
  d_theoryEngine(te),
  d_context(context)
{
  Debug("prop") << "Constructing the PropEngine" << endl;
  d_satSolver = new SatSolver(this, d_theoryEngine, d_context, d_options);
  d_cnfStream = new CVC4::prop::TseitinCnfStream(d_satSolver);
  d_satSolver->setCnfStream(d_cnfStream);
}

PropEngine::~PropEngine() {
  Debug("prop") << "Destructing the PropEngine" << endl;
  delete d_cnfStream;
  delete d_satSolver;
}

void PropEngine::assertFormula(TNode node) {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as non-removable
  d_cnfStream->convertAndAssert(node);
}

void PropEngine::assertLemma(TNode node) {
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as removable
  d_cnfStream->convertAndAssert(node);
}

Result PropEngine::checkSat() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "PropEngine::checkSat()" << endl;
  // Mark that we are in the checkSat
  d_inCheckSat = true;
  // Check the problem
  bool result = d_satSolver->solve();
  // Not in checkSat any more
  d_inCheckSat = false;
  Debug("prop") << "PropEngine::checkSat() => " << (result ? "true" : "false") << endl;
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

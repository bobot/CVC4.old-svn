/*********************                                                        */
/*! \file decision_engine.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Decision engine
 **
 ** Decision engine
 **/

#include "decision/decision_engine.h"
#include "decision/justification_heuristic.h"

#include "util/options.h"

using namespace std;

namespace CVC4 {

DecisionEngine::DecisionEngine() : d_needSimplifiedPreITEAssertions() {
  const Options* options = Options::current();
  Trace("decision") << "Creating decision engine" << std::endl;
  if(options->decisionMode == Options::DECISION_STRATEGY_INTERNAL) { }
  if(options->decisionMode == Options::DECISION_STRATEGY_JUSTIFICATION) {
    DecisionStrategy* ds = new decision::JustificationHueristic(this);
    enableStrategy(ds);
  }
}

void DecisionEngine::enableStrategy(DecisionStrategy* ds)
{
  d_enabledStrategies.push_back(ds);
  if( ds->needSimplifiedPreITEAssertions() )
    d_needSimplifiedPreITEAssertions.push_back(ds);
}

}/* CVC4 namespace */

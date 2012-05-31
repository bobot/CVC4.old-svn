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

#include "expr/node.h"
#include "decision/options.h"
#include "decision/decision_mode.h"

using namespace std;

namespace CVC4 {

DecisionEngine::DecisionEngine() : d_needSimplifiedPreITEAssertions() {
  Trace("decision") << "Creating decision engine" << std::endl;
  if(options::decisionMode() == decision::DECISION_STRATEGY_INTERNAL) { }
  if(options::decisionMode() == decision::DECISION_STRATEGY_JUSTIFICATION) {
    DecisionStrategy* ds = new decision::JustificationHeuristic(this);
    enableStrategy(ds);
  }
}

void DecisionEngine::enableStrategy(DecisionStrategy* ds)
{
  d_enabledStrategies.push_back(ds);
  if( ds->needSimplifiedPreITEAssertions() )
    d_needSimplifiedPreITEAssertions.push_back(ds);
}

void DecisionEngine::informSimplifiedPreITEAssertions(const vector<Node> &assertions)
{
  d_assertions.reserve(assertions.size());
  for(unsigned i = 0; i < assertions.size(); ++i)
    d_assertions.push_back(assertions[i]);
  for(unsigned i = 0; i < d_needSimplifiedPreITEAssertions.size(); ++i)
    d_needSimplifiedPreITEAssertions[i]->notifyAssertionsAvailable();
}

}/* CVC4 namespace */

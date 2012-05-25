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
#include "decision/relevancy.h"

#include "expr/node.h"
#include "util/options.h"

using namespace std;

namespace CVC4 {

  DecisionEngine::DecisionEngine(context::Context *sc,
                                 context::Context *uc) :
  d_enabledStrategies(),
  d_needIteSkolemMap(),
  d_relevancyStrategy(NULL),
  d_assertions(),
  d_cnfStream(NULL),
  d_satSolver(NULL),
  d_satContext(sc),
  d_userContext(uc),
  d_result(SAT_VALUE_UNKNOWN)
{
  const Options* options = Options::current();
  Trace("decision") << "Creating decision engine" << std::endl;

  if(options->incrementalSolving) return;

  if(options->decisionMode == Options::DECISION_STRATEGY_INTERNAL) { }
  if(options->decisionMode == Options::DECISION_STRATEGY_JUSTIFICATION) {
    ITEDecisionStrategy* ds = 
      new decision::JustificationHeuristic(this, d_satContext);
    enableStrategy(ds);
    d_needIteSkolemMap.push_back(ds);
  }
  if(options->decisionMode == Options::DECISION_STRATEGY_RELEVANCY) {
    bool relLeaves = (options->decisionExtra & 1) == 1;
    RelevancyStrategy* ds = 
      new decision::Relevancy(this, d_satContext, relLeaves);
    enableStrategy(ds);
    d_needIteSkolemMap.push_back(ds);
    d_relevancyStrategy = ds;
  }
}

void DecisionEngine::enableStrategy(DecisionStrategy* ds)
{
  d_enabledStrategies.push_back(ds);
}


bool DecisionEngine::isRelevant(SatVariable var)
{
  Debug("decision") << "isRelevant(" << var <<")" << std::endl;
  if(d_relevancyStrategy != NULL) {
    //Assert(d_cnfStream->hasNode(var));
    return d_relevancyStrategy->isRelevant( d_cnfStream->getNode(SatLiteral(var)) );
  } else {
    return true;
  }
}

SatValue DecisionEngine::getPolarity(SatVariable var)
{
  Debug("decision") << "getPolariry(" << var <<")" << std::endl;
  if(d_relevancyStrategy != NULL) {
    Assert(isRelevant(var));
    return d_relevancyStrategy->getPolarity( d_cnfStream->getNode(SatLiteral(var)) );
  } else {
    return SAT_VALUE_UNKNOWN;
  }
}








void DecisionEngine::addAssertions(const vector<Node> &assertions)
{
  Assert(false);  // doing this so that we revisit what to do
                  // here. Currently not being used.

  // d_result = SAT_VALUE_UNKNOWN;
  // d_assertions.reserve(assertions.size());
  // for(unsigned i = 0; i < assertions.size(); ++i)
  //   d_assertions.push_back(assertions[i]); 
}

void DecisionEngine::addAssertions(const vector<Node> &assertions,
                                   unsigned assertionsEnd,
                                   IteSkolemMap iteSkolemMap)
{
  // new assertions, reset whatever result we knew
  d_result = SAT_VALUE_UNKNOWN;
  
  d_assertions.reserve(assertions.size());
  for(unsigned i = 0; i < assertions.size(); ++i)
    d_assertions.push_back(assertions[i]);
  
  for(unsigned i = 0; i < d_needIteSkolemMap.size(); ++i)
    d_needIteSkolemMap[i]->
      addAssertions(assertions, assertionsEnd, iteSkolemMap);
}

// void DecisionEngine::addAssertion(Node n)
// {
//   d_result = SAT_VALUE_UNKNOWN;
//   if(needIteSkolemMap()) {
//     d_assertions.push_back(n);
//   }
//   for(unsigned i = 0; i < d_needIteSkolemMap.size(); ++i)
//     d_needIteSkolemMap[i]->notifyAssertionsAvailable();
// }
  

}/* CVC4 namespace */

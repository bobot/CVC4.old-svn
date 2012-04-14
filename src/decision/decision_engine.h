/*********************                                                        */
/*! \file decision_engine.h
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

#ifndef __CVC4__DECISION__DECISION_ENGINE_H
#define __CVC4__DECISION__DECISION_ENGINE_H

#include <vector>

#include "prop/sat_solver_types.h"
#include "util/output.h"
#include "decision/decision_strategy.h"

using namespace std;
using namespace CVC4::decision;

namespace CVC4 {

class DecisionEngine {

  vector <DecisionStrategy* > d_enabledStrategies;
  vector <DecisionStrategy* > d_needSimplifiedPreITEAssertions;

public:
  /** Constructor, enables decision stragies based on options */
  DecisionEngine();

  /** Destructor, currently does nothing */
  ~DecisionEngine() {
    Trace("decision") << "Destroying decision engine" << std::endl;
  }

  /** Gets the next decision based on strategies that are enabled */
  prop::SatLiteral getNext() {
    return prop::undefSatLiteral;
  }

  /**
   * This is called by SmtEngine, at shutdown time, just before
   * destruction.  It is important because there are destruction
   * ordering issues between some parts of the system.  For now,
   * there's nothing to do here in the DecisionEngine.
   */
  void shutdown() {
    Trace("decision") << "Shutting down decision engine" << std::endl;
  }

  bool needSimplifiedPreITEAssertions() {
    return false;
  }

private:
  /**
   * Enable a particular decision strategy, updating corresponding
   * decision strategies
   */
  void enableStrategy(DecisionStrategy* s);

};/* DecisionEngine class */

}/* CVC4 namespace */

#endif /* __CVC4__DECISION__DECISION_ENGINE_H */

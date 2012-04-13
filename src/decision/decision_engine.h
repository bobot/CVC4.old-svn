/*********************                                                        */
/*! \file decision_engine.h
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Decision engine
 **
 ** Decision engine
 **/

#include "prop/sat_solver_types.h"
#include "util/output.h"

#ifndef __CVC4__DECISION__DECISION_ENGINE_H
#define __CVC4__DECISION__DECISION_ENGINE_H

namespace CVC4 {

class DecisionEngine {
public:
  /** Constructor, currently does nothing */
  DecisionEngine() {
    Trace("decision") << "Creating decision engine" << std::endl;
  }

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
};/* DecisionEngine class */

}/* CVC4 namespace */

#endif /* __CVC4__DECISION__DECISION_ENGINE_H */

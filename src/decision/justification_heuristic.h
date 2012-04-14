/*********************                                                        */
/*! \file justification_heuristic.h
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
 ** \brief Justification hueristic for decision making
 **
 ** A ATGP-inspired justification-based decision hueristic. See
 ** [insert reference] for more details. This code is, or not, based
 ** on the CVC3 implementation of the same hueristic.
 **
 ** It needs access to the simplified but non-clausal formula.
 **/

#ifndef __CVC4__DECISION__JUSTIFICATION_HUERISTIC
#define __CVC4__DECISION__JUSTIFICATION_HUERISTIC

#include "decision_engine.h"
#include "decision_strategy.h"

#include "prop/sat_solver_types.h"

namespace CVC4 {

namespace decision {

class JustificationHueristic : public DecisionStrategy {
public:
  JustificationHueristic(CVC4::DecisionEngine* de) : DecisionStrategy(de) {
    Trace("decision") << "Justification hueristic enabled" << std::endl;
  }
  prop::SatLiteral getNext() { 
    Trace("decision") << "JustificationHueristic::getNext()" << std::endl;
    return prop::undefSatLiteral;
  } 
  bool needSimplifiedPreITEAssertions() { return true; }
};/* class JustificationHueristic */

}/* namespace decision */

}/* namespace CVC4 */

#endif /* __CVC4__DECISION__JUSTIFICATION_HUERISTIC */

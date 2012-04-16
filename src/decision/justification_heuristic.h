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
 ** \brief Justification heuristic for decision making
 **
 ** A ATGP-inspired justification-based decision heuristic. See
 ** [insert reference] for more details. This code is, or not, based
 ** on the CVC3 implementation of the same heuristic.
 **
 ** It needs access to the simplified but non-clausal formula.
 **/

#ifndef __CVC4__DECISION__JUSTIFICATION_HEURISTIC
#define __CVC4__DECISION__JUSTIFICATION_HEURISTIC

#include "decision_engine.h"
#include "decision_strategy.h"

#include "prop/sat_solver_types.h"
#include "expr/node.h"

using namespace CVC4::prop;

namespace CVC4 {

namespace decision {

class JustificationHeuristic : public DecisionStrategy {
  typedef __gnu_cxx::hash_map<TNode, bool, TNodeHashFunction> TNodeBoolMap;
  TNodeBoolMap d_justified;
  unsigned  d_prvsIndex;
public:
  JustificationHeuristic(CVC4::DecisionEngine* de) : 
    DecisionStrategy(de) {
    Trace("decision") << "Justification heuristic enabled" << std::endl;
  }
  prop::SatLiteral getNext() {
    Trace("decision") << "JustificationHeuristic::getNext()" << std::endl;

    const vector<Node>& assertions = d_decisionEngine->getAssertions();

    for(unsigned i = d_prvsIndex; i < assertions.size(); ++i) {
      SatLiteral l = findSplitterRec(assertions[i], SAT_VALUE_TRUE);
      if(l != prop::undefSatLiteral) {
        d_prvsIndex = i;
        return l;
      }
    }

    return prop::undefSatLiteral;
  } 
  bool needSimplifiedPreITEAssertions() { return true; }
  void notifyAssertionsAvailable() {
    /* clear the justifcation labels -- reconsider if/when to do
       this */
    d_justified.clear();
    d_prvsIndex = 0;
  }
private:
  /* Do all the hardwork. */ 
  SatLiteral findSplitterRec(Node n, SatValue val) { return prop::undefSatLiteral; }
};/* class JustificationHeuristic */

}/* namespace decision */

}/* namespace CVC4 */

#endif /* __CVC4__DECISION__JUSTIFICATION_HEURISTIC */

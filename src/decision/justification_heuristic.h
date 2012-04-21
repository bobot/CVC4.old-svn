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
  set<TNode> d_justified;
  unsigned  d_prvsIndex;
  IntStat d_helfulness;
public:
  JustificationHeuristic(CVC4::DecisionEngine* de) : 
    DecisionStrategy(de),
    d_helfulness("decision::jh::helpfulness", 0) {
    StatisticsRegistry::registerStat(&d_helfulness);
    Trace("decision") << "Justification heuristic enabled" << std::endl;
  }
  ~JustificationHeuristic() {
    StatisticsRegistry::unregisterStat(&d_helfulness);
  }
  prop::SatLiteral getNext(bool &stopSearch) {
    Trace("decision") << "JustificationHeuristic::getNext()" << std::endl;

    const vector<Node>& assertions = d_decisionEngine->getAssertions();

    for(unsigned i = d_prvsIndex; i < assertions.size(); ++i) {
      SatLiteral litDecision;

      Trace("decision") << assertions[i] << std::endl;

      SatValue desiredVal = SAT_VALUE_UNKNOWN;

      if(d_decisionEngine->hasSatLiteral(assertions[i]) ) {
        desiredVal = d_decisionEngine->getSatValue( d_decisionEngine->getSatLiteral(assertions[i]) );
        Trace("decision") << "JustificationHeuristic encountered a variable not in SatSolver." << std::endl;
        //    continue;
        //    Assert(not lit.isNull());
      }

      if(desiredVal == SAT_VALUE_UNKNOWN) desiredVal = SAT_VALUE_TRUE;

      bool ret = findSplitterRec(assertions[i], desiredVal, &litDecision);
      if(ret == true) {
        Trace("decision") << "Yippee!!" << std::endl;
        d_prvsIndex = i;
        return litDecision;
      }
    }

    Trace("decision") << "Nothing to split on " << std::endl;

    bool alljustified = true;
    for(unsigned i = 0 ; i < assertions.size() && alljustified ; ++i)
      alljustified &= assertions[i].getKind() == kind::NOT ? 
        checkJustified(assertions[i][0]) : checkJustified(assertions[i]);
    Assert(alljustified);

    stopSearch = alljustified;
    d_decisionEngine->setResult(SAT_VALUE_TRUE);

    return prop::undefSatLiteral;
  } 
  bool needSimplifiedPreITEAssertions() { return true; }
  void notifyAssertionsAvailable() {
    Trace("decision") << "JustificationHeuristic::notifyAssertionsAvailable()" 
                      << "  size = " << d_decisionEngine->getAssertions().size()
                      << std::endl;
    /* clear the justifcation labels -- reconsider if/when to do
       this */
    d_justified.clear();
    d_prvsIndex = 0;
  }
private:
  /* Do all the hardwork. */ 
  bool findSplitterRec(Node node, SatValue value, SatLiteral* litDecision);

  /* Helper functions */
  void setJustified(TNode);
  bool checkJustified(TNode);
  
  /* If literal exists corresponding to the node return
     that. Otherwise an UNKNOWN */
  SatValue tryGetSatValue(Node n)
  {
    if(d_decisionEngine->hasSatLiteral(n) ) {
      return d_decisionEngine->getSatValue(d_decisionEngine->getSatLiteral(n));
    } else {
      return SAT_VALUE_UNKNOWN;
    }
  }

};/* class JustificationHeuristic */

}/* namespace decision */

}/* namespace CVC4 */

#endif /* __CVC4__DECISION__JUSTIFICATION_HEURISTIC */

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

#include "context/cdhashset.h"
#include "expr/node.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {

namespace decision {

class GiveUpException : public Exception {
public:
  GiveUpException() : 
    Exception("justification hueristic: giving up") {
  }
};/* class GiveUpException */

class JustificationHeuristic : public ITEDecisionStrategy {
  typedef hash_map<TNode,std::vector<TNode>,TNodeHashFunction> IteCache;

  // being 'justified' is monotonic with respect to decisions
  context::CDHashSet<TNode,TNodeHashFunction> d_justified;
  context::CDO<unsigned>  d_prvsIndex;

  IntStat d_helfulness;
  IntStat d_giveup;
  TimerStat d_timestat;

  /**
   * A copy of the assertions that need to be justified
   * directly. Doesn't have ones introduced during during ITE-removal.
   */
  std::vector<TNode> d_assertions;   
  //TNode is fine since decisionEngine has them too

  /** map from ite-rewrite skolem to a boolean-ite assertion */
  hash_map<TNode,TNode,TNodeHashFunction> d_iteAssertions;
  // 'key' being TNode is fine since if a skolem didn't exist anywhere,
  // we won't look it up. as for 'value', same reason as d_assertions

  /** Cache for ITE skolems present in a atomic formula */
  IteCache d_iteCache;
public:
  JustificationHeuristic(CVC4::DecisionEngine* de, context::Context *c):
    ITEDecisionStrategy(de, c),
    d_justified(c),
    d_prvsIndex(c, 0),
    d_helfulness("decision::jh::helpfulness", 0),
    d_giveup("decision::jh::giveup", 0),
    d_timestat("decision::jh::time") {
    StatisticsRegistry::registerStat(&d_helfulness);
    StatisticsRegistry::registerStat(&d_giveup);
    StatisticsRegistry::registerStat(&d_timestat);
    Trace("decision") << "Justification heuristic enabled" << std::endl;
  }
  ~JustificationHeuristic() {
    StatisticsRegistry::unregisterStat(&d_helfulness);
    StatisticsRegistry::unregisterStat(&d_timestat);
  }
  prop::SatLiteral getNext(bool &stopSearch) {
    Trace("decision") << "JustificationHeuristic::getNext()" << std::endl;

    TimerStat::CodeTimer codeTimer(d_timestat);

    for(unsigned i = d_prvsIndex; i < d_assertions.size(); ++i) {
      SatLiteral litDecision;

      Trace("decision") << d_assertions[i] << std::endl;

      SatValue desiredVal = SAT_VALUE_UNKNOWN;

      if(d_decisionEngine->hasSatLiteral(d_assertions[i]) ) {
        //desiredVal = d_decisionEngine->getSatValue( d_decisionEngine->getSatLiteral(assertions[i]) );
        Trace("decision") << "JustificationHeuristic encountered a variable not in SatSolver." << std::endl;
        //    continue;
        //    Assert(not lit.isNull());
      }

      if(desiredVal == SAT_VALUE_UNKNOWN) desiredVal = SAT_VALUE_TRUE;

      bool ret;
      try {
        ret = findSplitterRec(d_assertions[i], desiredVal, &litDecision);
      }catch(GiveUpException &e) {
        return prop::undefSatLiteral;
      }
      if(ret == true) {
        Trace("decision") << "Yippee!!" << std::endl;
        //d_prvsIndex = i;
	++d_helfulness;
        return litDecision;
      }
    }

    Trace("decision") << "Nothing to split on " << std::endl;

    bool alljustified = true;
    for(unsigned i = 0 ; i < d_assertions.size() && alljustified ; ++i) {
      alljustified &= d_assertions[i].getKind() == kind::NOT ? 
        checkJustified(d_assertions[i][0]) :
        checkJustified(d_assertions[i]);

      if(Debug.isOn("decision")) {
	bool x = d_assertions[i].getKind() == kind::NOT ? 
        checkJustified(d_assertions[i][0]) : checkJustified(d_assertions[i]);
	if(x==false)
	  Debug("decision") << "****** Not justified [i="<<i<<"]: " << d_assertions[i] << std::endl;
      }
    }
    Assert(alljustified);

    stopSearch = alljustified;
    d_decisionEngine->setResult(SAT_VALUE_TRUE);

    return prop::undefSatLiteral;
  }

  void addAssertions(const std::vector<Node> &assertions,
                     unsigned assertionsEnd,
                     IteSkolemMap iteSkolemMap) {
    Trace("decision")
      << "JustificationHeuristic::addAssertions()" 
      << " size = " << d_decisionEngine->getAssertions().size()
      << " assertionsEnd = " << assertionsEnd
      << std::endl;

    for(unsigned i = 0; i < assertionsEnd; ++i)
      d_assertions.push_back(assertions[i]);
    
    for(IteSkolemMap::iterator i = iteSkolemMap.begin();
        i != iteSkolemMap.end(); ++i) {
      Assert(i->second >= assertionsEnd && i->second < assertions.size());
      d_iteAssertions[i->first] = assertions[i->second];
    }
  }
private:
  /* Do all the hardwork. */ 
  bool findSplitterRec(Node node, SatValue value, SatLiteral* litDecision);

  /* Helper functions */
  void setJustified(TNode);
  bool checkJustified(TNode);
  
  /* If literal exists corresponding to the node return
     that. Otherwise an UNKNOWN */
  SatValue tryGetSatValue(Node n);

  /* Get list of all ITEs for the atomic formula v */
  void getITEs(TNode n, vector<TNode> &v);
};/* class JustificationHeuristic */

}/* namespace decision */

}/* namespace CVC4 */

#endif /* __CVC4__DECISION__JUSTIFICATION_HEURISTIC */

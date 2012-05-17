/*********************                                                        */
/*! \file relevancy.h
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
 **
 ** Relevancy
 ** ---------
 **
 ** This class also currently computes the may-relevancy of a node
 **
 ** A node is may-relevant if there is a path from the root of the
 ** formula to the node such that no node on the path is justified. As
 ** contrapositive, a node is not relevant (with the may-notion) if all
 ** path from the root to the node go through a justified node.
 **/

#ifndef __CVC4__DECISION__RELEVANCY
#define __CVC4__DECISION__RELEVANCY

#include "decision_engine.h"
#include "decision_strategy.h"

#include "context/cdhashset.h"
#include "context/cdhashmap.h"
#include "expr/node.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {

namespace decision {

typedef std::vector<TNode> IteList;

class RelGiveUpException : public Exception {
public:
  RelGiveUpException() : 
    Exception("justification hueristic: giving up") {
  }
};/* class GiveUpException */

class Relevancy : public ITEDecisionStrategy {
  typedef hash_map<TNode,IteList,TNodeHashFunction> IteCache;
  typedef hash_map<TNode,TNode,TNodeHashFunction> SkolemMap;

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
  SkolemMap d_iteAssertions;
  // 'key' being TNode is fine since if a skolem didn't exist anywhere,
  // we won't look it up. as for 'value', same reason as d_assertions

  /** Cache for ITE skolems present in a atomic formula */
  IteCache d_iteCache;

  /**
   * This is used to prevent infinite loop when trying to find a
   * splitter. Can happen when exploring assertion corresponding to a
   * term-ITE.
   */
  hash_set<TNode,TNodeHashFunction> d_visited;

  /** 
   * May-relevancy of a node is an integer. For a node n, it becomes
   * irrelevant when d_maxRelevancy[n] = d_relevancy[n]
   */
  hash_map<TNode,int,TNodeHashFunction> d_maxRelevancy;
  context::CDHashMap<TNode,int,TNodeHashFunction> d_relevancy;

  /**
   * do we do "multiple-backtrace" to try to justify a node
   */
  bool d_computeRelevancy;     // are we in a mode where we compute relevancy?

  /** current decision for the recursive call */
  SatLiteral* d_curDecision;
public:
  Relevancy(CVC4::DecisionEngine* de, context::Context *c):
    ITEDecisionStrategy(de, c),
    d_justified(c),
    d_prvsIndex(c, 0),
    d_helfulness("decision::jh::helpfulness", 0),
    d_giveup("decision::jh::giveup", 0),
    d_timestat("decision::jh::time"),
    d_relevancy(c),
    d_computeRelevancy(true),
    d_curDecision(NULL)
  {
    StatisticsRegistry::registerStat(&d_helfulness);
    StatisticsRegistry::registerStat(&d_giveup);
    StatisticsRegistry::registerStat(&d_timestat);
    Trace("decision") << "Justification heuristic enabled" << std::endl;

  }
  ~Relevancy() {
    StatisticsRegistry::unregisterStat(&d_helfulness);
    StatisticsRegistry::unregisterStat(&d_timestat);
  }
  prop::SatLiteral getNext(bool &stopSearch) {
    Trace("decision") << "Relevancy::getNext()" << std::endl;
    TimerStat::CodeTimer codeTimer(d_timestat);

    d_visited.clear();

    for(unsigned i = d_prvsIndex; i < d_assertions.size(); ++i) {
      Trace("decision") << d_assertions[i] << std::endl;

      // Sanity check: if it was false, aren't we inconsistent?
      Assert( tryGetSatValue(d_assertions[i]) != SAT_VALUE_FALSE);

      SatValue desiredVal = SAT_VALUE_TRUE;
      SatLiteral litDecision = findSplitter(d_assertions[i], desiredVal);

      if(litDecision != undefSatLiteral)
        return litDecision;
    }

    Trace("decision") << "jh: Nothing to split on " << std::endl;

#if defined CVC4_ASSERTIONS || defined CVC4_DEBUG
    bool alljustified = true;
    for(unsigned i = 0 ; i < d_assertions.size() && alljustified ; ++i) {
      TNode curass = d_assertions[i];
      while(curass.getKind() == kind::NOT)
        curass = curass[0];
      alljustified &= checkJustified(curass);

      if(Debug.isOn("decision")) {
	if(!checkJustified(curass))
	  Debug("decision") << "****** Not justified [i="<<i<<"]: " 
                            << d_assertions[i] << std::endl;
      }
    }
    Assert(alljustified);
#endif

    // SAT solver can stop...
    stopSearch = true;
    d_decisionEngine->setResult(SAT_VALUE_TRUE);
    return prop::undefSatLiteral;
  }

  void traverseAssertion(TNode n) {
    d_maxRelevancy[n]++;
    for(unsigned i = 0; i < n.getNumChildren(); ++i)
      traverseAssertion(n[i]);
  }

  void addAssertions(const std::vector<Node> &assertions,
                     unsigned assertionsEnd,
                     IteSkolemMap iteSkolemMap) {
    Trace("decision")
      << "Relevancy::addAssertions()" 
      << " size = " << assertions.size()
      << " assertionsEnd = " << assertionsEnd
      << std::endl;

    // Save the 'real' assertions locally
    for(unsigned i = 0; i < assertionsEnd; ++i) {
      d_assertions.push_back(assertions[i]);
      traverseAssertion(assertions[i]);
    }

    // Save mapping between ite skolems and ite assertions
    for(IteSkolemMap::iterator i = iteSkolemMap.begin();
        i != iteSkolemMap.end(); ++i) {
      Assert(i->second >= assertionsEnd && i->second < assertions.size());
      Debug("jh-ite") << " jh-ite: " << (i->first) << " maps to "
                      << assertions[(i->second)] << std::endl;
      d_iteAssertions[i->first] = assertions[i->second];
      traverseAssertion(assertions[i->second]);
    }
  }

  /* Compute justified */
  /*bool computeJustified() {
    
  }*/
private:
  SatLiteral findSplitter(TNode node, SatValue desiredVal)
  {
    bool ret;
    SatLiteral litDecision;
    try {
      d_curDecision = &litDecision;
      ret = findSplitterRec(node, desiredVal);
      d_curDecision = NULL;
    }catch(RelGiveUpException &e) {
      return prop::undefSatLiteral;
    }
    if(ret == true) {
      Trace("decision") << "Yippee!!" << std::endl;
      //d_prvsIndex = i;
      ++d_helfulness;
      return litDecision;
    } else {
      return undefSatLiteral;
    }
  }
  
  /** 
   * Do all the hardwork. 
   * Return 'true' if the node cannot be justfied, 'false' it it can be.
   * Sets 'd_curDecision' if unable to justify (depending on the mode)
   * If 'd_computeRelevancy' is on does multiple backtrace
   */ 
  bool findSplitterRec(TNode node, SatValue value);
  // Functions to make findSplitterRec modular...
  bool handleOrFalse(TNode node, SatValue desiredVal);
  bool handleOrTrue(TNode node, SatValue desiredVal);
  bool handleITE(TNode node, SatValue desiredVal);

  /* Helper functions */
  void setJustified(TNode);
  bool checkJustified(TNode);
  
  /* If literal exists corresponding to the node return
     that. Otherwise an UNKNOWN */
  SatValue tryGetSatValue(Node n);

  /* Get list of all term-ITEs for the atomic formula v */
  const IteList& getITEs(TNode n);

  /* Compute all term-ITEs in a node recursively */
  void computeITEs(TNode n, IteList &l);
};/* class Relevancy */

}/* namespace decision */

}/* namespace CVC4 */

#endif /* __CVC4__DECISION__RELEVANCY */

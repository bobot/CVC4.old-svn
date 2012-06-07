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
#include "util/options.h"

namespace CVC4 {

namespace decision {

typedef std::vector<TNode> IteList;

class RelGiveUpException : public Exception {
public:
  RelGiveUpException() : 
    Exception("relevancy: giving up") {
  }
};/* class GiveUpException */

class Relevancy : public RelevancyStrategy {
  typedef hash_map<TNode,IteList,TNodeHashFunction> IteCache;
  typedef hash_map<TNode,TNode,TNodeHashFunction> SkolemMap;
  typedef hash_map<TNode,SatValue,TNodeHashFunction> PolarityCache;

  // being 'justified' is monotonic with respect to decisions
  context::CDHashSet<TNode,TNodeHashFunction> d_justified;
  context::CDO<unsigned>  d_prvsIndex;

  IntStat d_helfulness;
  IntStat d_polqueries;
  IntStat d_polhelp;
  IntStat d_giveup;
  IntStat d_expense;          /* Total number of nodes considered over
                                 all calls to the findSplitter function */
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
  PolarityCache d_polarityCache;

  /**  **** * * *** * * OPTIONS *** *  * ** * * **** */

  /**
   * do we do "multiple-backtrace" to try to justify a node
   */
  bool d_multipleBacktrace;
  bool d_computeRelevancy;     // are we in a mode where we compute relevancy?

  /** Only leaves can be relevant */
  bool d_relevancyLeaves;

  static const double secondsPerDecision = 0.001;
  static const double secondsPerExpense = 1e-7;
  static const double EPS = 1e-9;
  /** Maximum time this algorithm should spent as part of whole algorithm */
  double d_maxTimeAsPercentageOfTotalTime;

  /** current decision for the recursive call */
  SatLiteral* d_curDecision;
public:
  Relevancy(CVC4::DecisionEngine* de, context::Context *c, const Options::DecisionOptions &decOpt):
    RelevancyStrategy(de, c),
    d_justified(c),
    d_prvsIndex(c, 0),
    d_helfulness("decision::rel::preventedDecisions", 0),
    d_polqueries("decision::rel::polarityQueries", 0),
    d_polhelp("decision::rel::polarityHelp", 0),
    d_giveup("decision::rel::giveup", 0),
    d_expense("decision::rel::expense", 0),
    d_timestat("decision::rel::time"),
    d_relevancy(c),
    d_multipleBacktrace(true),
    d_computeRelevancy(true),
    d_relevancyLeaves(decOpt.relevancyLeaves),
    d_maxTimeAsPercentageOfTotalTime(decOpt.maxRelTimeAsPermille*1.0/10.0),
    d_curDecision(NULL)
  {
    StatisticsRegistry::registerStat(&d_helfulness);
    StatisticsRegistry::registerStat(&d_polqueries);
    StatisticsRegistry::registerStat(&d_polhelp);
    StatisticsRegistry::registerStat(&d_giveup);
    StatisticsRegistry::registerStat(&d_expense);
    StatisticsRegistry::registerStat(&d_timestat);
    Trace("decision") << "relevancy enabled with" << std::endl;
    Trace("decision") << "  * relevancyLeaves: " << (d_relevancyLeaves ? "on" : "off")
                      << std::endl;
  }
  ~Relevancy() {
    StatisticsRegistry::unregisterStat(&d_helfulness);
    StatisticsRegistry::unregisterStat(&d_polqueries);
    StatisticsRegistry::unregisterStat(&d_polhelp);
    StatisticsRegistry::unregisterStat(&d_giveup);
    StatisticsRegistry::unregisterStat(&d_expense);
    StatisticsRegistry::unregisterStat(&d_timestat);
  }
  prop::SatLiteral getNext(bool &stopSearch) {
    Debug("decision") << std::endl;
    Trace("decision") << "Relevancy::getNext()" << std::endl;
    TimerStat::CodeTimer codeTimer(d_timestat);

    if( d_maxTimeAsPercentageOfTotalTime < 100.0 - EPS &&
        double(d_polqueries.getData())*secondsPerDecision < 
          d_maxTimeAsPercentageOfTotalTime*double(d_expense.getData())*secondsPerExpense
      ) {
      ++d_giveup;
      return undefSatLiteral;
    }

    d_visited.clear();
    d_polarityCache.clear();

    for(unsigned i = d_prvsIndex; i < d_assertions.size(); ++i) {
      Trace("decision") << d_assertions[i] << std::endl;

      // Sanity check: if it was false, aren't we inconsistent?
      Assert( tryGetSatValue(d_assertions[i]) != SAT_VALUE_FALSE);

      SatValue desiredVal = SAT_VALUE_TRUE;
      SatLiteral litDecision = findSplitter(d_assertions[i], desiredVal);

      if(!d_computeRelevancy && litDecision != undefSatLiteral) {
        d_prvsIndex = i;
        return litDecision;
      }
    }
    if(d_computeRelevancy) return undefSatLiteral;

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

  void addAssertions(const std::vector<Node> &assertions,
                     unsigned assertionsEnd,
                     IteSkolemMap iteSkolemMap) {
    Trace("decision")
      << "Relevancy::addAssertions()" 
      << " size = " << assertions.size()
      << " assertionsEnd = " << assertionsEnd
      << std::endl;

    // Save mapping between ite skolems and ite assertions
    for(IteSkolemMap::iterator i = iteSkolemMap.begin();
        i != iteSkolemMap.end(); ++i) {
      Assert(i->second >= assertionsEnd && i->second < assertions.size());
      Debug("jh-ite") << " jh-ite: " << (i->first) << " maps to "
                      << assertions[(i->second)] << std::endl;
      d_iteAssertions[i->first] = assertions[i->second];
    }

    // Save the 'real' assertions locally
    for(unsigned i = 0; i < assertionsEnd; ++i) {
      d_assertions.push_back(assertions[i]);
      d_visited.clear();
      if(d_computeRelevancy) increaseMaxRelevancy(assertions[i]);
      d_visited.clear();
    }

  }

  bool isRelevant(TNode n) {
    Trace("decision") << "isRelevant(" << n << ")" << std::endl;
    if(Debug.isOn("decision")) {
      if(d_maxRelevancy.find(n) == d_maxRelevancy.end()) {
        // we are becuase of not getting information about literals
        // created using newLiteral command... need to figure how to
        // handle that
        Warning() << "isRelevant: WARNING: didn't find node when we should had" << std::endl;
        // Warning() doesn't work for some reason
        cout << "isRelevant: WARNING: didn't find node when we should had" << std::endl;
      }      
    }
    if(d_maxRelevancy.find(n) == d_maxRelevancy.end()) return true;
    if(d_relevancyLeaves && !isAtomicFormula(n)) return false;
    Debug("decision") << " maxRel: " << (d_maxRelevancy[n] )
                      << " rel: " << d_relevancy[n].get() << std::endl;
    // Assert(d_maxRelevancy.find(n) != d_maxRelevancy.end());
    Assert(0 <= d_relevancy[n] && d_relevancy[n] <= d_maxRelevancy[n]);
    if(d_maxRelevancy[n] == d_relevancy[n]) {
      ++d_helfulness; // preventedDecisions
      return false;
    } else {
      return true;
    }
  }

  SatValue getPolarity(TNode n) {
    Trace("decision") << "getPolarity([" << n.getId() << "]" << n << "): ";
    Assert(n.getKind() != kind::NOT);
    ++d_polqueries;
    PolarityCache::iterator it = d_polarityCache.find(n);
    if(it == d_polarityCache.end()) {
      Trace("decision") << "don't know" << std::endl;
      return SAT_VALUE_UNKNOWN;
    } else {
      ++d_polhelp;
      Trace("decision") << it->second << std::endl;
      return it->second;
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
      // init
      d_curDecision = &litDecision;
      
      // solve
      ret = findSplitterRec(node, desiredVal);

      // post
      d_curDecision = NULL;
    }catch(RelGiveUpException &e) {
      return prop::undefSatLiteral;
    }
    if(ret == true) {
      Trace("decision") << "Yippee!!" << std::endl;
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

  /* Checks whether something is an atomic formula or not */
  bool isAtomicFormula(TNode n) {
    return theory::kindToTheoryId(n.getKind()) != theory::THEORY_BOOL;
  }
  
  /** Recursively increase relevancies */
  void updateRelevancy(TNode n) {
    if(d_visited.find(n) != d_visited.end()) return;

    Assert(d_relevancy[n] <= d_maxRelevancy[n]);

    if(d_relevancy[n] != d_maxRelevancy[n])
      return;

    d_visited.insert(n);
    if(isAtomicFormula(n)) {
      const IteList& l = getITEs(n);
      for(unsigned i = 0; i < l.size(); ++i) {
        if(d_visited.find(l[i]) == d_visited.end()) continue;
        d_relevancy[l[i]] = d_relevancy[l[i]] + 1;
        updateRelevancy(l[i]);
      }
    } else {
      for(unsigned i = 0; i < n.getNumChildren(); ++i) {
        if(d_visited.find(n[i]) == d_visited.end()) continue;
        d_relevancy[n[i]] = d_relevancy[n[i]] + 1;
        updateRelevancy(n[i]);
      }
    }
    d_visited.erase(n);
  }

  /* */
  void increaseMaxRelevancy(TNode n) {

    Debug("decision") 
      << "increaseMaxRelevancy([" << n.getId() << "]" << n << ")" 
      << std::endl;    

    d_maxRelevancy[n]++;

    // don't update children multiple times
    if(d_visited.find(n) != d_visited.end()) return;
    
    d_visited.insert(n);
    // Part to make the recursive call
    if(isAtomicFormula(n)) {
      const IteList& l = getITEs(n);
      for(unsigned i = 0; i < l.size(); ++i)
        if(d_visited.find(l[i]) == d_visited.end())
          increaseMaxRelevancy(l[i]);
    } else {
      for(unsigned i = 0; i < n.getNumChildren(); ++i)
        increaseMaxRelevancy(n[i]);
    } //else (...atomic formula...)
  }

};/* class Relevancy */

}/* namespace decision */

}/* namespace CVC4 */

#endif /* __CVC4__DECISION__RELEVANCY */

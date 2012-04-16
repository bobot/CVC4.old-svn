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
  TNodeBoolMap justified;
  Node d_formula;
public:
  JustificationHeuristic(CVC4::DecisionEngine* de) : DecisionStrategy(de) {
    Trace("decision") << "Justification heuristic enabled" << std::endl;
  }
  prop::SatLiteral getNext() {
    Trace("decision") << "JustificationHeuristic::getNext()" << std::endl;

    findSplitterRec(d_formula, SAT_VALUE_TRUE);

    return prop::undefSatLiteral;
  } 
  bool needSimplifiedPreITEAssertions() { return true; }
  void notifyAssertionsAvailable() {
    // we do this here, but may be some/all of this needs to be done
    // in getNext()
    
    /* clear the justifcation labels -- reconsider if/when to do
       this */
    justified.clear();
    
    /* build a big AND formula from assertions */
    /*const vector<Node>& ass = d_decisionEngine->getAssertions();
    NodeBuilder<> b(kind::AND);
    for(int i = 0; ass.size(); ++i)
      b << ass[i];
      d_formula = b;*/
  }
private:
  /* Do all the hardwork. */ 
  SatLiteral findSplitterRec(Node n, SatValue val) {}
};/* class JustificationHeuristic */

}/* namespace decision */

}/* namespace CVC4 */

#endif /* __CVC4__DECISION__JUSTIFICATION_HEURISTIC */

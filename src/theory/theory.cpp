/*********************                                                        */
/*! \file theory.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base for theory interface.
 **
 ** Base for theory interface.
 **/

#include "theory/theory.h"
#include "util/Assert.h"
#include "theory/quantifiers_engine.h"
#include "theory/instantiator_default.h"

#include <vector>

using namespace std;

namespace CVC4 {
namespace theory {

/** Default value for the uninterpreted sorts is the UF theory */
TheoryId Theory::s_uninterpretedSortOwner = THEORY_UF;

std::ostream& operator<<(std::ostream& os, Theory::Effort level){
  switch(level){
  case Theory::EFFORT_STANDARD:
    os << "EFFORT_STANDARD"; break;
  case Theory::EFFORT_FULL:
    os << "EFFORT_FULL"; break;
  case Theory::EFFORT_COMBINATION:
    os << "EFFORT_COMBINATION"; break;
  case Theory::EFFORT_LAST_CALL:
    os << "EFFORT_LAST_CALL"; break;
  default:
      Unreachable();
  }
  return os;
}/* ostream& operator<<(ostream&, Theory::Effort) */

void Theory::addSharedTermInternal(TNode n) {
  Debug("sharing") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << std::endl;
  Debug("theory::assertions") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << std::endl;
  d_sharedTerms.push_back(n);
  addSharedTerm(n);
}

void Theory::computeCareGraph() {
  Debug("sharing") << "Theory::computeCareGraph<" << getId() << ">()" << std::endl;
  for (unsigned i = 0; i < d_sharedTerms.size(); ++ i) {
    TNode a = d_sharedTerms[i];
    TypeNode aType = a.getType();
    for (unsigned j = i + 1; j < d_sharedTerms.size(); ++ j) {
      TNode b = d_sharedTerms[j];
      if (b.getType() != aType) {
        // We don't care about the terms of different types
        continue;
      }
      switch (d_valuation.getEqualityStatus(a, b)) {
      case EQUALITY_TRUE_AND_PROPAGATED:
      case EQUALITY_FALSE_AND_PROPAGATED:
  	// If we know about it, we should have propagated it, so we can skip
  	break;
      default:
  	// Let's split on it
  	addCarePair(a, b);
  	break;
      }
    }
  }
}

Assertion Theory::get() {
  Assert( !done(), "Theory::get() called with assertion queue empty!" );

  // Get the assertion
  Assertion fact = d_facts[d_factsHead];
  d_factsHead = d_factsHead + 1;

  Trace("theory") << "Theory::get() => " << fact << " (" << d_facts.size() - d_factsHead << " left)" << std::endl;

  if(Dump.isOn("state")) {
    Dump("state") << AssertCommand(fact.assertion.toExpr());
  }

  // if quantifiers are turned on, notify the instantiator
  if(getInstantiator() != NULL) {
    getInstantiator()->assertNode(fact);
  }

  return fact;
}


void Theory::printFacts(std::ostream& os) const {
  unsigned i, n = d_facts.size();
  for(i = 0; i < n; i++){
    const Assertion& a_i = d_facts[i];
    Node assertion  = a_i;
    os << d_id << '[' << i << ']' << " " << assertion << endl;
  }
}

void Theory::debugPrintFacts() const{
  DebugChannel.getStream() << "Theory::debugPrintFacts()" << endl;
  printFacts(DebugChannel.getStream());
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

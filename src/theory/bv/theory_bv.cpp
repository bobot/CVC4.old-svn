/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"

#include "theory/valuation.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

using namespace std;

void TheoryBV::preRegisterTerm(TNode node) {

  Debug("bitvector") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (node.getKind() == kind::EQUAL) {
	// Add the terms to the equality manager 
    d_eqEngine.addTerm(node[0]);
    if (node[0].getKind() == kind::BITVECTOR_CONCAT) {
      for (unsigned i = 0, i_end = node[0].getNumChildren(); i < i_end; ++ i) {
        d_eqEngine.addTerm(node[0][i]);
      }
    }
    d_eqEngine.addTerm(node[1]);
    if (node[1].getKind() == kind::BITVECTOR_CONCAT) {
      for (unsigned i = 0, i_end = node[1].getNumChildren(); i < i_end; ++ i) {
        d_eqEngine.addTerm(node[1][i]);
      }
    }
    // Add to the watch manager
    d_watchManager.addEqualityToWatch(node[0], node[1]);
  }
}

void TheoryBV::check(Effort e) {

  Debug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;

  // Get all the assertions
  std::vector<TNode> assertionsList;
  while (!done()) {
    // Get the assertion
    TNode assertion = get();
    d_assertions.insert(assertion);
    assertionsList.push_back(assertion);
  }

  for (unsigned i = 0; i < assertionsList.size(); ++ i) {
    // Get the assertion
    TNode assertion = assertionsList[i];
    Debug("bitvector") << "TheoryBV::check(" << e << "): asserting: " << assertion << std::endl;
    // Do the right stuff
    switch (assertion.getKind()) {
    case kind::EQUAL: {
      // Slice and solve the equality, adding the equality information to the watch manager
      d_sliceManager.solveEquality(assertion[0], assertion[1]);
      // Above will add information to the watch manager so we run it now
      d_watchManager.propagate(d_eqEngine);
      break;
    }
    case kind::NOT: {
      // These will get propagated, so we do nothing
      break;
    }
    default:
      Unhandled(assertion.getKind());
    }
  }
}

Node TheoryBV::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryBV::explain(TNode node) {
  Debug("bitvector") << "TheoryBV::explain(" << node << ")" << std::endl;
  return;
}

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

  Debug("theory::bv") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (node.getKind() == kind::EQUAL) {
    // Add to the watch manager
    d_watchManager.addEqualityToWatch(node[0], node[1]);
  }
}

void TheoryBV::check(Effort e) {

  Debug("theory::bv") << "TheoryBV::check(" << e << ")" << std::endl;

  while (!done() && !d_out->inConflict()) {
    // Get the assertion
    TNode assertion = get();
    Debug("theory::bv") << "TheoryBV::check(" << e << "): asserting: " << assertion << std::endl;

    // Do initial checks and book-keeping
    if (d_assertions.find(assertion) != d_assertions.end()) {
      // Add to the assertion set and continue
      Debug("theory::bv") << "TheoryBV::check(" << e << "): already propagated." << std::endl;
      continue;
    } else {
      // If the negation is there we have a conflict
      TNode negation = utils::negate(assertion);
      if (d_assertions.find(negation) != d_assertions.end()) {
        Debug("theory::bv") << "TheoryBV::check() => conflict" << std::endl;
        std::vector<TNode> conflict;
        conflict.push_back(assertion);
        explainPropagation(negation, conflict);
        Debug("theory::bv") << "TheoryBV::check() => " << utils::mkConjunction(conflict) << std::endl;
        d_out->conflict(utils::mkConjunction(conflict));
        return;
      }
      // No conflict yet, add to the assertion set
      d_assertions.insert(assertion);
    }

    // Assert the assertion to the apropriate subtheory
    switch (assertion.getKind()) {
    case kind::EQUAL: {
      // Slice and solve the equality, adding the equality information to the watch manager
      d_sliceManager.solveEquality(assertion[0], assertion[1]);
      // Above will add information to the watch manager so we run it now
      d_watchManager.propagate();
      break;
    }
    case kind::NOT: {
      // These will get propagated for now, so we do nothing
      break;
    }
    default:
      Unhandled(assertion.getKind());
    }
  }
}

void TheoryBV::propagate(Effort level) {
  Debug("theory::bv") << "TheoryBV::propagate()" << std::endl;
  // Propagate all that is learned
  for(; d_toPropagateIndex < d_toPropagateList.size(); d_toPropagateIndex = d_toPropagateIndex + 1) {
    // This is what we've learned
    propagation_info propInfo = d_toPropagateList[d_toPropagateIndex];
    // If it's already been asserted, we go to the next
    if (d_assertions.find(propInfo.literal) != d_assertions.end()) {
      continue;
    }
    // Otherwise propagate
    d_out->propagate(propInfo.literal);
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

bool TheoryBV::propagate(const propagation_info& prop_info) {
  Debug("theory::bv") << "TheoryBV::propagate(" << prop_info.literal << ")" << std::endl;
  if (d_assertions.find(prop_info.literal) != d_assertions.end()) {
    // If already there, do nothing
    Debug("theory::bv") << "TheoryBV::propagate(" << prop_info.literal << ") => already propagated" << std::endl;
    return false;
  }
  Assert(d_propagationInfo.find(prop_info.literal) == d_propagationInfo.end());
  d_toPropagateList.push_back(prop_info);
  d_propagationInfo[prop_info.literal] = prop_info;
  d_assertions.insert(prop_info.literal);
  TNode negatedLiteral = utils::negate(prop_info.literal);
  if (d_assertions.find(negatedLiteral) != d_assertions.end()) {
    Debug("theory::bv") << "TheoryBV::propagate(" << prop_info.literal << ") => conflict" << std::endl;
    std::vector<TNode> conflict;
    conflict.push_back(negatedLiteral);
    explainPropagation(prop_info.literal, conflict);
    Debug("theory::bv") << "TheoryBV::propagate(" << prop_info.literal << ") => " << utils::mkConjunction(conflict) << std::endl;
    d_out->conflict(utils::mkConjunction(conflict));
    return true;
  }
  return false;
}

void TheoryBV::explainPropagation(TNode node, std::vector<TNode>& explanation) {
  // Get the propagation info
  Debug("theory::bv") << "TheoryBV::explainPropagation(" << node << ")" << std::endl;
  Assert(d_propagationInfo.find(node) != d_propagationInfo.end());
  propagation_info propInfo = d_propagationInfo[node];
  switch(propInfo.subTheory) {
  case EQUALITY_CORE:
    d_watchManager.explain(propInfo.info, explanation);
    break;
  default:
    Unreachable();
  }
}

void TheoryBV::explain(TNode node) {
  Debug("theory::bv") << "TheoryBV::explain(" << node << ")" << std::endl;
  std::vector<TNode> explanation;
  explainPropagation(node, explanation);
  d_out->explanation(utils::mkConjunction(explanation));
}

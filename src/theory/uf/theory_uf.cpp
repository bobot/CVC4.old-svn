/*********************                                                        */
/*! \file theory_uf.cpp
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
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine_impl.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

using namespace std;

Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}

void TheoryUF::check(Effort level) {

  // Assertions to process
  std::vector<TNode> toProcess;
  
  while (!done() && !d_conflict) {
    // Get all the assertions
    TNode assertion = get();
    // If propagated, we're done with it
    if (d_knownFacts.find(assertion) != d_knownFacts.end()) {
      continue;
    }
    // If negation is already known, we have a conflict
    TNode negatedAssertion = assertion.getKind() == kind::NOT ? assertion[0] : (TNode) assertion.notNode();
    if (d_knownFacts.find(negatedAssertion) != d_knownFacts.end()) {
      Debug("uf") << "TheoryUF::check(): conflict" << std::endl;
      std::vector<TNode> assumptions;
      assumptions.push_back(assertion);
      explain(negatedAssertion, assumptions);
      d_conflictNode = mkAnd(assumptions);
      d_conflict = true;
      break;
    }        
    // Add to processing list
    d_knownFacts.insert(assertion);
    toProcess.push_back(assertion);
  }
  
  // Process all the assertions
  for (unsigned i = 0; i < toProcess.size() && !d_conflict; ++ i) {
    
    // Get the assertion
    TNode assertion = toProcess[i];
    Debug("uf") << "TheoryUF::check(): processing " << assertion << std::endl;
	  
    switch (assertion.getKind()) {
    case kind::EQUAL:
      d_equalityEngine.addEquality(assertion[0], assertion[1], assertion);
      break;
    case kind::APPLY_UF:
      d_equalityEngine.addEquality(assertion, d_true, assertion);
    case kind::NOT:
      if (assertion[0].getKind() == kind::APPLY_UF) {
        d_equalityEngine.addEquality(assertion[0], d_false, assertion);
      }
      break;
    default:
      Unreachable();
    }
  }

  // If in conflict, output the conflict
  if (d_conflict) {
    Debug("uf") << "TheoryUF::check(): conflict " << d_conflictNode << std::endl;
    d_out->conflict(d_conflictNode);
    d_literalsToPropagate.clear();
  }
}

void TheoryUF::propagate(Effort level) {
  Debug("uf") << "TheoryUF::propagate()" << std::endl;
  if (!d_conflict) {
    for (unsigned i = 0; i < d_literalsToPropagate.size(); ++ i) {
      Debug("uf") << "TheoryUF::propagate(): propagating " << d_literalsToPropagate[i] << std::endl;
      d_out->propagate(d_literalsToPropagate[i]);
    }
  }
  d_literalsToPropagate.clear();
}

void TheoryUF::preRegisterTerm(TNode node) {
  Debug("uf") << "TheoryUF::preRegisterTerm(" << node << ")" << std::endl;

  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the terms
    d_equalityEngine.addTerm(node[0]);
    d_equalityEngine.addTerm(node[1]);
    // Add the trigger
    d_equalityEngine.addTriggerEquality(node[0], node[1], node);
    break;
  case kind::APPLY_UF:
    // Function applications/predicates
    d_equalityEngine.addTerm(node);
    // Maybe it's a predicate
    if (node.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerEquality(node, d_true, node);
      d_equalityEngine.addTriggerEquality(node, d_false, node.notNode());
    }
  default:
    // Variables etc
    d_equalityEngine.addTerm(node);
    break;
  }
}

bool TheoryUF::propagate(TNode atom, bool isTrue) {
  Debug("uf") << "TheoryUF::propagate(" << atom << ", " << (isTrue ? "true" : "false" ) << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("uf") << "TheoryUF::propagate(" << atom << ", " << (isTrue ? "true" : "false" ) << "): already in conflict" << std::endl;
    return false;
  }

  // The literal
  TNode literal = isTrue ? (Node) atom : atom.notNode();
  TNode negatedLiteral = isTrue ? atom.notNode() : (Node) atom;

  // If asserted, we're done
  if (d_knownFacts.find(literal) != d_knownFacts.end()) {
    Debug("uf") << "TheoryUF::propagate(" << atom << ", " << (isTrue ? "true" : "false" ) << ") => already known" << std::endl;
    return true;
  }

  // If negated asserted, we're in conflict
  if (literal == d_false || d_knownFacts.find(negatedLiteral) != d_knownFacts.end()) {
    Debug("uf") << "TheoryUF::propagate(" << atom << ", " << (isTrue ? "true" : "false" ) << ") => conflict" << std::endl;
    std::vector<TNode> assumptions;
    if (literal != d_false) {
      assumptions.push_back(negatedLiteral);
    }
    explain(literal, assumptions);
    d_conflictNode = mkAnd(assumptions);
    d_conflict = true;
    return false;
  }

  // Nothing, just enqueue it for propagation and mark it as asserted already
  Debug("uf") << "TheoryUF::propagate(" << atom << ", " << (isTrue ? "true" : "false" ) << ") => enqueuing for propagation" << std::endl;
  d_literalsToPropagate.push_back(literal);
  d_knownFacts.insert(literal);

  return true;
}

void TheoryUF::explain(TNode literal, std::vector<TNode>& assumptions) {
  TNode lhs, rhs;
  switch (literal.getKind()) {
    case kind::EQUAL:
      lhs = literal[0];
      rhs = literal[1];
      break;
    case kind::APPLY_UF:
      lhs = literal;
      rhs = d_true;
      break;
    case kind::NOT:
      lhs = literal[0];
      rhs = d_false;
    case kind::CONST_BOOLEAN:
      // we get to explain true = false, since we set false to be the trigger of this
      lhs = d_true;
      rhs = d_false;
      break;
    default:
      Unreachable();
  }
  d_equalityEngine.getExplanation(lhs, rhs, assumptions);
}

void TheoryUF::explain(TNode literal) {
  Debug("uf") << "TheoryUF::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  d_out->explanation(mkAnd(assumptions));
}

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

  while (!done() && !d_conflict) {
    // Get all the assertions
    TNode assertion = get();
    Debug("uf") << "TheoryUF::check(): processing " << assertion << std::endl;

    // Fo the work
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

  // Otherwise we propagate in order to detect a weird conflict like
  // p, x = y
  // p -> f(x) != f(y) -- f(x) = f(y) gets added to the propagation list at preregistration time
  // but when f(x) != f(y) is deduced by the sat solver, so it's asserted, and we don't detect the conflict
  // until we go through the propagation list
  propagate(level);
}

void TheoryUF::propagate(Effort level) {
  Debug("uf") << "TheoryUF::propagate()" << std::endl;
  if (!d_conflict) {
    for (unsigned i = 0; i < d_literalsToPropagate.size(); ++ i) {
      TNode literal = d_literalsToPropagate[i];
      Debug("uf") << "TheoryUF::propagate(): propagating " << literal << std::endl;
      bool satValue;
      if (!d_valuation.hasSatValue(literal, satValue)) {
        d_out->propagate(literal);
      } else {
        std::vector<TNode> assumptions;
        if (literal != d_false) {
          TNode negatedLiteral = literal.getKind() == kind::NOT ? literal[0] : (TNode) literal.notNode();
          assumptions.push_back(negatedLiteral);
        }
        explain(literal, assumptions);
        d_conflictNode = mkAnd(assumptions);
        d_conflict = true;
        break;
      }
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

  // See if the literal has been asserted already
  bool satValue = false;
  bool isAsserted = literal == d_false || d_valuation.hasSatValue(literal, satValue);

  // If asserted, we're done or in conflict
  if (isAsserted) {
    if (satValue) {
      Debug("uf") << "TheoryUF::propagate(" << atom << ", " << (isTrue ? "true" : "false" ) << ") => already known" << std::endl;
      return true;
    } else {
      Debug("uf") << "TheoryUF::propagate(" << atom << ", " << (isTrue ? "true" : "false" ) << ") => conflict" << std::endl;
      std::vector<TNode> assumptions;
      if (literal != d_false) {
        TNode negatedLiteral = isTrue ? atom.notNode() : (Node) atom;
        assumptions.push_back(negatedLiteral);
      }
      explain(literal, assumptions);
      d_conflictNode = mkAnd(assumptions);
      d_conflict = true;
      return false;
    }
  }

  // Nothing, just enqueue it for propagation and mark it as asserted already
  Debug("uf") << "TheoryUF::propagate(" << atom << ", " << (isTrue ? "true" : "false" ) << ") => enqueuing for propagation" << std::endl;
  d_literalsToPropagate.push_back(literal);

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

void TheoryUF::presolve() {
  // TimerStat::CodeTimer codeTimer(d_presolveTimer);

  Debug("uf") << "uf: begin presolve()" << endl;
  if(Options::current()->ufSymmetryBreaker) {
    vector<Node> newClauses;
    d_symb.apply(newClauses);
    for(vector<Node>::const_iterator i = newClauses.begin();
        i != newClauses.end();
        ++i) {
      d_out->lemma(*i);
    }
  }
  Debug("uf") << "uf: end presolve()" << endl;
}

void TheoryUF::staticLearning(TNode n, NodeBuilder<>& learned) {
  if(Options::current()->ufSymmetryBreaker) {
    d_symb.assertFormula(n);
  }
}


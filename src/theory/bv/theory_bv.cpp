/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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
#include "theory/bv/bv_sat.h"
#include "theory/uf/equality_engine_impl.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::context;

using namespace std;
using namespace CVC4::theory::bv::utils;


const bool d_useEqualityEngine = false;
const bool d_useSatPropagation = true;


TheoryBV::TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation)
  : Theory(THEORY_BV, c, u, out, valuation),
    d_context(c),
    d_assertions(c),
    d_bitblaster(new Bitblaster(c, this) ),
    d_statistics(),
    d_alreadyPropagatedSet(c),
    d_notify(*this),
    d_equalityEngine(d_notify, c, "theory::bv::TheoryBV"),
    d_conflict(c, false),
    d_literalsToPropagate(c),
    d_literalsToPropagateIndex(c, 0),
    d_toBitBlast(c),
    d_propagator(c)
  {
    d_true = utils::mkTrue();
    d_false = utils::mkFalse();

    if (d_useEqualityEngine) {
      d_equalityEngine.addTerm(d_true);
      d_equalityEngine.addTerm(d_false);
      d_equalityEngine.addTriggerEquality(d_true, d_false, d_false);

      // The kinds we are treating as function application in congruence
      d_equalityEngine.addFunctionKind(kind::BITVECTOR_CONCAT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_AND);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_OR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_XOR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NOT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NAND);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NOR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_XNOR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_COMP);
      d_equalityEngine.addFunctionKind(kind::BITVECTOR_MULT);
      d_equalityEngine.addFunctionKind(kind::BITVECTOR_PLUS);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SUB);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NEG);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_UDIV);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_UREM);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SDIV);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SREM);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SMOD);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SHL);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_LSHR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_ASHR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_ULT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_ULE);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_UGT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_UGE);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SLT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SLE);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SGT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SGE);

    }
  }

TheoryBV::~TheoryBV() {
  delete d_bitblaster; 
}
TheoryBV::Statistics::Statistics():
  d_avgConflictSize("theory::bv::AvgBVConflictSize"),
  d_solveSubstitutions("theory::bv::NumberOfSolveSubstitutions", 0),
  d_solveTimer("theory::bv::solveTimer")
{
  StatisticsRegistry::registerStat(&d_avgConflictSize);
  StatisticsRegistry::registerStat(&d_solveSubstitutions);
  StatisticsRegistry::registerStat(&d_solveTimer); 
}

TheoryBV::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_avgConflictSize);
  StatisticsRegistry::unregisterStat(&d_solveSubstitutions);
  StatisticsRegistry::unregisterStat(&d_solveTimer); 
}

void TheoryBV::preRegisterTerm(TNode node) {
  BVDebug("bitvector-preregister") << "TheoryBV::preRegister(" << node << ")" << std::endl;
  if (node.getKind() == kind::EQUAL ||
      node.getKind() == kind::BITVECTOR_ULT ||
      node.getKind() == kind::BITVECTOR_ULE ||
      node.getKind() == kind::BITVECTOR_SLT ||
      node.getKind() == kind::BITVECTOR_SLE) {
    d_bitblaster->bbAtom(node);
  }

  if (d_useEqualityEngine) {
    switch (node.getKind()) {
      case kind::EQUAL:
        // Add the terms
        d_equalityEngine.addTerm(node);
        // Add the trigger for equality
        d_equalityEngine.addTriggerEquality(node[0], node[1], node);
        d_equalityEngine.addTriggerDisequality(node[0], node[1], node.notNode());
        break;
      default:
        d_equalityEngine.addTerm(node);
        break;
    }
  }

}

void TheoryBV::check(Effort e)
{
  BVDebug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;

  while (!done() && !d_conflict) {
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    BVDebug("bitvector-assertions") << "TheoryBV::check assertion " << fact << "\n"; 

    // If the assertion doesn't have a literal, it's a shared equality
    bool shared = !assertion.isPreregistered;

    // Notify the equality engine
    if (d_useEqualityEngine && (d_propagator.find(fact) == d_propagator.end() ||
                                d_propagator[fact] != SUB_EQUALITY)) {
      
      bool negated = fact.getKind() == kind::NOT; 
      Node predicate = negated ? fact[0] : fact;
      
      Assert(!shared ||
             (predicate.getKind() == kind::EQUAL &&
              d_equalityEngine.hasTerm(predicate[0]) &&
              d_equalityEngine.hasTerm(predicate[1]))); 

      if (predicate.getKind() == kind::EQUAL) {
        // Adding (dis)equality
        if (negated) {
          d_equalityEngine.addDisequality(predicate[0], predicate[1], fact); 
        } else {
          d_equalityEngine.addEquality(predicate[0], predicate[1], fact); 
        }
      } else {
        // Adding predicate
        if (d_equalityEngine.isFunctionKind(predicate.getKind())) {
          d_equalityEngine.addPredicate(predicate, !negated, fact); 
        }
      }
    }

    // Bit-blaster
    if (!d_conflict) {
      PropagatedMap::const_iterator find = d_propagator.find(fact);
      if (find == d_propagator.end() || (*find).second != SUB_BITBLASTER) {
        // Some atoms have not been bit-blasted yet
        d_bitblaster->bbAtom(fact);
        // Assert to sat
        bool ok = d_bitblaster->assertToSat(fact, d_useSatPropagation);
        if (!ok) {
          std::vector<TNode> conflictAtoms;
          d_bitblaster->getConflict(conflictAtoms);
          d_statistics.d_avgConflictSize.addEntry(conflictAtoms.size());
          d_conflict = true;
          d_conflictNode = mkConjunction(conflictAtoms);
          break;
        }
      }
    }
  }

  // If in conflict, output the conflict
  if (d_conflict) {
    BVDebug("bitvector") << spaces(getContext()->getLevel()) << "TheoryBV::check(): conflict " << d_conflictNode << std::endl;
    d_out->conflict(d_conflictNode);
    return;
  }

  if (e == EFFORT_FULL) {
    Assert(done() && !d_conflict);
    BVDebug("bitvector") << "TheoryBV::check " << e << "\n";
    bool ok = d_bitblaster->solve();
    if (!ok) {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      d_statistics.d_avgConflictSize.addEntry(conflictAtoms.size());
      Node conflict = mkConjunction(conflictAtoms);
      d_out->conflict(conflict);
      BVDebug("bitvector") << "TheoryBV::check returns conflict: " <<conflict <<" \n ";
      return; 
    }
  }
}


Node TheoryBV::getValue(TNode n) {
  //NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    Unhandled(kind::VARIABLE);

  default:
    Unhandled(n.getKind());
  }
}


void TheoryBV::propagate(Effort e) {

  BVDebug("bitvector") << spaces(getContext()->getLevel()) << "TheoryBV::propagate()" << std::endl;

  if (d_conflict) {
    return;
  }

  // get new propagations from the equality engine
  for (; d_literalsToPropagateIndex < d_literalsToPropagate.size(); d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1)
  {
    TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
    BVDebug("bitvector") << spaces(getContext()->getLevel()) << "TheoryBV::propagate(): propagating from equality engine: " << literal << std::endl;
    bool satValue;

    Node normalized = Rewriter::rewrite(literal);

    if (!d_valuation.hasSatValue(normalized, satValue) || satValue) {
      if (!satValue) {
        d_out->propagate(literal);
      }
    } else {
      Debug("bitvector") << spaces(getContext()->getLevel()) << "TheoryBV::propagate(): in conflict, normalized = " << normalized << std::endl;

      Node negatedLiteral;
      std::vector<TNode> assumptions;
      if (normalized != d_false) {
        negatedLiteral = normalized.getKind() == kind::NOT ? (Node) normalized[0] : normalized.notNode();
        assumptions.push_back(negatedLiteral);
      }
      explain(literal, d_propagator[literal], assumptions);
      d_conflictNode = mkAnd(assumptions);
      d_conflict = true;
      return;
    }
  }
}

Theory::PPAssertStatus TheoryBV::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  switch(in.getKind()) {
  case kind::EQUAL:
    
    if (in[0].getMetaKind() == kind::metakind::VARIABLE && !in[1].hasSubterm(in[0])) {
      ++(d_statistics.d_solveSubstitutions); 
      outSubstitutions.addSubstitution(in[0], in[1]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].getMetaKind() == kind::metakind::VARIABLE && !in[0].hasSubterm(in[1])) {
      ++(d_statistics.d_solveSubstitutions); 
      outSubstitutions.addSubstitution(in[1], in[0]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    // to do constant propagations

    break;
  case kind::NOT:
    break;
  default:
    // TODO other predicates
    break;
  }
  return PP_ASSERT_STATUS_UNSOLVED;
}


bool TheoryBV::storePropagation(TNode literal, SubTheory subtheory)
{
  Debug("bitvector") << spaces(getContext()->getLevel()) << "TheoryBV::propagate(" << literal  << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("bitvector") << spaces(getContext()->getLevel()) << "TheoryBV::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }

  // See if the literal has been asserted already
  bool satValue = false;
  bool hasSatValue = d_valuation.hasSatValue(literal, satValue);

  // If asserted, we might be in conflict
  if (hasSatValue) {
    if (!satValue) {
      Debug("bitvector") << spaces(getContext()->getLevel()) << "TheoryBV::propagate(" << literal << ") => conflict" << std::endl;
      std::vector<TNode> assumptions;
      Node negatedLiteral = literal.getKind() == kind::NOT ? (Node) literal[0] : literal.notNode();
      assumptions.push_back(negatedLiteral);
      explain(literal, subtheory, assumptions);
      d_conflictNode = mkAnd(assumptions);
      d_conflict = true;
      return false;
    } else {
      // Propagate even if already known in SAT - could be a new equation between shared terms
    }
  } else {

  }

  // Nothing, just enqueue it for propagation and mark it as asserted already
  Debug("bitvector") << spaces(getContext()->getLevel()) << "TheoryBV::propagate(" << literal << ") => enqueuing for propagation" << std::endl;
  d_literalsToPropagate.push_back(literal);

  return true;
}/* TheoryBV::propagate(TNode) */


void TheoryBV::explain(TNode literal, SubTheory subtheory, std::vector<TNode>& assumptions) {

  if (subtheory == SUB_EQUALITY) {
    TNode lhs, rhs;
    switch (literal.getKind()) {
      case kind::EQUAL:
        lhs = literal[0];
        rhs = literal[1];
        break;
      case kind::NOT:
        if (literal[0].getKind() == kind::EQUAL) {
          // Disequalities
          d_equalityEngine.explainDisequality(literal[0][0], literal[0][1], assumptions);
          return;
        } else {
          // Predicates
          lhs = literal[0];
          rhs = d_false;
          break;
        }
      case kind::CONST_BOOLEAN:
        // we get to explain true = false, since we set false to be the trigger of this
        lhs = d_true;
        rhs = d_false;
        break;
      default:
        Unreachable();
    }
    d_equalityEngine.explainEquality(lhs, rhs, assumptions);
  } else if (subtheory == SUB_BITBLASTER) {
    d_bitblaster->explain(literal, assumptions); 
  }
}


Node TheoryBV::explain(TNode node) {
  BVDebug("bitvector") << "TheoryBV::explain(" << node << ")" << std::endl;
  std::vector<TNode> assumptions;

  // check who has propagated the node
  SubTheory subtheory = d_propagator[node];

  // Ask for the explanation
  explain(node, subtheory, assumptions);

  // return the explanation
  return mkAnd(assumptions);
}


void TheoryBV::addSharedTerm(TNode t) {
  Debug("bitvector::sharing") << spaces(getContext()->getLevel()) << "TheoryBV::addSharedTerm(" << t << ")" << std::endl;
  if (d_useEqualityEngine) {
    d_equalityEngine.addTriggerTerm(t);
  }
}


EqualityStatus TheoryBV::getEqualityStatus(TNode a, TNode b)
{
  if (d_useEqualityEngine) {
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  return EQUALITY_UNKNOWN;
}


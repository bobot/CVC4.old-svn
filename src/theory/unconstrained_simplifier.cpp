/*********************                                                        */
/*! \file unconstrained_simplifier.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simplifications based on unconstrained variables
 **
 ** This module implements a preprocessing phase which replaces certain "unconstrained" expressions
 ** by variables.  Based on Roberto Bruttomesso's PhD thesis.
 **/


#include "theory/unconstrained_simplifier.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4;
using namespace theory;


UnconstrainedSimplifier::UnconstrainedSimplifier(context::Context* context,
                                                 const LogicInfo& logicInfo)
  : d_numUnconstrainedElim("preprocessor::number of unconstrained elims", 0),
    d_context(context), d_substitutions(context), d_logicInfo(logicInfo)
{
  StatisticsRegistry::registerStat(&d_numUnconstrainedElim);
}


UnconstrainedSimplifier::~UnconstrainedSimplifier()
{
  StatisticsRegistry::unregisterStat(&d_numUnconstrainedElim);    
}


struct unc_preprocess_stack_element {
  TNode node;
  TNode parent;
  unc_preprocess_stack_element(TNode n) : node(n) {}
  unc_preprocess_stack_element(TNode n, TNode p) : node(n), parent(p) {}
};/* struct unc_preprocess_stack_element */


void UnconstrainedSimplifier::visitAll(TNode assertion)
{
  // Do a topological sort of the subexpressions and substitute them
  vector<unc_preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  while (!toVisit.empty())
  {
    // The current node we are processing
    unc_preprocess_stack_element& stackHead = toVisit.back();
    toVisit.pop_back();
    TNode current = stackHead.node;

    TNodeCountMap::iterator find = d_visited.find(current);
    if (find != d_visited.end()) {
      if (find->second == 1) {
        d_visitedOnce.erase(current);
        if (current.isVar()) {
          d_unconstrained.erase(current);
        }
      }
      ++find->second;
      continue;
    }

    d_visited[current] = 1;
    d_visitedOnce[current] = stackHead.parent;

    if (current.getNumChildren() == 0) {
      if (current.isVar()) {
        d_unconstrained.insert(current);
      }
    }
    else {
      for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
        TNode childNode = *child_it;
        toVisit.push_back(unc_preprocess_stack_element(childNode, current));
      }
    }
  }
}

Node UnconstrainedSimplifier::newUnconstrainedVar(TypeNode t, TNode var)
{
  Node n = NodeManager::currentNM()->mkVar(t);
  Dump.declareVar(n.toExpr(), "a new var introduced because of unconstrained variable " + var.toString());
  return n;
}


void UnconstrainedSimplifier::processUnconstrained()
{
  TNodeSet::iterator it = d_unconstrained.begin(), iend = d_unconstrained.end();
  vector<TNode> workList;
  for ( ; it != iend; ++it) {
    workList.push_back(*it);
  }
  Node currentSub;
  TNode parent;
  bool swap;
  bool isSigned;
  bool strict;
  vector<TNode> delayQueueLeft;
  vector<Node> delayQueueRight;

  TNode current = workList.back();
  workList.pop_back();
  for (;;) {
    Assert(d_visitedOnce.find(current) != d_visitedOnce.end());
    parent = d_visitedOnce[current];
    if (!parent.isNull()) {
      swap = isSigned = strict = false;
      switch (parent.getKind()) {

        // If-then-else operator - any two unconstrained children makes the parent unconstrained
        case kind::ITE: {
          Assert(parent[0] == current || parent[1] == current || parent[2] == current);
          bool uCond = parent[0] == current || d_unconstrained.find(parent[0]) != d_unconstrained.end();
          bool uThen = parent[1] == current || d_unconstrained.find(parent[1]) != d_unconstrained.end();
          bool uElse = parent[2] == current || d_unconstrained.find(parent[2]) != d_unconstrained.end();
          if ((uCond && uThen) || (uCond && uElse) || (uThen && uElse)) {
            if (d_unconstrained.find(parent) == d_unconstrained.end() &&
                !d_substitutions.hasSubstitution(parent)) {
              ++d_numUnconstrainedElim;
              if (uThen) {
                if (parent[1] != current) {
                  if (parent[1].isVar()) {
                    currentSub = parent[1];
                  }
                  else {
                    Assert(d_substitutions.hasSubstitution(parent[1]));
                    currentSub = d_substitutions.apply(parent[1]);
                  }
                }
                else if (currentSub.isNull()) {
                  currentSub = current;
                }
              }
              else if (parent[2] != current) {
                if (parent[2].isVar()) {
                  currentSub = parent[2];
                }
                else {
                  Assert(d_substitutions.hasSubstitution(parent[2]));
                  currentSub = d_substitutions.apply(parent[2]);
                }
              }
              else if (currentSub.isNull()) {
                currentSub = current;
              }
              current = parent;
            }
            else {
              currentSub = Node();
            }
          }
          else if (uCond && parent.getType().getCardinality().isFinite() && parent.getType().getCardinality().getFiniteCardinality() == 2) {
            // Special case: condition is unconstrained, then and else are different, and total cardinality of the type is 2, then the result
            // is unconstrained
            Node test;
            if (parent.getType().isBoolean()) {
              test = Rewriter::rewrite(parent[1].iffNode(parent[2]));
            }
            else {
              test = Rewriter::rewrite(parent[1].eqNode(parent[2]));
            }
            if (test == NodeManager::currentNM()->mkConst<bool>(false)) {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull()) {
                currentSub = current;
              }
              currentSub = newUnconstrainedVar(parent.getType(), currentSub);
              current = parent;
            }
          }
          break;
        }

        // Comparisons that return a different type - assuming domains are larger than 1, any
        // unconstrained child makes parent unconstrained as well
        case kind::EQUAL:
          if (parent[0].getType() != parent[1].getType()) {
            TNode other = (parent[0] == current) ? parent[1] : parent[0];
            if (current.getType().isSubtypeOf(other.getType())) {
              break;
            }
          }
        case kind::BITVECTOR_COMP:
        case kind::LT:
        case kind::LEQ:
        case kind::GT:
        case kind::GEQ:
        {
          if (d_unconstrained.find(parent) == d_unconstrained.end() &&
              !d_substitutions.hasSubstitution(parent)) {
            ++d_numUnconstrainedElim;
            Assert(parent[0] != parent[1] &&
                   (parent[0] == current || parent[1] == current));
            if (currentSub.isNull()) {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            current = parent;
          }
          else {
            currentSub = Node();
          }
          break;
        }

        // Unary operators that propagate unconstrainedness
        case kind::NOT:
        case kind::BITVECTOR_NOT:
        case kind::BITVECTOR_NEG:
        case kind::UMINUS:
          ++d_numUnconstrainedElim;
          Assert(parent[0] == current);
          if (currentSub.isNull()) {
            currentSub = current;
          }
          current = parent;
          break;

        // Unary operators that propagate unconstrainedness and return a different type
        case kind::BITVECTOR_EXTRACT:
          ++d_numUnconstrainedElim;
          Assert(parent[0] == current);
          if (currentSub.isNull()) {
            currentSub = current;
          }
          currentSub = newUnconstrainedVar(parent.getType(), currentSub);
          current = parent;
          break;

        // Operators returning same type requiring all children to be unconstrained
        case kind::AND:
        case kind::OR:
        case kind::IMPLIES:
        case kind::BITVECTOR_AND:
        case kind::BITVECTOR_OR:
        case kind::BITVECTOR_NAND:
        case kind::BITVECTOR_NOR:
        {
          bool allUnconstrained = true;
          for(TNode::iterator child_it = parent.begin(); child_it != parent.end(); ++child_it) {
            if (d_unconstrained.find(*child_it) == d_unconstrained.end()) {
              allUnconstrained = false;
              break;
            }
          }
          if (allUnconstrained) {
            if (d_unconstrained.find(parent) == d_unconstrained.end() &&
                !d_substitutions.hasSubstitution(parent)) {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull()) {
                currentSub = current;
              }
              current = parent;
            }
            else {
              currentSub = Node();
            }
          }
        }
        break;

        // Require all children to be unconstrained and different
        case kind::BITVECTOR_SHL:
        case kind::BITVECTOR_LSHR:
        case kind::BITVECTOR_ASHR:
        case kind::BITVECTOR_UDIV:
        case kind::BITVECTOR_UREM:
        case kind::BITVECTOR_SDIV:
        case kind::BITVECTOR_SREM:
        case kind::BITVECTOR_SMOD: {
          bool allUnconstrained = true;
          bool allDifferent = true;
          for(TNode::iterator child_it = parent.begin(); child_it != parent.end(); ++child_it) {
            if (d_unconstrained.find(*child_it) == d_unconstrained.end()) {
              allUnconstrained = false;
              break;
            }
            for(TNode::iterator child_it2 = child_it + 1; child_it2 != parent.end(); ++child_it2) {
              if (*child_it == *child_it2) {
                allDifferent = false;
                break;
              }
            }
          }
          if (allUnconstrained && allDifferent) {
            if (d_unconstrained.find(parent) == d_unconstrained.end() &&
                !d_substitutions.hasSubstitution(parent)) {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull()) {
                currentSub = current;
              }
              current = parent;
            }
            else {
              currentSub = Node();
            }
          }
          break;
        }

        // Requires all children to be unconstrained and different, and returns a different type
        case kind::BITVECTOR_CONCAT:
        {
          bool allUnconstrained = true;
          bool allDifferent = true;
          for(TNode::iterator child_it = parent.begin(); child_it != parent.end(); ++child_it) {
            if (d_unconstrained.find(*child_it) == d_unconstrained.end()) {
              allUnconstrained = false;
              break;
            }
            for(TNode::iterator child_it2 = child_it + 1; child_it2 != parent.end(); ++child_it2) {
              if (*child_it == *child_it2) {
                allDifferent = false;
                break;
              }
            }
          }
          if (allUnconstrained && allDifferent) {
            if (d_unconstrained.find(parent) == d_unconstrained.end() &&
                !d_substitutions.hasSubstitution(parent)) {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull()) {
                currentSub = current;
              }
              currentSub = newUnconstrainedVar(parent.getType(), currentSub);
              current = parent;
            }
            else {
              currentSub = Node();
            }
          }
        }
        break;

        // N-ary operators returning same type requiring at least one child to be unconstrained
        case kind::PLUS:
        case kind::MINUS:
          if (current.getType().isInteger() &&
              !parent.getType().isInteger()) {
            break;
          }
        case kind::IFF:
        case kind::XOR:
        case kind::BITVECTOR_XOR:
        case kind::BITVECTOR_XNOR:
        case kind::BITVECTOR_PLUS:
        case kind::BITVECTOR_SUB:
          if (d_unconstrained.find(parent) == d_unconstrained.end() &&
              !d_substitutions.hasSubstitution(parent)) {
            ++d_numUnconstrainedElim;
            if (currentSub.isNull()) {
              currentSub = current;
            }
            current = parent;
          }
          else {
            currentSub = Node();
          }
          break;

        // Multiplication/division: must be non-integer and other operand must be non-zero
        case kind::MULT: {
        case kind::DIVISION:
          Assert(parent.getNumChildren() == 2);
          TNode other;
          if (parent[0] == current) {
            other = parent[1];
          }
          else {
            Assert(parent[1] == current);
            other = parent[0];
          }
          if (d_unconstrained.find(other) != d_unconstrained.end()) {
            if (d_unconstrained.find(parent) == d_unconstrained.end() &&
                !d_substitutions.hasSubstitution(parent)) {
              if (current.getType().isInteger() && other.getType().isInteger()) {
                Assert(parent.getKind() == kind::DIVISION || parent.getType().isInteger());
                if (parent.getKind() == kind::DIVISION) {
                  break;
                }
              }
              ++d_numUnconstrainedElim;
              if (currentSub.isNull()) {
                currentSub = current;
              }
              current = parent;
            }
            else {
              currentSub = Node();
            }
          }
          else {
            // if only the denominator of a division is unconstrained, can't set it to 0 so the result is not unconstrained
            if (parent.getKind() == kind::DIVISION && current == parent[1]) {
              break;
            }
            NodeManager* nm = NodeManager::currentNM();
            // if we are an integer, the only way we are unconstrained is if we are a MULT by -1
            if (current.getType().isInteger()) {
              // div/mult by 1 should have been simplified
              Assert(other != nm->mkConst<Rational>(1));
              if (other == nm->mkConst<Rational>(-1)) {
                // div by -1 should have been simplified
                Assert(parent.getKind() == kind::MULT);
                Assert(parent.getType().isInteger());
              }
              else {
                break;
              }
            }
            else {
              // TODO: could build ITE here
              Node test = other.eqNode(nm->mkConst<Rational>(0));
              if (Rewriter::rewrite(test) != nm->mkConst<bool>(false)) {
                break;
              }
            }
            ++d_numUnconstrainedElim;
            if (currentSub.isNull()) {
              currentSub = current;
            }
            current = parent;
          }
          break;
        }

        // Bitvector MULT - current must only appear once in the children:
        // all other children must be unconstrained or odd
        case kind::BITVECTOR_MULT:
        {
          bool found = false;
          bool done = false;
          for(TNode::iterator child_it = parent.begin(); child_it != parent.end(); ++child_it) {
            if ((*child_it) == current) {
              if (found) {
                done = true;
                break;
              }
              found = true;
              continue;
            }
            else if (d_unconstrained.find(*child_it) != d_unconstrained.end()) {
              continue;
            }
            else {
              NodeManager* nm = NodeManager::currentNM();
              Node extractOp = nm->mkConst<BitVectorExtract>(BitVectorExtract(0,0));
              vector<Node> children;
              children.push_back(*child_it);
              Node test = nm->mkNode(extractOp, children);
              BitVector one(1,unsigned(1));
              test = test.eqNode(nm->mkConst<BitVector>(one));
              if (Rewriter::rewrite(test) != nm->mkConst<bool>(true)) {
                done = true;
                break;
              }
            }
          }
          if (done) {
            break;
          }
          if (d_unconstrained.find(parent) == d_unconstrained.end() &&
              !d_substitutions.hasSubstitution(parent)) {
            ++d_numUnconstrainedElim;
            if (currentSub.isNull()) {
              currentSub = current;
            }
            current = parent;
          }
          else {
            currentSub = Node();
          }
          break;
        }

        // Uninterpreted function - if domain is infinite, no quantifiers are used, and any child is unconstrained, result is unconstrained
        case kind::APPLY_UF:
          if (d_logicInfo.isQuantified() || !current.getType().getCardinality().isInfinite()) {
            break;
          }
          if (d_unconstrained.find(parent) == d_unconstrained.end() &&
              !d_substitutions.hasSubstitution(parent)) {
            ++d_numUnconstrainedElim;
            if (currentSub.isNull()) {
              currentSub = current;
            }
            if (parent.getType() != current.getType()) {
              currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            }
            current = parent;
          }
          else {
            currentSub = Node();
          }
          break;

        // Array select - if array is unconstrained, so is result
        case kind::SELECT:
          if (parent[0] == current) {
            ++d_numUnconstrainedElim;
            Assert(current.getType().isArray());
            if (currentSub.isNull()) {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(current.getType().getArrayConstituentType(), currentSub);
            current = parent;
          }
          break;

        // Array store - if both store and value are unconstrained, so is resulting store
        case kind::STORE:
          if (((parent[0] == current &&
                d_unconstrained.find(parent[2]) != d_unconstrained.end()) ||
               (parent[2] == current &&
                d_unconstrained.find(parent[0]) != d_unconstrained.end()))) {
            if (d_unconstrained.find(parent) == d_unconstrained.end() &&
                !d_substitutions.hasSubstitution(parent)) {
              ++d_numUnconstrainedElim;
              if (parent[0] != current) {
                if (parent[0].isVar()) {
                  currentSub = parent[0];
                }
                else {
                  Assert(d_substitutions.hasSubstitution(parent[0]));
                  currentSub = d_substitutions.apply(parent[0]);
                }
              }
              else if (currentSub.isNull()) {
                currentSub = current;
              }
              current = parent;
            }
            else {
              currentSub = Node();
            }
          }
          break;

        // Bit-vector comparisons: replace with new Boolean variable, but have to also conjoin with a side condition
        // as there is always one case when the comparison is forced to be false
        case kind::BITVECTOR_ULT:
          strict = true;
        case kind::BITVECTOR_UGE:
          goto bvineq;

        case kind::BITVECTOR_UGT:
          strict = true;
        case kind::BITVECTOR_ULE:
          swap = true;
          goto bvineq;

        case kind::BITVECTOR_SLT:
          strict = true;
        case kind::BITVECTOR_SGE:
          isSigned = true;
          goto bvineq;

        case kind::BITVECTOR_SGT:
          strict = true;
        case kind::BITVECTOR_SLE:
          isSigned = true;
          swap = true;

        bvineq: {
          TNode other;
          bool left = false;
          if (parent[0] == current) {
            other = parent[1];
            left = true;
          }
          else {
            Assert(parent[1] == current);
            other = parent[0];
          }
          if (d_unconstrained.find(other) != d_unconstrained.end()) {
            if (d_unconstrained.find(parent) == d_unconstrained.end() &&
                !d_substitutions.hasSubstitution(parent)) {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull()) {
                currentSub = current;
              }
              currentSub = newUnconstrainedVar(parent.getType(), currentSub);
              current = parent;
            }
            else {
              currentSub = Node();
            }
          }
          else {
            unsigned size = current.getType().getBitVectorSize();
            BitVector bv = isSigned ? BitVector(size, Integer(1).multiplyByPow2(size - 1)) : BitVector(size, unsigned(0));
            if (swap == left) {
              bv = ~bv;
            }
            if (currentSub.isNull()) {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            current = parent;
            NodeManager* nm = NodeManager::currentNM();
            Node test = Rewriter::rewrite(other.eqNode(nm->mkConst<BitVector>(bv)));
            if (test == nm->mkConst<bool>(false)) {
              break;
            }
            if (strict) {
              currentSub = currentSub.andNode(test.notNode());
            }
            else {
              currentSub = currentSub.orNode(test);
            }
            // Delay adding this substitution - see comment at end of function
            delayQueueLeft.push_back(current);
            delayQueueRight.push_back(currentSub);
            currentSub = Node();
            parent = TNode();
          }
          break;
        }

        // These should have been rewritten up front
        case kind::BITVECTOR_REPEAT:
        case kind::BITVECTOR_ZERO_EXTEND:
        case kind::BITVECTOR_ROTATE_LEFT:
        case kind::BITVECTOR_ROTATE_RIGHT:
          Unreachable();
          break;

        // Do nothing
        case kind::BITVECTOR_SIGN_EXTEND:
        default:
          break;
      }
      if (current == parent && d_visited[parent] == 1) {
        d_unconstrained.insert(parent);
        continue;
      }
    }
    if (!currentSub.isNull()) {
      Assert(currentSub.isVar());
      d_substitutions.addSubstitution(current, currentSub, false);
    }
    if (workList.empty()) {
      break;
    }
    current = workList.back();
    currentSub = Node();
    workList.pop_back();
  }
  TNode left;
  Node right;
  // All substitutions except those arising from bitvector comparisons are
  // substitutions t -> x where x is a variable.  This allows us to build the
  // substitution very quickly (never invalidating the substitution cache).
  // Bitvector comparisons are more complicated and may require
  // back-substitution and cache-invalidation.  So we do these last.
  while (!delayQueueLeft.empty()) {
    left = delayQueueLeft.back();
    if (!d_substitutions.hasSubstitution(left)) {
      right = d_substitutions.apply(delayQueueRight.back());
      d_substitutions.addSubstitution(delayQueueLeft.back(), right);
    }
    delayQueueLeft.pop_back();
    delayQueueRight.pop_back();
  }
}


void UnconstrainedSimplifier::processAssertions(vector<Node>& assertions)
{
  d_context->push();

  vector<Node>::iterator it = assertions.begin(), iend = assertions.end();
  for (; it != iend; ++it) {
    visitAll(*it);
  }

  if (!d_unconstrained.empty()) {
    processUnconstrained();
    //    d_substitutions.print(Message.getStream());
    for (it = assertions.begin(); it != iend; ++it) {
      (*it) = Rewriter::rewrite(d_substitutions.apply(*it));
    }
  }

  // to clear substitutions map
  d_context->pop();

  d_visited.clear();
  d_visitedOnce.clear();
  d_unconstrained.clear();
}

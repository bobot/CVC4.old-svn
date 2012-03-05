/*********************                                                        */
/*! \file theory_bv_rewriter.cpp
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

#include "theory/theory.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_rewrite_rules_core.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewrite_rules_constant_evaluation.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

RewriteResponse TheoryBVRewriter::postRewrite(TNode node) {
  
  BVDebug("bitvector") << "TheoryBV::postRewrite(" << node << ")" << std::endl;
    
  Node result = node;

  if (node.getKind() == kind::CONST_BITVECTOR ||
      (node.getKind() != kind::EQUAL && Theory::isLeafOf(node, THEORY_BV))) {
    result = node;
  }
  else {
    result = operatorEliminationRewrites(node);
    result = constantEvaluationRewrites(result);
    result = simplificationRewrites(result);
    result = normalizationRewrites(result);
    if (node.getType().isBitVector()) {
      Assert(utils::getSize(result) == utils::getSize(node));
    }
  }

  BVDebug("bitvector") << "TheoryBV::postRewrite(" << node << ") => " << result << std::endl;
  
  return RewriteResponse(REWRITE_DONE, result);
}


Node TheoryBVRewriter::operatorEliminationRewrites(TNode node) {
  Node result = node;

  switch(node.getKind()) {
    case kind::CONST_BITVECTOR:
      // nothing to do
      result = node;
      break;
    case kind::BITVECTOR_UGT:
      result = LinearRewriteStrategy <
                  RewriteRule<UgtToUlt>
               >::apply(node);
      break;

    case kind::BITVECTOR_UGE:
      result = LinearRewriteStrategy <
                  RewriteRule<UgeToUle>
               >::apply(node);
      break;
    case kind::BITVECTOR_SGT:
      result = LinearRewriteStrategy <
                  RewriteRule<SgtToSlt>
               >::apply(node);
      break;
    case kind::BITVECTOR_SGE:
      result = LinearRewriteStrategy <
                  RewriteRule<SgeToSle>
               >::apply(node);
      break;
    case kind::BITVECTOR_REPEAT:
      result = LinearRewriteStrategy <
                  RewriteRule<RepeatEliminate>
               >::apply(node);
      break;
    case kind::BITVECTOR_ROTATE_RIGHT:
      result = LinearRewriteStrategy <
                  RewriteRule<RotateRightEliminate>
               >::apply(node);
      break;
    case kind::BITVECTOR_ROTATE_LEFT:
      result = LinearRewriteStrategy <
                  RewriteRule<RotateLeftEliminate>
               >::apply(node);
      break;
    case kind::BITVECTOR_NAND:
      result = LinearRewriteStrategy <
                  RewriteRule<NandEliminate>
               >::apply(node);
      break;
    case kind::BITVECTOR_NOR:
      result = LinearRewriteStrategy <
                  RewriteRule<NorEliminate>
               >::apply(node);
      break;

    case kind::BITVECTOR_SDIV:
      result = LinearRewriteStrategy <
                  RewriteRule<SdivEliminate>
               >::apply(node);
      break;
  case kind::BITVECTOR_SREM:
      result = LinearRewriteStrategy <
                  RewriteRule<SremEliminate>
               >::apply(node);
     break;
    case kind::BITVECTOR_SMOD:
      result = LinearRewriteStrategy <
                  RewriteRule<SmodEliminate>
                >::apply(node);
      break;
    case kind::BITVECTOR_ZERO_EXTEND:
      result = LinearRewriteStrategy <
                  RewriteRule<ZeroExtendEliminate>
                >::apply(node);
      break;
  default:
      result = node; 
  }

  return result; 
}

Node TheoryBVRewriter::constantEvaluationRewrites(TNode node){
  Node result = node;

  if (!utils::isBVGroundTerm(node)) {
    return result; 
  }
  
  switch(node.getKind()) {
  case kind::CONST_BITVECTOR:
    // do nothing
    break;
  case kind::EQUAL:
    result = LinearRewriteStrategy< RewriteRule<EvalEquals> >::apply(node); 
  case kind::BITVECTOR_CONCAT:
    result = LinearRewriteStrategy< RewriteRule<EvalConcat> >::apply(node); 
    break;
  case kind::BITVECTOR_AND:
    result = LinearRewriteStrategy< RewriteRule<EvalAnd> >::apply(node); 
    break;
  case kind::BITVECTOR_OR:
    result = LinearRewriteStrategy< RewriteRule<EvalOr> >::apply(node); 
    break;
  case kind::BITVECTOR_XOR:
    result = LinearRewriteStrategy< RewriteRule<EvalXor> >::apply(node); 
    break;
  case kind::BITVECTOR_XNOR:
    result = LinearRewriteStrategy< RewriteRule<EvalXnor> >::apply(node); 
    break;
  case kind::BITVECTOR_NOT:
    result = LinearRewriteStrategy< RewriteRule<EvalNot> >::apply(node); 
    break;
  case kind::BITVECTOR_COMP:
    result = LinearRewriteStrategy< RewriteRule<EvalComp> >::apply(node); 
    break;
  case kind::BITVECTOR_MULT:
    result = LinearRewriteStrategy< RewriteRule<EvalMult> >::apply(node); 
    break;
  case kind::BITVECTOR_PLUS:
    result = LinearRewriteStrategy< RewriteRule<EvalPlus> >::apply(node); 
    break;
  case kind::BITVECTOR_SUB:
    result = LinearRewriteStrategy< RewriteRule<EvalSub> >::apply(node); 
    break;
  case kind::BITVECTOR_NEG:
    result = LinearRewriteStrategy< RewriteRule<EvalNeg> >::apply(node); 
    break;
  case kind::BITVECTOR_UDIV:
    result = LinearRewriteStrategy< RewriteRule<EvalUdiv> >::apply(node); 
    break;
  case kind::BITVECTOR_UREM:
    result = LinearRewriteStrategy< RewriteRule<EvalUrem> >::apply(node); 
    break;
  case kind::BITVECTOR_SHL:
    result = LinearRewriteStrategy< RewriteRule<EvalShl> >::apply(node); 
    break;
  case kind::BITVECTOR_LSHR:
    result = LinearRewriteStrategy< RewriteRule<EvalLshr> >::apply(node); 
    break;
  case kind::BITVECTOR_ASHR:
    result = LinearRewriteStrategy< RewriteRule<EvalAshr> >::apply(node); 
    break;
  case kind::BITVECTOR_ULT:
    result = LinearRewriteStrategy< RewriteRule<EvalUlt> >::apply(node); 
    break;
  case kind::BITVECTOR_SLT:
    result = LinearRewriteStrategy< RewriteRule<EvalSlt> >::apply(node); 
    break;
  case kind::BITVECTOR_SLE:
    result = LinearRewriteStrategy< RewriteRule<EvalSle> >::apply(node); 
    break;
  case kind::BITVECTOR_ULE:
    result = LinearRewriteStrategy< RewriteRule<EvalUle> >::apply(node); 
    break;
  case kind::BITVECTOR_EXTRACT:
    result = LinearRewriteStrategy< RewriteRule<EvalExtract> >::apply(node); 
    break;
  case kind::BITVECTOR_SIGN_EXTEND:
    result = LinearRewriteStrategy< RewriteRule<EvalSignExtend> >::apply(node); 
    break;
  default:
    Unhandled(node.getKind()); 
  }
  
  return result; 
}

Node TheoryBVRewriter::simplificationRewrites(TNode node) {
  Node result = node;
  return result; 
}

Node TheoryBVRewriter::normalizationRewrites(TNode node) {
  Node result = node;
  switch (node.getKind()) {
    case kind::BITVECTOR_CONCAT:
      result = LinearRewriteStrategy<
                  // Flatten the top level concatenations
                  RewriteRule<ConcatFlatten>,
                  // Merge the adjacent extracts on non-constants
                  RewriteRule<ConcatExtractMerge>,
                  // Merge the adjacent extracts on constants
                  RewriteRule<ConcatConstantMerge>,
                  // At this point only Extract-Whole could apply, if the result is only one extract
                  // or at some sub-expression if the result is a concatenation.
                  ApplyRuleToChildren<kind::BITVECTOR_CONCAT, ExtractWhole>
               >::apply(node);
      break;
    case kind::BITVECTOR_EXTRACT:
      result = LinearRewriteStrategy<
                  // Extract over a concatenation is distributed to the appropriate concatenations
                  RewriteRule<ExtractConcat>,
                  // Extract over a constant gives a constant
                  RewriteRule<ExtractConstant>,
                  // We could get another extract over extract
                  RewriteRule<ExtractExtract>,
                  // At this point only Extract-Whole could apply
                  RewriteRule<ExtractWhole>
                >::apply(node);
      break;
    case kind::EQUAL:
      result = LinearRewriteStrategy<
                  // Two distinct values rewrite to false
                  RewriteRule<FailEq>,
                  // If both sides are equal equality is true
                  RewriteRule<SimplifyEq>,
                  // Eliminate the equalities
                  RewriteRule<ReflexivityEq>
                >::apply(node);
      break;
    default:
      result = node;
      break;
      }

  
  return result; 
}



CVC4_THREADLOCAL(AllRewriteRules*) TheoryBVRewriter::s_allRules = NULL;

void TheoryBVRewriter::init() {
  s_allRules = new AllRewriteRules;
}

void TheoryBVRewriter::shutdown() {
  delete s_allRules;
}

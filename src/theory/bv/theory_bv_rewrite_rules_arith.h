/*********************                                                        */
/*! \file theory_bv_rewrite_rules_core.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
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

#include "cvc4_private.h"

#pragma once

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

template<>
bool RewriteRule<UgtToUlt>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UGT);
}

template<>
Node RewriteRule<UgtToUlt>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgtToUlt>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_ULT, b, a);
  return result;
}


template<>
bool RewriteRule<UgeToUle>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UGE);
}

template<>
Node RewriteRule<UgeToUle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgeToUle>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_ULE, b, a);
  return result;
}


template<>
bool RewriteRule<SgtToSlt>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SGT);
}

template<>
Node RewriteRule<SgtToSlt>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgtToUlt>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_SLT, b, a);
  return result;
}


template<>
bool RewriteRule<SgeToSle>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SGE);
}

template<>
Node RewriteRule<SgeToSle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SgeToSle>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_SLE, b, a);
  return result;
}


template<>
bool RewriteRule<UleSplit>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULE);
}

template<>
Node RewriteRule<UleSplit>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UleSplit>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node eq = utils::mkNode(kind::EQUAL, a, b);
  Node lt = utils::mkNode(kind::BITVECTOR_ULT, a, b); 
  Node result = utils::mkNode(kind::OR, eq, lt);
  return result;
}

template<>
bool RewriteRule<SleSplit>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SLE);
}

template<>
Node RewriteRule<SleSplit>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SleSplit>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node eq = utils::mkNode(kind::EQUAL, a, b);
  Node lt = utils::mkNode(kind::BITVECTOR_SLT, a, b); 
  Node result = utils::mkNode(kind::OR, eq, lt);
  return result;
}

template<>
bool RewriteRule<RepeatNormalize>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_REPEAT);
}

template<>
Node RewriteRule<RepeatNormalize>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<RepeatNormalize>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount = node.getOperator().getConst<BitVectorRepeat>().repeatAmount;
  Assert(amount >= 1);
  if(amount == 1) {
    return a; 
  }
  NodeBuilder<> result(kind::BITVECTOR_CONCAT);
  for(unsigned i = 0; i < amount; ++i) {
    result << node[0]; 
  }
  Node resultNode = result; 
  return resultNode;
}

template<>
bool RewriteRule<RotateLeftNormalize>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ROTATE_LEFT);
}

template<>
Node RewriteRule<RotateLeftNormalize>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<RotateLeftNormalize>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount = node.getOperator().getConst<BitVectorRotateLeft>().rotateLeftAmount;
  amount = amount % utils::getSize(a); 
  if (amount == 0) {
    return a; 
  }

  Node left   = utils::mkExtract(a, utils::getSize(a)-1 - amount, 0);
  Node right  = utils::mkExtract(a, utils::getSize(a) -1, utils::getSize(a) - amount);
  Node result = utils::mkConcat(left, right);

  return result;
}

template<>
bool RewriteRule<RotateRightNormalize>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ROTATE_RIGHT);
}

template<>
Node RewriteRule<RotateRightNormalize>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<RotateRightNormalize>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount = node.getOperator().getConst<BitVectorRotateRight>().rotateRightAmount;
  amount = amount % utils::getSize(a); 
  if (amount == 0) {
    return a; 
  }
  
  Node left  = utils::mkExtract(a, amount - 1, 0);
  Node right = utils::mkExtract(a, utils::getSize(a)-1, amount);
  Node result = utils::mkConcat(left, right);

  return result;
}

template<>
bool RewriteRule<NandNormalize>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NAND);
}

template<>
Node RewriteRule<NandNormalize>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NandNormalize>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1]; 
  Node andNode = utils::mkNode(kind::BITVECTOR_AND, a, b);
  Node result = utils::mkNode(kind::BITVECTOR_NOT, andNode); 
  return result;
}

template<>
bool RewriteRule<NorNormalize>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NOR);
}

template<>
Node RewriteRule<NorNormalize>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NorNormalize>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1]; 
  Node orNode = utils::mkNode(kind::BITVECTOR_OR, a, b);
  Node result = utils::mkNode(kind::BITVECTOR_NOT, orNode); 
  return result;
}

template<>
bool RewriteRule<SdivNormalize>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SDIV);
}

template<>
Node RewriteRule<SdivNormalize>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SdivNormalize>(" << node << ")" << std::endl;

  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);
  
  Node one     = utils::mkConst(1, 1);
  Node a_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(a, size-1, size-1), one);
  Node b_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(b, size-1, size-1), one); 
  Node abs_a   = utils::mkNode(kind::ITE, a_lt_0, utils::mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b   = utils::mkNode(kind::ITE, b_lt_0, utils::mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_udiv_b   = utils::mkNode(kind::BITVECTOR_UDIV, abs_a, abs_b);
  Node neg_result = utils::mkNode(kind::BITVECTOR_NEG, a_udiv_b);
  
  Node condition = utils::mkNode(kind::XOR, a_lt_0, b_lt_0);
  Node result    = utils::mkNode(kind::ITE, condition, neg_result, a_udiv_b);
  
  return result;
}


template<>
bool RewriteRule<SremNormalize>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SREM);
}

template<>
Node RewriteRule<SremNormalize>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SremNormalize>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);
  
  Node one     = utils::mkConst(1, 1);
  Node a_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(a, size-1, size-1), one);
  Node b_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(b, size-1, size-1), one); 
  Node abs_a   = utils::mkNode(kind::ITE, a_lt_0, utils::mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b   = utils::mkNode(kind::ITE, b_lt_0, utils::mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_urem_b   = utils::mkNode(kind::BITVECTOR_UREM, abs_a, abs_b);
  Node neg_result = utils::mkNode(kind::BITVECTOR_NEG, a_urem_b);
  
  Node result    = utils::mkNode(kind::ITE, a_lt_0, neg_result, a_urem_b);

  return result;
}

template<>
bool RewriteRule<SmodNormalize>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SMOD);
}

template<>
Node RewriteRule<SmodNormalize>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SmodNormalize>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);
  
  Node one     = utils::mkConst(1, 1);
  Node zero    = utils::mkConst(1, 0);
  Node a_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(a, size-1, size-1), one);
  Node b_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(b, size-1, size-1), one);
  
  Node a_gte_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(a, size-1, size-1), zero);
  Node b_gte_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(b, size-1, size-1), zero); 

  Node abs_a   = utils::mkNode(kind::ITE, a_lt_0, utils::mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b   = utils::mkNode(kind::ITE, b_lt_0, utils::mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_urem_b   = utils::mkNode(kind::BITVECTOR_UREM, abs_a, abs_b);
  Node neg_rem = utils::mkNode(kind::BITVECTOR_NEG, a_urem_b);

  
  Node aneg_bpos = utils::mkNode(kind::AND, a_lt_0, b_gte_0);
  Node apos_bneg = utils::mkNode(kind::AND, a_gte_0, b_lt_0);
  Node aneg_bneg = utils::mkNode(kind::AND, a_lt_0, b_lt_0);
                                 
  Node result = utils::mkNode(kind::ITE, aneg_bpos, utils::mkNode(kind::BITVECTOR_PLUS, neg_rem, b), 
                              utils::mkNode(kind::ITE, apos_bneg, utils::mkNode(kind::BITVECTOR_PLUS, a_urem_b, b),
                                            utils::mkNode(kind::ITE, aneg_bneg, neg_rem,
                                                             a_urem_b)));
  return result;
}


template<>
bool RewriteRule<DivZeroGuard>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UDIV ||
          node.getKind() == kind::BITVECTOR_UREM ||
          node.getKind() == kind::BITVECTOR_SDIV ||
          node.getKind() == kind::BITVECTOR_SREM ||
          node.getKind() == kind::BITVECTOR_SMOD);
}

template<>
Node RewriteRule<DivZeroGuard>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<DivZeroGuard>(" << node << ")" << std::endl;

  TNode divisor = node[1];
  Node fresh_var = utils::mkVar(utils::getSize(node));
  Node zero = utils::mkConst(utils::getSize(node), 0); 

  Node cond = utils::mkNode(kind::NOT, utils::mkNode(kind::EQUAL, node[0], zero));
  Node result = utils::mkNode(kind::ITE, cond, node, fresh_var); 
  
  return result;
}




}
}
}

/*********************                                                        */
/*! \file theory_bv_rewrite_rules_simplification.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): 
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

// FIXME: this rules subsume the constant evaluation ones


/**
 * ShlByConst
 *
 * Left Shift by constant amount 
 */
template<>
bool RewriteRule<ShlByConst>::applies(Node node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_SHL &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<>
Node RewriteRule<ShlByConst>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ShlByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return 0
    return utils::mkConst(BitVector(size, Integer(0)));
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));
  
  uint32_t uint32_amount = amount.toUnsignedInt();
  Node left = utils::mkExtract(a, size - 1 - uint32_amount, 0);
  Node right = utils::mkConst(BitVector(uint32_amount, Integer(0))); 
  return utils::mkConcat(left, right); 
}

/**
 * LshrByConst
 *
 * Right Logical Shift by constant amount 
 */

template<>
bool RewriteRule<LshrByConst>::applies(Node node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_LSHR &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<>
Node RewriteRule<LshrByConst>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<LshrByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return 0
    return utils::mkConst(BitVector(size, Integer(0)));
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));
  
  uint32_t uint32_amount = amount.toUnsignedInt();
  Node right = utils::mkExtract(a, size - 1, uint32_amount);
  Node left = utils::mkConst(BitVector(uint32_amount, Integer(0))); 
  return utils::mkConcat(left, right); 
}

/**
 * AshrByConst
 *
 * Right Arithmetic Shift by constant amount 
 */

template<>
bool RewriteRule<AshrByConst>::applies(Node node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_ASHR &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<>
Node RewriteRule<AshrByConst>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<AshrByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  Node sign_bit = utils::mkExtract(a, size-1, size-1);
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return n repetitions
    // of the first bit
    return utils::mkConcat(sign_bit, size); 
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));

  uint32_t uint32_amount = amount.toUnsignedInt();
  if (uint32_amount == 0) {
    return a; 
  }
  
  Node left = utils::mkConcat(sign_bit, uint32_amount); 
  Node right = utils::mkExtract(a, size - 1, uint32_amount);
  return utils::mkConcat(left, right); 
}

/**
 * BitwiseIdemp
 *
 * (a bvand a) ==> a
 * (a bvor a)  ==> a
 */

template<>
bool RewriteRule<BitwiseIdemp>::applies(Node node) {
  return ((node.getKind() == kind::BITVECTOR_AND ||
           node.getKind() == kind::BITVECTOR_OR) &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<BitwiseIdemp>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<BitwiseIdemp>(" << node << ")" << std::endl;
  return node[0]; 
}

/**
 * XorDuplicate
 *
 * (a bvxor a) ==> 0
 */

template<>
bool RewriteRule<XorDuplicate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_XOR &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<XorDuplicate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorDuplicate>(" << node << ")" << std::endl;
  return utils::mkConst(BitVector(utils::getSize(node), Integer(0))); 
}

/**
 * BitwiseNegAnd
 *
 * (a bvand (~ a)) ==> 0
 */

template<>
bool RewriteRule<BitwiseNegAnd>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_AND &&
          ((node[0].getKind() == kind::BITVECTOR_NOT && node[0][0] == node[1]) ||
           (node[1].getKind() == kind::BITVECTOR_NOT && node[1][0] == node[0]))); 
}

template<>
Node RewriteRule<BitwiseNegAnd>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<BitwiseNegAnd>(" << node << ")" << std::endl;
  return utils::mkConst(BitVector(utils::getSize(node), Integer(0))); 
}

/**
 * BitwiseNegOr
 *
 * (a bvor (~ a)) ==> 1
 */

template<>
bool RewriteRule<BitwiseNegOr>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_OR &&
          ((node[0].getKind() == kind::BITVECTOR_NOT && node[0][0] == node[1]) ||
           (node[1].getKind() == kind::BITVECTOR_NOT && node[1][0] == node[0]))); 
}

template<>
Node RewriteRule<BitwiseNegOr>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<BitwiseNegOr>(" << node << ")" << std::endl;
  uint32_t size = utils::getSize(node);
  Integer ones = Integer(1).multiplyByPow2(size) - 1; 
  return utils::mkConst(BitVector(size, ones)); 
}

/**
 * XorNeg
 *
 * ((~ a) bvxor (~ b)) ==> (a bvxor b)
 */

template<>
bool RewriteRule<XorNeg>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_XOR &&
          node[0].getKind() == kind::BITVECTOR_NOT &&
          node[1].getKind() == kind::BITVECTOR_NOT); 
}

template<>
Node RewriteRule<XorNeg>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorNeg>(" << node << ")" << std::endl;
  Node a = node[0][0];
  Node b = node[1][0]; 
  return utils::mkNode(kind::BITVECTOR_XOR, a, b); 
}

/**
 * LtSelf
 *
 * a < a ==> false
 */

template<>
bool RewriteRule<LtSelf>::applies(Node node) {
  return ((node.getKind() == kind::BITVECTOR_ULT ||
           node.getKind() == kind::BITVECTOR_SLT) &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<LtSelf>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<LtSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}

/**
 * LteSelf
 *
 * a <= a ==> true
 */

template<>
bool RewriteRule<LteSelf>::applies(Node node) {
  return ((node.getKind() == kind::BITVECTOR_ULE ||
           node.getKind() == kind::BITVECTOR_SLE) &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<LteSelf>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<LteSelf>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * UltZero
 *
 * a < 0 ==> false
 */

template<>
bool RewriteRule<UltZero>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<>
Node RewriteRule<UltZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UltZero>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}

/**
 * UleZero
 *
 * a <= 0 ==> a = 0
 */

template<>
bool RewriteRule<UleZero>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<>
Node RewriteRule<UleZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UleZero>(" << node << ")" << std::endl;
  return utils::mkNode(kind::EQUAL, node[0], node[1]); 
}

/**
 * ZeroUle
 *
 * 0 <= a ==> true
 */

template<>
bool RewriteRule<ZeroUle>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<>
Node RewriteRule<ZeroUle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ZeroUle>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * UleMax
 *
 * a <= 11..1 ==> true
 */

template<>
bool RewriteRule<UleMax>::applies(Node node) {
  if (node.getKind()!= kind::BITVECTOR_ULE) {
    return false; 
  }
  uint32_t size = utils::getSize(node[0]); 
  Integer ones = Integer(1).multiplyByPow2(size) -1; 
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkConst(BitVector(size, ones)));
}

template<>
Node RewriteRule<UleMax>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UleMax>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * NotUlt
 *
 * ~ ( a < b) ==> b <= a
 */

template<>
bool RewriteRule<NotUlt>::applies(Node node) {
  return (node.getKind() == kind::NOT &&
          node[0].getKind() == kind::BITVECTOR_ULT);
}

template<>
Node RewriteRule<NotUlt>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NotUlt>(" << node << ")" << std::endl;
  Node ult = node[0];
  Node a = ult[0];
  Node b = ult[1]; 
  return utils::mkNode(kind::BITVECTOR_ULE, b, a); 
}

/**
 * NotUle
 *
 * ~ ( a <= b) ==> b < a
 */

template<>
bool RewriteRule<NotUle>::applies(Node node) {
  return (node.getKind() == kind::NOT &&
          node[0].getKind() == kind::BITVECTOR_ULE);
}

template<>
Node RewriteRule<NotUle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NotUle>(" << node << ")" << std::endl;
  Node ult = node[0];
  Node a = ult[0];
  Node b = ult[1]; 
  return utils::mkNode(kind::BITVECTOR_ULT, b, a); 
}



}
}
}

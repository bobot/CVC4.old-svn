/*********************                                                        */
/*! \file theory_bv_rewrite_rules_core.h
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

template<>
bool RewriteRule<UgtEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UGT);
}

template<>
Node RewriteRule<UgtEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgtEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_ULT, b, a);
  return result;
}


template<>
bool RewriteRule<UgeEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UGE);
}

template<>
Node RewriteRule<UgeEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgeEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_ULE, b, a);
  return result;
}


template<>
bool RewriteRule<SgtEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SGT);
}

template<>
Node RewriteRule<SgtEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RgewriteRule<UgtEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_SLT, b, a);
  return result;
}


template<>
bool RewriteRule<SgeEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SGE);
}

template<>
Node RewriteRule<SgeEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<SgeEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_SLE, b, a);
  return result;
}

template <>
bool RewriteRule<SltEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLT); 
}

template <>
Node RewriteRule<SltEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<SltEliminate>(" << node << ")" << std::endl;
  
  unsigned size = utils::getSize(node[0]);
  Node pow_two = utils::mkConst(BitVector(size, Integer(1).multiplyByPow2(size - 1)));
  Node a = utils::mkNode(kind::BITVECTOR_PLUS, node[0], pow_two);
  Node b = utils::mkNode(kind::BITVECTOR_PLUS, node[1], pow_two);
  
  return utils::mkNode(kind::BITVECTOR_ULT, a, b); 
  
}

template <>
bool RewriteRule<SleEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLE); 
}

template <>
Node RewriteRule<SleEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<SleEliminate>(" << node << ")" << std::endl;
  
  unsigned size = utils::getSize(node[0]);
  Node pow_two = utils::mkConst(BitVector(size, Integer(1).multiplyByPow2(size - 1)));
  Node a = utils::mkNode(kind::BITVECTOR_PLUS, node[0], pow_two);
  Node b = utils::mkNode(kind::BITVECTOR_PLUS, node[1], pow_two);
  
  return utils::mkNode(kind::BITVECTOR_ULE, a, b); 
  
}

template <>
bool RewriteRule<CompEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_COMP); 
}

template <>
Node RewriteRule<CompEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<CompEliminate>(" << node << ")" << std::endl;
  Node comp = utils::mkNode(kind::EQUAL, node[0], node[1]);
  Node one = utils::mkConst(1, 1);
  Node zero = utils::mkConst(1, 0); 

  return utils::mkNode(kind::ITE, comp, one, zero);
}

template <>
bool RewriteRule<SubEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SUB); 
}

template <>
Node RewriteRule<SubEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<SubEliminate>(" << node << ")" << std::endl;
  Node negb = utils::mkNode(kind::BITVECTOR_NEG, node[1]);
  Node a = node[0];

  return utils::mkNode(kind::BITVECTOR_PLUS, a, negb);
}


template<>
bool RewriteRule<RepeatEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_REPEAT);
}

template<>
Node RewriteRule<RepeatEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<RepeatEliminate>(" << node << ")" << std::endl;
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
bool RewriteRule<RotateLeftEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ROTATE_LEFT);
}

template<>
Node RewriteRule<RotateLeftEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<RotateLeftEliminate>(" << node << ")" << std::endl;
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
bool RewriteRule<RotateRightEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ROTATE_RIGHT);
}

template<>
Node RewriteRule<RotateRightEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<RotateRightEliminate>(" << node << ")" << std::endl;
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
bool RewriteRule<NandEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NAND &&
          node.getNumChildren() == 2);
}

template<>
Node RewriteRule<NandEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<NandEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1]; 
  Node andNode = utils::mkNode(kind::BITVECTOR_AND, a, b);
  Node result = utils::mkNode(kind::BITVECTOR_NOT, andNode); 
  return result;
}

template<>
bool RewriteRule<NorEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NOR &&
          node.getNumChildren() == 2);
}

template<>
Node RewriteRule<NorEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<NorEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1]; 
  Node orNode = utils::mkNode(kind::BITVECTOR_OR, a, b);
  Node result = utils::mkNode(kind::BITVECTOR_NOT, orNode); 
  return result;
}

template<>
bool RewriteRule<XnorEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_XNOR &&
          node.getNumChildren() == 2);
}

template<>
Node RewriteRule<XnorEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<XnorEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1]; 
  Node xorNode = utils::mkNode(kind::BITVECTOR_XOR, a, b);
  return utils::mkNode(kind::BITVECTOR_NOT, xorNode); 
}


template<>
bool RewriteRule<SdivEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SDIV);
}

template<>
Node RewriteRule<SdivEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<SdivEliminate>(" << node << ")" << std::endl;

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
bool RewriteRule<SremEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SREM);
}

template<>
Node RewriteRule<SremEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<SremEliminate>(" << node << ")" << std::endl;
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
bool RewriteRule<SmodEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SMOD);
}

template<>
Node RewriteRule<SmodEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<SmodEliminate>(" << node << ")" << std::endl;
  TNode s = node[0];
  TNode t = node[1];
  unsigned size = utils::getSize(s);
  
  // (bvsmod s t) abbreviates
  //     (let ((?msb_s ((_ extract |m-1| |m-1|) s))
  //           (?msb_t ((_ extract |m-1| |m-1|) t)))
  //       (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
  //             (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
  //         (let ((u (bvurem abs_s abs_t)))
  //           (ite (= u (_ bv0 m))
  //                u
  //           (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
  //                u
  //           (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
  //                (bvadd (bvneg u) t)
  //           (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
  //                (bvadd u t)
  //                (bvneg u))))))))

  Node msb_s = utils::mkExtract(s, size-1, size-1);
  Node msb_t = utils::mkExtract(t, size-1, size-1);

  Node bit1    = utils::mkConst(1, 1);
  Node bit0    = utils::mkConst(1, 0);

  Node abs_s = msb_s.eqNode(bit0).iteNode(s, utils::mkNode(kind::BITVECTOR_NEG, s));
  Node abs_t = msb_t.eqNode(bit0).iteNode(t, utils::mkNode(kind::BITVECTOR_NEG, t));

  Node u = utils::mkNode(kind::BITVECTOR_UREM, abs_s, abs_t);
  Node neg_u = utils::mkNode(kind::BITVECTOR_NEG, u);

  Node cond0 = u.eqNode(utils::mkConst(size, 0));
  Node cond1 = msb_s.eqNode(bit0).andNode(msb_t.eqNode(bit0));
  Node cond2 = msb_s.eqNode(bit1).andNode(msb_t.eqNode(bit0));
  Node cond3 = msb_s.eqNode(bit0).andNode(msb_t.eqNode(bit1));

  Node result = cond0.iteNode(u,
                cond1.iteNode(u,
                cond2.iteNode(utils::mkNode(kind::BITVECTOR_PLUS, neg_u, t),
                cond3.iteNode(utils::mkNode(kind::BITVECTOR_PLUS, u, t), neg_u))));

  return result;

}


template<>
bool RewriteRule<ZeroExtendEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ZERO_EXTEND); 
}

template<>
Node RewriteRule<ZeroExtendEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<ZeroExtendEliminate>(" << node << ")" << std::endl;

  TNode bv = node[0];
  unsigned amount = node.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount;
  if (amount == 0) {
    return node[0]; 
  }
  Node zero = utils::mkConst(amount, 0);
  Node result = utils::mkConcat(zero, node[0]); 

  return result;
}

template<>
bool RewriteRule<SignExtendEliminate>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SIGN_EXTEND); 
}

template<>
Node RewriteRule<SignExtendEliminate>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<SignExtendEliminate>(" << node << ")" << std::endl;

  unsigned amount = node.getOperator().getConst<BitVectorSignExtend>().signExtendAmount;
  if(amount == 0) {
    return node[0]; 
  }
  unsigned size = utils::getSize(node[0]); 
  Node sign_bit = utils::mkExtract(node[0], size-1, size-1); 
  Node extension = utils::mkConcat(sign_bit, amount);

  return utils::mkConcat(extension, node[0]);
}


}
}
}

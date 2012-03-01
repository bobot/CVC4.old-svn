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
bool RewriteRule<EvalAnd>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_AND &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalAnd>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalAnd>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a & b;
  
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalOr>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_OR &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalOr>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalOr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a | b;
  
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalXor>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_XOR &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalXor>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalXor>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a ^ b;
 
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalXnor>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_XNOR &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalXnor>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalXnor>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = ~ (a ^ b);
  
  return utils::mkConst(res);
}
template<>
bool RewriteRule<EvalNot>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NOT &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalNot>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalNot>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector res = ~ a;  
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalComp>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_COMP &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalComp>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalComp>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res;
  if (a == b) {
    res = BitVector(1, Integer(1));
  } else {
    res = BitVector(1, Integer(0)); 
  }
  
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalMult>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_MULT &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalMult>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalMult>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a * b;
  
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalPlus>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_PLUS &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalPlus>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalPlus>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a + b;
  
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalSub>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SUB &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalSub>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalSub>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a - b;
  
  return utils::mkConst(res);
}
template<>
bool RewriteRule<EvalNeg>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalNeg>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalNeg>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector res = - a;
  
  return utils::mkConst(res);
}
template<>
bool RewriteRule<EvalUdiv>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UDIV &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalUdiv>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalUdiv>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a.unsignedDiv(b);
  
  return utils::mkConst(res);
}
template<>
bool RewriteRule<EvalUrem>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UREM &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalUrem>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalUrem>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a.unsignedRem(b);
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalShl>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SHL &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalShl>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalShl>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.leftShift(b);
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalLshr>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_LSHR &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalLshr>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalLshr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  
  BitVector res = a.logicalRightShift(b);
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalAshr>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ASHR &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalAshr>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalAshr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.arithRightShift(b);
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalUlt>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalUlt>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalUlt>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.unsignedLessThan(b);
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalSlt>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SLT &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalSlt>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalSlt>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.signedLessThan(b);
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalUle>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalUle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalUle>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.unsignedLessThanEq(b);
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalSle>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SLE &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalSle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalSle>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.signedLessThanEq(b);
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalExtract>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalExtract>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalExtract>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  unsigned lo = utils::getExtractLow(node);
  unsigned hi = utils::getExtractHigh(node);

  BitVector res = a.extract(lo, hi);
  return utils::mkConst(res);
}


template<>
bool RewriteRule<EvalConcat>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalConcat>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalConcat>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a.concat(b);
  
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalSignExtend>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SIGN_EXTEND &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalSignExtend>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalSignExtend>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  unsigned amount = node.getOperator().getConst<BitVectorSignExtend>().signExtendAmount; 
  BitVector res = a.signExtend(amount);
  
  return utils::mkConst(res);
}

template<>
bool RewriteRule<EvalEquals>::applies(Node node) {
  return (node.getKind() == kind::EQUAL &&
          utils::isBVGroundTerm(node));
}

template<>
Node RewriteRule<EvalEquals>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalEquals>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  if (a == b) {
    return utils::mkTrue(); 
  }
  return utils::mkFalse();

}


}
}
}

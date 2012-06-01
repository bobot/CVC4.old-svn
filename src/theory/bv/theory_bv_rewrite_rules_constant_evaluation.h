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

template<> inline
bool RewriteRule<EvalAnd>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_AND &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalAnd>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalAnd>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a & b;
  
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalOr>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_OR &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalOr>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalOr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a | b;
  
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalXor>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_XOR &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalXor>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalXor>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a ^ b;
 
  return utils::mkConst(res);
}

// template<> inline
// bool RewriteRule<EvalXnor>::applies(TNode node) {
//   return (node.getKind() == kind::BITVECTOR_XNOR &&
//           utils::isBVGroundTerm(node));
// }

// template<> inline
// Node RewriteRule<EvalXnor>::apply(TNode node) {
//   BVDebug("bv-rewrite") << "RewriteRule<EvalXnor>(" << node << ")" << std::endl;
//   BitVector a = node[0].getConst<BitVector>();
//   BitVector b = node[1].getConst<BitVector>();
//   BitVector res = ~ (a ^ b);
  
//   return utils::mkConst(res);
// }
template<> inline
bool RewriteRule<EvalNot>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NOT &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalNot>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalNot>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector res = ~ a;  
  return utils::mkConst(res);
}

// template<> inline
// bool RewriteRule<EvalComp>::applies(TNode node) {
//   return (node.getKind() == kind::BITVECTOR_COMP &&
//           utils::isBVGroundTerm(node));
// }

// template<> inline
// Node RewriteRule<EvalComp>::apply(TNode node) {
//   BVDebug("bv-rewrite") << "RewriteRule<EvalComp>(" << node << ")" << std::endl;
//   BitVector a = node[0].getConst<BitVector>();
//   BitVector b = node[1].getConst<BitVector>();
//   BitVector res;
//   if (a == b) {
//     res = BitVector(1, Integer(1));
//   } else {
//     res = BitVector(1, Integer(0)); 
//   }
  
//   return utils::mkConst(res);
// }

template<> inline
bool RewriteRule<EvalMult>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_MULT &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalMult>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalMult>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a * b;
  
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalPlus>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_PLUS &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalPlus>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalPlus>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a + b;
  
  return utils::mkConst(res);
}

// template<> inline
// bool RewriteRule<EvalSub>::applies(TNode node) {
//   return (node.getKind() == kind::BITVECTOR_SUB &&
//           utils::isBVGroundTerm(node));
// }

// template<> inline
// Node RewriteRule<EvalSub>::apply(TNode node) {
//   BVDebug("bv-rewrite") << "RewriteRule<EvalSub>(" << node << ")" << std::endl;
//   BitVector a = node[0].getConst<BitVector>();
//   BitVector b = node[1].getConst<BitVector>();
//   BitVector res = a - b;
  
//   return utils::mkConst(res);
// }
template<> inline
bool RewriteRule<EvalNeg>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalNeg>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalNeg>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector res = - a;
  
  return utils::mkConst(res);
}
template<> inline
bool RewriteRule<EvalUdiv>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UDIV &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalUdiv>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalUdiv>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a.unsignedDiv(b);
  
  return utils::mkConst(res);
}
template<> inline
bool RewriteRule<EvalUrem>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UREM &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalUrem>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalUrem>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a.unsignedRem(b);
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalShl>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SHL &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalShl>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalShl>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.leftShift(b);
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalLshr>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_LSHR &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalLshr>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalLshr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  
  BitVector res = a.logicalRightShift(b);
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalAshr>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ASHR &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalAshr>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalAshr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.arithRightShift(b);
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalUlt>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalUlt>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalUlt>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.unsignedLessThan(b)) {
    return utils::mkTrue();
  }
  return utils::mkFalse();
}

template<> inline
bool RewriteRule<EvalSlt>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLT &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalSlt>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalSlt>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.signedLessThan(b)) {
    return utils::mkTrue();
  }
  return utils::mkFalse();

}

template<> inline
bool RewriteRule<EvalUle>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalUle>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalUle>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.unsignedLessThanEq(b)) {
    return utils::mkTrue();
  }
  return utils::mkFalse();
}

template<> inline
bool RewriteRule<EvalSle>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLE &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalSle>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalSle>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.signedLessThanEq(b)) {
    return utils::mkTrue(); 
  }
  return utils::mkFalse();
}

template<> inline
bool RewriteRule<EvalExtract>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalExtract>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalExtract>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  unsigned lo = utils::getExtractLow(node);
  unsigned hi = utils::getExtractHigh(node);

  BitVector res = a.extract(hi, lo);
  return utils::mkConst(res);
}


template<> inline
bool RewriteRule<EvalConcat>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalConcat>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalConcat>(" << node << ")" << std::endl;
  unsigned num = node.getNumChildren();
  BitVector res = node[0].getConst<BitVector>();
  for(unsigned i = 1; i < num; ++i ) {  
    BitVector a = node[i].getConst<BitVector>();
    res = res.concat(a); 
  }
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalSignExtend>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SIGN_EXTEND &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalSignExtend>::apply(TNode node) {
  BVDebug("bv-rewrite") << "RewriteRule<EvalSignExtend>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  unsigned amount = node.getOperator().getConst<BitVectorSignExtend>().signExtendAmount; 
  BitVector res = a.signExtend(amount);
  
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalEquals>::applies(TNode node) {
  return (node.getKind() == kind::EQUAL &&
          utils::isBVGroundTerm(node));
}

template<> inline
Node RewriteRule<EvalEquals>::apply(TNode node) {
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

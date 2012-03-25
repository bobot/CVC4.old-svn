/*********************                                                        */
/*! \file theory_bv_rewrite_rules_normalization.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
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

#include "cvc4_private.h"

#pragma once

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * ExtractBitwise
 *   (x bvop y) [i:j] ==> x[i:j] bvop y[i:j]
 *  where bvop is bvand,bvor, bvxor
 */
template<>
bool RewriteRule<ExtractBitwise>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          (node[0].getKind() == kind::BITVECTOR_AND ||
           node[0].getKind() == kind::BITVECTOR_OR ||
           node[0].getKind() == kind::BITVECTOR_XOR ));
}

template<>
Node RewriteRule<ExtractBitwise>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ExtractBitwise>(" << node << ")" << std::endl;
  unsigned high = utils::getExtractHigh(node);
  unsigned low = utils::getExtractLow(node);
  Node a = utils::mkExtract(node[0][0], high, low);
  Node b = utils::mkExtract(node[0][1], high, low);
  Kind kind = node[0].getKind(); 
  return utils::mkNode(kind, a, b);
}

/**
 * ExtractNot
 *
 *  (~ a) [i:j] ==> ~ (a[i:j])
 */
template<>
bool RewriteRule<ExtractNot>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          node[0].getKind() == kind::BITVECTOR_NOT);
}

template<>
Node RewriteRule<ExtractNot>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ExtractNot>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  unsigned high = utils::getExtractHigh(node);
  Node a = utils::mkExtract(node[0][0], high, low);
  return utils::mkNode(kind::BITVECTOR_NOT, a); 
}

/**
 * ExtractArith
 * 
 * (a bvop b) [k:0] ==> (a[k:0] bvop b[k:0])
 */

template<>
bool RewriteRule<ExtractArith>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          utils::getExtractLow(node) == 0 &&
          (node[0].getKind() == kind::BITVECTOR_PLUS ||
           node[0].getKind() == kind::BITVECTOR_MULT));
}

template<>
Node RewriteRule<ExtractArith>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ExtractArith>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  Assert (low == 0); 
  unsigned high = utils::getExtractHigh(node);
  Node a = utils::mkExtract(node[0][0], high, low);
  Node b = utils::mkExtract(node[0][1], high, low);
  
  Kind kind = node[0].getKind(); 
  return utils::mkNode(kind, a, b); 
  
}

/**
 * ExtractArith2
 *
 * (a bvop b) [i:j] ==> (a[i:0] bvop b[i:0]) [i:j]
 */

// careful not to apply in a loop 
template<>
bool RewriteRule<ExtractArith2>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          (node[0].getKind() == kind::BITVECTOR_PLUS ||
           node[0].getKind() == kind::BITVECTOR_MULT));
}

template<>
Node RewriteRule<ExtractArith2>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ExtractArith2>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  unsigned high = utils::getExtractHigh(node);
  Node a = utils::mkExtract(node[0][0], high, 0);
  Node b = utils::mkExtract(node[0][1], high, 0);
  
  Kind kind = node[0].getKind(); 
  Node a_op_b = utils::mkNode(kind, a, b); 
  
  return utils::mkExtract(a_op_b, high, low); 
}

template<>
bool RewriteRule<FlattenAssocCommut>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_PLUS ||
          node.getKind() == kind::BITVECTOR_MULT ||
          node.getKind() == kind::BITVECTOR_OR ||
          node.getKind() == kind::BITVECTOR_XOR ||
          node.getKind() == kind::BITVECTOR_AND);
}


template<>
Node RewriteRule<FlattenAssocCommut>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<FlattenAssocCommut>(" << node << ")" << std::endl;
  std::vector<Node> processingStack;
  processingStack.push_back(node);
  std::vector<Node> children;
  Kind kind = node.getKind(); 
  
  while (! processingStack.empty()) {
    TNode current = processingStack.back();
    processingStack.pop_back();

    // flatten expression
    if (current.getKind() == kind) {
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        processingStack.push_back(current[i]);
      }
    } else {
      children.push_back(current); 
    }
  }
  std::sort(children.begin(), children.end()); 
  return utils::mkNode(kind, children); 
}

static inline void addToCoefMap(std::map<Node, BitVector>& map,
                                TNode term, const BitVector& coef) {
  if (map.find(term) != map.end()) {
    map[term] = map[term] + coef; 
  } else {
    map[term] = coef;
  }
}


template<>
bool RewriteRule<PlusCombineLikeTerms>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_PLUS);
}

template<>
Node RewriteRule<PlusCombineLikeTerms>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<PlusCombineLikeTerms>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node); 
  BitVector constSum(size, (unsigned)0); 
  std::map<Node, BitVector> factorToCoefficient;

  // combine like-terms
  for(unsigned i= 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    
    // look for c * x, where c is a constant
    if (current.getKind() == kind::BITVECTOR_MULT &&
        (current[0].getKind() == kind::CONST_BITVECTOR ||
         current[1].getKind() == kind::CONST_BITVECTOR)) {
      // if we are multiplying by a constant
      BitVector coeff;
      TNode term;
      // figure out which part is the constant
      if (current[0].getKind() == kind::CONST_BITVECTOR) {
        coeff = current[0].getConst<BitVector>();
        term = current[1];
      } else {
        coeff = current[1].getConst<BitVector>();
        term = current[0];
      }
      if(term.getKind() == kind::BITVECTOR_SUB) {
        TNode a = term[0];
        TNode b = term[1];
        addToCoefMap(factorToCoefficient, a, coeff);
        addToCoefMap(factorToCoefficient, b, -coeff); 
      }
      else if(term.getKind() == kind::BITVECTOR_NEG) {
        addToCoefMap(factorToCoefficient, term[0], -BitVector(size, coeff));
      }
      else {
        addToCoefMap(factorToCoefficient, term, coeff);
      }
    }
    else if (current.getKind() == kind::BITVECTOR_SUB) {
      // turn into a + (-1)*b 
      addToCoefMap(factorToCoefficient, current[0], BitVector(size, (unsigned)1)); 
      addToCoefMap(factorToCoefficient, current[1], -BitVector(size, (unsigned)1)); 
    }
    else if (current.getKind() == kind::BITVECTOR_NEG) {
      addToCoefMap(factorToCoefficient, current[0], -BitVector(size, (unsigned)1)); 
    }
    else if (current.getKind() == kind::CONST_BITVECTOR) {
      BitVector constValue = current.getConst<BitVector>(); 
      constSum = constSum + constValue;
    }
    else {
      // store as 1 * current
      addToCoefMap(factorToCoefficient, current, BitVector(size, (unsigned)1)); 
    }
  }
    
  NodeBuilder<> sum(kind::BITVECTOR_PLUS);
  
  if ( constSum!= BitVector(size, (unsigned)0)) {
    sum << utils::mkConst(constSum); 
  }

  // construct result 
  std::map<Node, BitVector>::const_iterator it = factorToCoefficient.begin();
  
  for (; it != factorToCoefficient.end(); ++it) {
    BitVector bv_coeff = it->second;
    TNode term = it->first;
    if(bv_coeff == BitVector(size, (unsigned)0)) {
      continue;
    }
    else if (bv_coeff == BitVector(size, (unsigned)1)) {
      sum << term; 
    }
    else if (bv_coeff == -BitVector(size, (unsigned)1)) {
      // avoid introducing an extra multiplication
      sum << utils::mkNode(kind::BITVECTOR_NEG, term); 
    }
    else {
      Node coeff = utils::mkConst(bv_coeff);
      Node product = utils::mkNode(kind::BITVECTOR_MULT, coeff, term); 
      sum << product; 
    }
  }

  if(sum.getNumChildren() == 0) {
    return utils::mkConst(size, (unsigned)0); 
  }
  
  if(sum.getNumChildren() == 1) {
    return sum[0];
  }
  
  return sum;
}


template<>
bool RewriteRule<MultSimplify>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_MULT);
}

template<>
Node RewriteRule<MultSimplify>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<MultSimplify>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node); 
  BitVector constant(size, Integer(1));

  std::vector<Node> children; 
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    if (current.getKind() == kind::CONST_BITVECTOR) {
      BitVector value = current.getConst<BitVector>();
      if(value == BitVector(size, (unsigned) 0)) {
        return utils::mkConst(size, 0); 
      }
      constant = constant * current.getConst<BitVector>();
    } else {
      children.push_back(current); 
    }
  }

  std::sort(children.begin(), children.end()); 
  if(constant != BitVector(size, (unsigned)1)) {
    children.push_back(utils::mkConst(constant)); 
  }

  if(children.size() == 0) {
    return utils::mkConst(size, (unsigned)1); 
  }

  if(children.size() == 1) {
    return children[0];
  }
  
  return utils::mkNode(kind::BITVECTOR_MULT, children); 
}

template<>
bool RewriteRule<MultDistribConst>::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_MULT)
    return false;

  TNode factor;
  if (node[0].getKind() == kind::CONST_BITVECTOR) {
    factor = node[1];
  } else if (node[1].getKind() == kind::CONST_BITVECTOR) {
    factor = node[0];
  } else {
    return false; 
  }
  
  return (factor.getKind() == kind::BITVECTOR_PLUS ||
          factor.getKind() == kind::BITVECTOR_SUB ||
          factor.getKind() == kind::BITVECTOR_NEG); 
}

template<>
Node RewriteRule<MultDistribConst>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<MultDistribConst>(" << node << ")" << std::endl;

  TNode constant;
  TNode factor;
  if (node[0].getKind() == kind::CONST_BITVECTOR) {
    constant = node[0];
    factor = node[1]; 
  } else {
  Assert(node[1].getKind() == kind::CONST_BITVECTOR);
  constant = node[1];
  factor = node[0];
  }

  if (factor.getKind() == kind::BITVECTOR_NEG) {
    // push negation on the constant part
    BitVector const_bv = constant.getConst<BitVector>();
    return utils::mkNode(kind::BITVECTOR_MULT,
                         utils::mkConst(-const_bv),
                         factor[0]); 
  }
  
  return utils::mkNode(factor.getKind(),
                       utils::mkNode(kind::BITVECTOR_MULT, constant, factor[0]),
                       utils::mkNode(kind::BITVECTOR_MULT, constant, factor[1])); 
}


/**
 * -(c * expr) ==> (-c * expr)
 * where c is a constant
 */
template<>
bool RewriteRule<NegMult>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_MULT);
}

template<>
Node RewriteRule<NegMult>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NegMult>(" << node << ")" << std::endl;
  TNode mult = node[0];
  std::vector<Node> children;
  bool has_const = false; 
  for(unsigned i = 0; i < mult.getNumChildren(); ++i) {
    if(mult[i].getKind() == kind::CONST_BITVECTOR) {
      Assert(has_const == false);
      has_const = true; 
      BitVector bv = mult[i].getConst<BitVector>();
      children.push_back(utils::mkConst(-bv)); 
    } else {
      children.push_back(mult[i]); 
    }
  }
  return utils::mkNode(kind::BITVECTOR_MULT, children);
}

template<>
bool RewriteRule<NegSub>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_SUB);
}

template<>
Node RewriteRule<NegSub>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NegSub>(" << node << ")" << std::endl;
  return utils::mkNode(kind::BITVECTOR_SUB, node[0][1], node[0][0]);
}

// template<>
// bool RewriteRule<AndSimplify>::applies(Node node) {
//   return (node.getKind() == kind::BITVECTOR_AND);
// }

// template<>
// Node RewriteRule<AndSimplify>::apply(Node node) {
//   BVDebug("bv-rewrite") << "RewriteRule<AndSimplify>(" << node << ")" << std::endl;
//   return resultNode;
// }


// template<>
// bool RewriteRule<>::applies(Node node) {
//   return (node.getKind() == kind::BITVECTOR_CONCAT);
// }

// template<>
// Node RewriteRule<>::apply(Node node) {
//   BVDebug("bv-rewrite") << "RewriteRule<>(" << node << ")" << std::endl;
//   return resultNode;
// }



}
}
}

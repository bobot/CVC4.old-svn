/*********************                                                        */
/*! \file bitblast_strategies.cpp
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
 ** \brief Implementation of bitblasting functions for various operators. 
 **
 ** Implementation of bitblasting functions for various operators. 
 **/

#include "bitblast_strategies.h"
#include "bv_sat.h"
#include "prop/sat_module.h"

using namespace CVC4::prop; 
using namespace CVC4::theory::bv::utils;
namespace CVC4 {
namespace theory {
namespace bv {


void inline negateBits(const Bits& bits, Bits& negated_bits) {
  for(int i = 0; i < bits.size(); ++i) {
    negated_bits.push_back(utils::mkNot(bits[i])); 
  }
}

Node UndefinedAtomBBStrategy(TNode node, Bitblaster* bb) {
  Debug("bitvector") << "TheoryBV::Bitblaster Undefined bitblasting strategy for kind: "
                     << node.getKind() << "\n";
  Unreachable(); 
}

Node DefaultEqBB(TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  

  Assert(node.getKind() == kind::EQUAL);
  Bits lhs, rhs; 
  bb->bbTerm(node[0], lhs);
  bb->bbTerm(node[1], rhs);

  Assert(lhs.size() == rhs.size());

  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> bits_eq;
  for (unsigned i = 0; i < lhs.size(); i++) {
    Node bit_eq = nm->mkNode(kind::IFF, lhs[i], rhs[i]);
    bits_eq.push_back(bit_eq); 
  }
  Node bv_eq = utils::mkAnd(bits_eq);
  Node definition = nm->mkNode(kind::IFF, node, bv_eq); 
  
  return definition; 
}

Node DefaultUltBB(TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert(node.getKind() == kind::BITVECTOR_ULT);
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());
  
  // a < b <=> ~ (add(a, ~b, 1).carry_out)
  Bits not_b;
  negateBits(b, not_b);
  Node carry = mkTrue();
  
  for (unsigned i = 0 ; i < a.size(); ++i) {
    carry = mkOr( mkAnd(a[i], not_b[i]),
                  mkAnd( mkXor(a[i], not_b[i]),
                         carry));
  }
  Node definition = NodeManager::currentNM()->mkNode(kind::IFF, node, mkNot(carry)); 
  return definition;
}

Node DefaultUleBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}
Node DefaultUgtBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}
Node DefaultUgeBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}

Node DefaultSltBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);
  Assert(a.size() == b.size());
  
  // a < b <=> (a[0] <=> b[0]) xor (add(a, ~b, 1).carry_out)
  Bits not_b;
  negateBits(b, not_b);
  Node carry = mkTrue();
  
  for (unsigned i = 0 ; i < a.size(); ++i) {
    carry = mkOr( mkAnd(a[i], not_b[i]),
                  mkAnd( mkXor(a[i], not_b[i]),
                         carry));
  }
  NodeManager* nm = NodeManager::currentNM(); 
  Node definition = nm->mkNode(kind::IFF,
                               node,
                               mkXor( nm->mkNode(kind::IFF, a.back(), b.back()),
                                      carry)); 
  return definition;
}

Node DefaultSleBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}
 
Node DefaultSgtBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}

Node DefaultSgeBB(TNode node, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}


/// Term bitblasting strategies 

void UndefinedTermBBStrategy(TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Undefined bitblasting strategy for kind: "
                     << node.getKind() << "\n";
  Unreachable(); 
}

void DefaultVarBB (TNode node, Bits& bits, Bitblaster* bb) {
  Assert (node.getKind() == kind::VARIABLE);
  Assert(bits.size() == 0);
  
  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    bits.push_back(utils::mkBitOf(node, i));
  }

  Debug("bitvector-bb") << "theory::bv::DefaultVarBB bitblasting  " << node << "\n";
  Debug("bitvector-bb") << "                           with bits  " << toString(bits); 
}

void DefaultConstBB       (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultConstBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::CONST_BITVECTOR);
  Assert(bits.size() == 0);
  
  NodeManager* nm = NodeManager::currentNM(); 
  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    Integer bit = node.getConst<BitVector>().extract(i, i).getValue();
    if(bit == Integer(0)){
      bits.push_back(utils::mkFalse());
    } else {
      Assert (bit == Integer(1));
      bits.push_back(utils::mkTrue()); 
    }
  }
  Debug("bitvector-bb") << "with  bits: " << toString(bits) << "\n"; 
}


void DefaultNotBB         (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultNotBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_NOT);
  Assert(bits.size() == 0);
  Bits bv; 
  bb->bbTerm(node[0], bv);
  negateBits(bv, bits);
}

void DefaultConcatBB      (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultConcatBB bitblasting " << node << "\n";
  Assert(bits.size() == 0);
  
  Assert (node.getKind() == kind::BITVECTOR_CONCAT);
  for (int i = node.getNumChildren() -1 ; i >= 0; --i ) {
    TNode current = node[i];
    Bits current_bits; 
    bb->bbTerm(current, current_bits);

    for(unsigned j = 0; j < utils::getSize(current); ++j) {
      bits.push_back(current_bits[j]);
    }
  }
  Assert (bits.size() == utils::getSize(node)); 
  Debug("bitvector-bb") << "with  bits: " << toString(bits) << "\n"; 
}


void DefaultAndBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultAndBB bitblasting " << node << "\n";

  Assert(node.getNumChildren() == 2 &&
         node.getKind() == kind::BITVECTOR_AND &&
         bits.size() == 0);
  
  Bits lhs, rhs;
  bb->bbTerm(node[0], rhs);
  bb->bbTerm(node[1], lhs);

  Assert (lhs.size() == rhs.size()); 
  for (unsigned i = 0; i < lhs.size(); ++i) {
    bits.push_back(utils::mkAnd(lhs[i], rhs[i])); 
  }

}

void DefaultOrBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultOrBB bitblasting " << node << "\n";

  Assert(node.getNumChildren() == 2 &&
         node.getKind() == kind::BITVECTOR_OR &&
         bits.size() == 0);
  
  Bits lhs, rhs;
  bb->bbTerm(node[0], lhs);
  bb->bbTerm(node[1], rhs);
  Assert(lhs.size() == rhs.size()); 
  
  for (unsigned i = 0; i < lhs.size(); ++i) {
    bits.push_back(utils::mkOr(lhs[i], rhs[i])); 
  }
}

void DefaultXorBB         (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultXorBB bitblasting " << node << "\n";

  Assert(node.getNumChildren() == 2 &&
         node.getKind() == kind::BITVECTOR_XOR &&
         bits.size() == 0);
  
  Bits lhs, rhs;
  bb->bbTerm(node[0], lhs);
  bb->bbTerm(node[1], rhs);
  Assert(lhs.size() == rhs.size()); 
  
  for (unsigned i = 0; i < lhs.size(); ++i) {
    bits.push_back(utils::mkXor(lhs[i], rhs[i])); 
  }
}

void DefaultNandBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultNorBB         (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultCompBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: DefaultCompBB bitblasting "<< node << "\n";

  Assert(getSize(node) == 1 && bits.size() == 0 && node.getKind() == kind::BITVECTOR_COMP);
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b);

  std::vector<Node> bit_eqs;
  NodeManager* nm = NodeManager::currentNM(); 
  for (unsigned i = 0; i < a.size(); ++i) {
    Node eq = nm->mkNode(kind::IFF, a[i], b[i]);
    bit_eqs.push_back(eq); 
  }
  Node a_eq_b = mkAnd(bit_eqs);
  bits.push_back(a_eq_b);   
}
void DefaultMultBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

void DefaultPlusBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaulPlusBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_PLUS &&
         bits.size() == 0);

  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b); 

  Assert(a.size() == b.size() && utils::getSize(node) == a.size());
  
  Node carry = utils::mkFalse();
  for (unsigned i = 0 ; i < getSize(node); ++i) {
    Node sum = mkXor(mkXor(a[i], b[i]), carry);
    carry = mkOr( mkAnd(a[i], b[i]),
                  mkAnd( mkXor(a[i], b[i]),
                         carry));
    bits.push_back(sum); 
  } 
}

void DefaultSubBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefautSubBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_SUB &&  bits.size() == 0);
    
  Bits a, b;
  bb->bbTerm(node[0], a);
  bb->bbTerm(node[1], b); 
  Assert(a.size() == b.size() && utils::getSize(node) == a.size());

  // bvsub a b = adder(a, ~b, 1)
  Bits not_b;
  negateBits(b, not_b);
  Node carry = utils::mkTrue();

  for (unsigned i = 0 ; i < getSize(node); ++i) {
    Node sum = mkXor(mkXor(a[i], not_b[i]), carry);
    carry = mkOr( mkAnd(a[i], not_b[i]),
                  mkAnd( mkXor(a[i], not_b[i]),
                         carry));
    bits.push_back(sum); 
  } 

}

void DefaultNegBB         (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefautNegBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_NEG);
  
  Bits a;
  bb->bbTerm(node[0], a);
  Assert(utils::getSize(node) == a.size());

  // -a = add(~a, 1, 0).
  Bits not_a;
  negateBits(a, not_a);
  Node carry = utils::mkFalse();

  for (unsigned i = 0 ; i < getSize(node); ++i) {
    Node one = i == 0? mkTrue() : mkFalse();
    Node sum = mkXor(mkXor(not_a[i], one), carry);
    carry = mkOr( mkAnd(not_a[i], one),
                  mkAnd( mkXor(not_a[i], one),
                         carry));
    bits.push_back(sum); 
  } 
}

void DefaultUdivBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultUremBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultSdivBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultSremBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultSmodBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultShlBB         (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultLshrBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
void DefaultAshrBB        (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

void DefaultExtractBB     (TNode node, Bits& bits, Bitblaster* bb) {
  Assert (node.getKind() == kind::BITVECTOR_EXTRACT);
  Assert(bits.size() == 0);
  
  Bits base_bits;
  bb->bbTerm(node[0], base_bits);
  unsigned high = utils::getExtractHigh(node);
  unsigned low  = utils::getExtractLow(node);

  for (unsigned i = low; i <= high; ++i) {
    bits.push_back(base_bits[i]); 
  }
  Assert (bits.size() == high - low + 1);   

  Debug("bitvector-bb") << "theory::bv::DefaultExtractBB bitblasting " << node << "\n";
  Debug("bitvector-bb") << "                               with bits " << toString(bits); 
       
}


void DefaultRepeatBB      (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

void DefaultZeroExtendBB  (TNode node, Bits& res_bits, Bitblaster* bb) {

  Debug("bitvector-bb") << "theory::bv::DefaultZeroExtendBB bitblasting " << node  << "\n";
  Assert (node.getKind() == kind::BITVECTOR_ZERO_EXTEND &&
          res_bits.size() == 0);
  Bits bits;
  bb->bbTerm(node[0], bits);
  
  unsigned amount = node.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount; 

  for (unsigned i = 0; i < bits.size(); ++i ) {
    res_bits.push_back(bits[i]); 
  }
  
  for (unsigned i = 0 ; i < amount ; ++i ) {
    res_bits.push_back(utils::mkFalse()); 
  }
  
  Assert (res_bits.size() == amount + bits.size()); 
}

void DefaultSignExtendBB  (TNode node, Bits& res_bits, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultSignExtendBB bitblasting " << node  << "\n";

  Assert (node.getKind() == kind::BITVECTOR_SIGN_EXTEND &&
          res_bits.size() == 0);

  Bits bits;
  bb->bbTerm(node[0], bits);
  
  TNode sign_bit = bits.back(); 
  unsigned amount = node.getOperator().getConst<BitVectorSignExtend>().signExtendAmount; 

  for (unsigned i = 0; i < bits.size(); ++i ) {
    res_bits.push_back(bits[i]); 
  }
         
  for (unsigned i = 0 ; i < amount ; ++i ) {
    res_bits.push_back(sign_bit); 
  }
         
  Assert (res_bits.size() == amount + bits.size()); 
}

void DefaultRotateRightBB (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

void DefaultRotateLeftBB  (TNode node, Bits& bits, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}


}
}
}



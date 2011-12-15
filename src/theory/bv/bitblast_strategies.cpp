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

namespace CVC4 {
namespace theory {
namespace bv {


// helper functions
inline void bitXor(SatLit res, SatLit a, SatLit b, Bitblaster* bb) {
  bb->mkClause(neg(res), a, b);
  bb->mkClause(neg(res), neg(a), neg(b));
  bb->mkClause(res, neg(a), b);
  bb->mkClause(res, a, neg(b)); 
}

inline void bitAnd(SatLit res, SatLit a, SatLit b, Bitblaster* bb) {
  bb->mkClause(neg(res), a);
  bb->mkClause(neg(res), b);
  bb->mkClause(res, neg(a), neg(b)); 
}

inline void bitOr(SatLit res, SatLit a, SatLit b, Bitblaster* bb) {
  bb->mkClause(res, neg(a));
  bb->mkClause(res, neg(b));
  bb->mkClause(neg(res), a, b);
}

inline void bitImpl(SatLit res, SatLit a, SatLit b, Bitblaster* bb) {
  bb->mkClause(neg(res), neg(a), b);
  bb->mkClause(res, a);
  bb->mkClause(res, neg(b)); 
}

inline void bitIff(SatLit res, SatLit a, SatLit b, Bitblaster* bb) {
  bitImpl(res, a, b, bb);
  bitImpl(res, b, a, bb); 
}

inline void bitEqual(SatLit a, SatLit b, Bitblaster* bb) {
  bb->mkClause(neg(a), b);
  bb->mkClause(neg(b), a); 
}

inline SatLit mkBitXor(SatLit a, SatLit b, Bitblaster* bb) {
  SatLit res = mkLit(bb->newVar());
  bitXor(res, a, b, bb); 
  return res; 
}

inline SatLit mkBitAnd(SatLit a, SatLit b, Bitblaster* bb) {
  SatLit res = mkLit(bb->newVar());
  bitAnd(res, a, b, bb); 
  return res; 
}

inline SatLit mkBitOr(SatLit a, SatLit b, Bitblaster* bb) {
  SatLit res = mkLit(bb->newVar());
  bitOr(res, a, b, bb); 
  return res; 
}

inline SatLit mkBitImpl(SatLit a, SatLit b, Bitblaster* bb) {
  SatLit res = mkLit(bb->newVar());
  bitImpl(res, a, b, bb); 
  return res; 
}

inline SatLit mkBitIff(SatLit a, SatLit b, Bitblaster* bb) {
  SatLit res = mkLit(bb->newVar());
  bitIff(res, a, b, bb); 
  return res; 
}


inline Bits* mkConstBits(int size, int val, Bitblaster* bb) {
  Bits* res = new Bits(size);
  for(int i = size - 1; i >= 0; --i) {
    res->operator[](i) = val % 2 ? bb->d_trueLit : bb->d_falseLit;
    val = val / 2; 
  }
  return res; 
}


inline Bits* negateBits(const Bits* bits) {
  Assert(bits); 
  Bits* res = new Bits();
  for(int i = 0; i < bits->size(); ++i) {
    res->push_back(neg(bits->operator[](i))); 
  }
  return res; 
}


/// make adder

/** 
 * Adds the clauses corresponding to a ripple carry adder
 * for res = term1 + term2
 * 
 * @param term1  
 * @param term2 
 * @param carry_in whether there the carry_in bit is true 
 * @param res the result of the addition 
 * @param bb the bitblaster
 * 
 * @return returns a literal representing the carry_out 
 */
inline SatLit mkAdder(Bits* term1, Bits* term2, bool carry_in, Bits* res, Bitblaster* bb) 
{
  Assert (term1 && term2 && res); 
  Assert (term1->size() == term2->size() && term1->size() == res->size());

  Bits& a = *term1;
  Bits& b = *term2;
  Bits& sum = *res;

  Bits* new_carry = bb->freshBits(res->size());
  Bits& carry = *new_carry;

  SatLit carry_bit = carry_in? bb->d_trueLit : bb->d_falseLit;
    
  for (int i = sum.size() - 1; i >= 0; --i) {
    // sum = (a xor b) xor carry_in
    SatLit aXORb = mkLit(bb->newVar());
    bitXor(aXORb, a[i], b[i], bb);
    SatLit carry_in = i == (sum.size() - 1)? carry_bit : carry[i+1]; 
    bitXor(sum[i], aXORb, carry_in , bb);
    
    // carry_out = (a and b) or ((a xor b) and carry)
    SatLit aANDb = mkLit(bb->newVar());
    bitAnd(aANDb, a[i], b[i], bb); 
    SatLit aXORb_AND_c = mkLit(bb->newVar());
    bitAnd(aXORb_AND_c, aXORb, carry_in, bb); 
    bitOr(carry[i], aANDb, aXORb_AND_c, bb);
    }

  SatLit carry_out = carry[0];
  delete new_carry;
  return carry_out; 
  
}

inline SatLit mkCarryOut(Bits* term1, Bits* term2, bool carry_in, Bitblaster* bb) 
{
  Assert (term1 && term2); 
  Assert (term1->size() == term2->size());

  Bits& a = *term1;
  Bits& b = *term2;
  //  Bits& sum = *res;

  Bits* new_carry = bb->freshBits(a.size());
  Bits& carry = *new_carry;

  SatLit carry_bit = carry_in? bb->d_trueLit : bb->d_falseLit;
    
  for (int i = a.size() - 1; i >= 0; --i) {
    // sum = (a xor b) xor carry_in
    SatLit aXORb = mkLit(bb->newVar());
    bitXor(aXORb, a[i], b[i], bb);
    SatLit carry_in = i == (a.size() - 1)? carry_bit : carry[i+1]; 
    // bitXor(sum[i], aXORb, carry_in , bb);
    
    // carry_out = (a and b) or ((a xor b) and carry)
    SatLit aANDb = mkLit(bb->newVar());
    bitAnd(aANDb, a[i], b[i], bb); 
    SatLit aXORb_AND_c = mkLit(bb->newVar());
    bitAnd(aXORb_AND_c, aXORb, carry_in, bb); 
    bitOr(carry[i], aANDb, aXORb_AND_c, bb);
    }

  SatLit carry_out = carry[0];
  delete new_carry;
  return carry_out; 
  
}




void UndefinedAtomBBStrategy(TNode node, SatVar atom_var, Bitblaster* bb) {
  Debug("bitvector") << "TheoryBV::Bitblaster Undefined bitblasting strategy for kind: "
                     << node.getKind() << "\n";
  Unreachable(); 
}

void DefaultEqBB(TNode node, SatVar atom_var, Bitblaster* bb) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Debug("bitvector-bb") << "      marker lit " << toStringLit(mkLit(atom_var)) << "\n"; 
  
  Assert(node.getKind() == kind::EQUAL);
  const Bits& lhs = *(bb->bbTerm(node[0]));
  const Bits& rhs = *(bb->bbTerm(node[1]));

  Assert(lhs.size() == rhs.size());

  SatLit atom_lit = mkLit(atom_var); 
  std::vector<SatLit> lits;
  /// constructing the clause x_1 /\ .. /\ x_n =
  lits.push_back(atom_lit);
  
  for (unsigned i = 0; i < lhs.size(); i++) {
    SatLit x = mkLit(bb->newVar());
    
    /// Adding the clauses corresponding to:
    ///       x_i = (lhs_i = rhs_i)
    bb->mkClause(neg(x), lhs[i], neg(rhs[i]));
    bb->mkClause(neg(x), neg(lhs[i]), rhs[i]);
    bb->mkClause(x, lhs[i], rhs[i]);
    bb->mkClause(x, neg(lhs[i]), neg(rhs[i]));

    /// adding the clauses for atom_lit => x_1 /\ ... /\ x_n
    bb->mkClause(neg(atom_lit), x); 
    lits.push_back(neg(x));
  }
  bb->mkClause(lits); 

}

void DefaultUltBB(TNode node, SatVar markerVar, Bitblaster* bb) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Debug("bitvector-bb") << "      marker lit " << toStringLit(mkLit(markerVar)) << "\n"; 

  Assert(node.getKind() == kind::BITVECTOR_ULT);
  Bits* a = bb->bbTerm(node[0]);
  Bits* b = bb->bbTerm(node[1]);
  Bits* notb = negateBits(b);
  SatLit carry_out = mkCarryOut(a, notb, true, bb);
  SatLit atom_lit = mkLit(markerVar);

  // a < b <=> ~ (add(a, ~b, 1).carry_out)
  bitEqual(atom_lit, neg(carry_out), bb); 
  
  delete notb; 
  
}
void DefaultUleBB(TNode node, SatVar markerVar, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unreachable(); 
}
void DefaultUgtBB(TNode node, SatVar markerVar, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}
void DefaultUgeBB(TNode node, SatVar markerVar, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}

void DefaultSltBB(TNode node, SatVar markerVar, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}

void DefaultSleBB(TNode node, SatVar markerVar, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}

void DefaultSgtBB(TNode node, SatVar markerVar, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}

void DefaultSgeBB(TNode node, SatVar markerVar, Bitblaster* bb){
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Unimplemented(); 
}


/// Term bitblasting strategies 

Bits* UndefinedTermBBStrategy(TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Undefined bitblasting strategy for kind: "
                     << node.getKind() << "\n";
  Unreachable(); 
}

Bits* DefaultVarBB (TNode node, Bitblaster* bb) {
  Assert (node.getKind() == kind::VARIABLE);
  Bits* bits;
  bits = bb->freshBits(utils::getSize(node));

  Debug("bitvector-bb") << "theory::bv::DefaultVarBB bitblasting  " << node << "\n";
  Debug("bitvector-bb") << "                           with bits  " << toString(bits); 

  return bits; 

}

Bits* DefaultConstBB       (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultConstBB bitblasting " << node << "\n";

  Assert(node.getKind() == kind::CONST_BITVECTOR);

  Bits* bits = new Bits();

  for (int i = utils::getSize(node) - 1; i >= 0; --i) {
    Integer bit = node.getConst<BitVector>().extract(i, i).getValue();
    if(bit == Integer(0)){
      bits->push_back(bb->d_falseLit);
    } else {
      Assert (bit == Integer(1));
      bits->push_back(bb->d_trueLit); 
    }
  }
  return bits; 
}


Bits* DefaultNotBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultNotBB bitblasting " << node << "\n";
  
  Assert(node.getKind() == kind::BITVECTOR_NOT);

  const Bits* bv = bb->bbTerm(node[0]);
  Bits* notbv = negateBits(bv);
  return notbv; 
}

Bits* DefaultConcatBB      (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultConcatBB bitblasting " << node << "\n";
  Bits* bits = new Bits();
  
  Assert (node.getKind() == kind::BITVECTOR_CONCAT);
  for (unsigned i = 0; i < node.getNumChildren(); ++i ) {
    TNode current = node[i];
    const Bits* bv = bb->bbTerm(current);
    Assert(bv);
    for(unsigned j = 0; j < utils::getSize(current); ++j) {
      bits->push_back(bv->operator[](j));
    }
  }
  Assert (bits->size() == utils::getSize(node)); 
  return bits; 
}


Bits* DefaultAndBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultAndBB bitblasting " << node << "\n";
  // TODO: n-ary and
  Assert(node.getNumChildren() == 2); 
  Assert(node.getKind() == kind::BITVECTOR_AND);
  Bits* res = bb->freshBits(utils::getSize(node));
  
  Bits* lhs = bb->bbTerm(node[0]);
  Bits* rhs = bb->bbTerm(node[1]);
  
  Assert(res && lhs && rhs && bb);
  const Bits& c = *res;
  const Bits& a = *lhs;
  const Bits& b = *rhs;

  for (unsigned i = 0; i < c.size(); ++i) {
    bitAnd(c[i], a[i], b[i],  bb); 
  }
  return res; 
}

Bits* DefaultOrBB          (TNode node, Bitblaster* bb) {
  // TODO: n-ary 
  Debug("bitvector-bb") << "theory::bv::DefaultOrBB bitblasting " << node << "\n";
  Assert(node.getNumChildren() == 2); 
  Assert(node.getKind() == kind::BITVECTOR_OR);
  Bits* res = bb->freshBits(utils::getSize(node));
  Bits* lhs = bb->bbTerm(node[0]);
  Bits* rhs = bb->bbTerm(node[1]); 

  Assert (res && lhs && rhs);
  
  for (unsigned i = 0; i < res->size(); ++i) {
    bitOr(res->operator[](i), lhs->operator[](i), rhs->operator[](i), bb); 
  }
  return res; 
}

Bits* DefaultXorBB         (TNode node, Bitblaster* bb) {
  // TODO n-ary 
  Debug("bitvector-bb") << "theory::bv::DefaultXorBB bitblasting " << node << "\n";
  Assert(node.getNumChildren() == 2); 
  Assert(node.getKind() == kind::BITVECTOR_XOR);
  Bits* res = bb->freshBits(utils::getSize(node));
  Bits* lhs = bb->bbTerm(node[0]);
  Bits* rhs = bb->bbTerm(node[1]); 
    
  Assert (res && lhs && rhs && bb);
  const Bits& c = *res;
  const Bits& a = *lhs;
  const Bits& b = *rhs; 
  for (unsigned i = 0; i < res->size(); ++i) {
    bitXor(c[i], a[i], b[i], bb); 
  }
  return res; 
}
Bits* DefaultNandBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultNorBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultCompBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultMultBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

Bits* DefaultPlusBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaulPlusBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_PLUS);

  // bvadd a b = adder(a, b, 0)
  Bits* new_sum   = bb->freshBits(utils::getSize(node));
  Bits* a = bb->bbTerm(node[0]);
  Bits* b = bb->bbTerm(node[1]); 
  mkAdder(a, b, false, new_sum, bb);
  return new_sum; 
}

Bits* DefaultSubBB (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefautSubBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_SUB);
  // bvsub a b = adder(a, ~b, 1)
  
  Bits* new_sub   = bb->freshBits(utils::getSize(node));
  Bits* a = bb->bbTerm(node[0]);
  Bits* b = bb->bbTerm(node[1]);
  Bits* notb = negateBits(b);
  mkAdder(a, notb, true, new_sub, bb);
  delete notb; 
  return new_sub; 
}

Bits* DefaultNegBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefautNegBB bitblasting " << node << "\n";
  Assert(node.getKind() == kind::BITVECTOR_NEG);
  // adding the following constraint:
  // -a = add(~a, 1, 0).

  const Bits& a = *(bb->bbTerm(node[0]));
  
  Bits* nota = negateBits(&a);
  Bits* one = mkConstBits(a.size(), 1, bb); 
  Bits* res = bb->freshBits(a.size());
  mkAdder(nota, one, false, res, bb);
  delete nota; 
  delete one;
  
  return res; 
}

Bits* DefaultUdivBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultUremBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultSdivBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultSremBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultSmodBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultShlBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultLshrBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultAshrBB        (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

Bits* DefaultExtractBB     (TNode node, Bitblaster* bb) {
  Assert (node.getKind() == kind::BITVECTOR_EXTRACT);
  const Bits* bits = bb->bbTerm(node[0]);
  unsigned high = utils::getExtractHigh(node);
  unsigned low  = utils::getExtractLow(node);

  Bits* extractbits = new Bits(); 
  for (unsigned i = bits->size() - 1 - high; i <= bits->size() -1 - low; ++i) {
    extractbits->push_back(bits->operator[](i)); 
  }
  Assert (extractbits->size() == high - low + 1);   

  Debug("bitvector-bb") << "theory::bv::DefaultExtractBB bitblasting " << node << "\n";
  Debug("bitvector-bb") << "                               with bits " << toString(extractbits); 
       
  return extractbits; 
}


Bits* DefaultRepeatBB      (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

Bits* DefaultZeroExtendBB  (TNode node, Bitblaster* bb) {

  Debug("bitvector-bb") << "theory::bv::DefaultZeroExtendBB bitblasting " << node  << "\n";
  
  Assert (node.getKind() == kind::BITVECTOR_ZERO_EXTEND);
  Bits* bits = bb->bbTerm(node[0]); 
  unsigned amount = node.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount; 
  Bits* res_bits = new Bits();

  for (unsigned i = 0 ; i < amount ; ++i ) {
    res_bits->push_back(bb->d_falseLit); 
  }
  for (unsigned i = 0; i < bits->size(); ++i ) {
    res_bits->push_back(bits->operator[](i)); 
  }
  Assert (res_bits->size() == amount + bits->size()); 
  return res_bits; 

}

Bits* DefaultSignExtendBB  (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultSignExtendBB bitblasting " << node  << "\n";
  
  Assert (node.getKind() == kind::BITVECTOR_SIGN_EXTEND);
  Bits* bits = bb->bbTerm(node[0]);
  
  SatLit sign_bit = bits->operator[](0); 
  unsigned amount = node.getOperator().getConst<BitVectorSignExtend>().signExtendAmount; 
  Bits* res_bits = new Bits();

  for (unsigned i = 0 ; i < amount ; ++i ) {
    res_bits->push_back(sign_bit); 
  }
  for (unsigned i = 0; i < bits->size(); ++i ) {
    res_bits->push_back(bits->operator[](i)); 
  }
  Assert (res_bits->size() == amount + bits->size()); 
  return res_bits; 
}

Bits* DefaultRotateRightBB (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}

Bits* DefaultRotateLeftBB  (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}


}
}
}



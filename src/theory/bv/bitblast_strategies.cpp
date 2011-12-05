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

  Unimplemented(); 
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
  Debug("bitvector-bb") << "theory::bv::DefaultNotBB bitblastinge " << node << "\n";
  
  Assert(node.getKind() == kind::BITVECTOR_NOT);

  const Bits* bv = bb->bbTerm(node[0]);
  Bits* notbv = bb->freshBits(utils::getSize(node[0])); 
    
  for (unsigned i = 0; i < bv->size(); i++) {
    // adding the constraints (lhs_i OR rhs_i) and (NOT lhs_i) OR (NOT rhs_i)
    bb->mkClause(neg(bv->operator[](i)), neg(notbv->operator[](i)) );
    bb->mkClause( bv->operator[](i),  notbv->operator[](i));
  }
  return notbv; 
}

Bits* DefaultConcatBB      (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultConcatBB bitblasting " << node << "\n";
  
  Assert (node.getKind() == kind::BITVECTOR_CONCAT);
  TNode first = node[0];
  TNode second = node[1]; 
  const Bits* bv1 = bb->bbTerm(first);
  const Bits* bv2 = bb->bbTerm(second);
    
  Bits* bits = new Bits();
    
  for(unsigned i = 0; i < utils::getSize(node[0]); ++i) {
    bits->push_back(bv1->operator[](i));
  }
    
  for(unsigned i = 0; i < utils::getSize(node[1]); ++i) {
    bits->push_back(bv2->operator[](i)); 
  }
  Assert (bits->size() == bv1->size() + bv2->size()); 
  return bits; 
}

Bits* DefaultAndBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultAndBB bitblasting " << node << "\n";
  
  Assert(node.getKind() == kind::BITVECTOR_AND);
  Bits* res = bb->freshBits(utils::getSize(node));
  
  Bits* lhs = bb->bbTerm(node[0]);
  Bits* rhs = bb->bbTerm(node[1]);
  
  Assert(res && lhs && rhs && bb);
  const Bits& c = *res;
  const Bits& a = *lhs;
  const Bits& b = *rhs;

  for (unsigned i = 0; i < c.size(); ++i) {
    bb->mkClause(neg(c[i]), a[i]);
    bb->mkClause(neg(c[i]), b[i]);
    bb->mkClause(c[i], neg(a[i]), neg(b[i])); 
  }
  return res; 
}

Bits* DefaultOrBB          (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultOrBB bitblasting " << node << "\n";

  Assert(node.getKind() == kind::BITVECTOR_OR);
  Bits* res = bb->freshBits(utils::getSize(node));
  Bits* lhs = bb->bbTerm(node[0]);
  Bits* rhs = bb->bbTerm(node[1]); 

  Assert (res && lhs && rhs);
  
  for (unsigned i = 0; i < res->size(); ++i) {
    bb->mkClause( res->operator[](i),     neg(lhs->operator[](i)) );
    bb->mkClause( res->operator[](i),     neg(rhs->operator[](i)) );
    bb->mkClause(neg(res->operator[](i)), lhs->operator[](i), rhs->operator[](i));
  }
  return res; 
}

Bits* DefaultXorBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector-bb") << "theory::bv::DefaultXorBB bitblasting " << node << "\n";

  Assert(node.getKind() == kind::BITVECTOR_XOR);
  Bits* res = bb->freshBits(utils::getSize(node));
  Bits* lhs = bb->bbTerm(node[0]);
  Bits* rhs = bb->bbTerm(node[1]); 
    
  Assert (res && lhs && rhs && bb);
  const Bits& c = *res;
  const Bits& a = *lhs;
  const Bits& b = *rhs; 
  for (unsigned i = 0; i < res->size(); ++i) {
    bb->mkClause(neg(c[i]), a[i], b[i]);
    bb->mkClause(neg(c[i]), neg(a[i]), neg(b[i]));
    bb->mkClause(c[i], neg(a[i]), b[i]);
    bb->mkClause(c[i], a[i], neg(b[i])); 
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
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultSubBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
}
Bits* DefaultNegBB         (TNode node, Bitblaster* bb) {
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
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
  Debug("bitvector") << "theory::bv:: Unimplemented kind "
                     << node.getKind() << "\n";
  Unimplemented(); 
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



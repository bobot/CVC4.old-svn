/*********************                                                        */
/*! \file bv_sat.cpp
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
 ** 
 **/

#include "bv_sat.h"
#include "theory_bv_utils.h"
using namespace BVMinisat; 
using namespace CVC4::theory::bv::utils;
namespace CVC4 {
namespace theory {
namespace bv{

/** Helper methods for printing */

// void printDebug (Minisat::Lit l) {
//   Debug("bitvectors") << (sign(l) ? "-" : "") << var(l) + 1 << endl;
// }

// void printDebug (Minisat::Clause& c) {
//   for (int i = 0; i < c.size(); i++) {
//     Debug("bitvectors") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " "; 
//   }
//   Debug("bitvectors") << endl;
// }



BVSolver::BVSolver():
  d_solver()
{}

void BVSolver::addClause(SatClause* clause) {
  d_solver.addClause(*clause); 
}

void BVSolver::addClause(SatLit lit) {
  d_solver.addClause(lit); 
}

bool BVSolver::solve() {
  return d_solver.solve(); 
}

SatVar BVSolver::newVar() {
  return d_solver.newVar(); 
}

/** class Bitblaster **/


void Bitblaster::assertToSat(TNode node) {
  bbAtom(node);
  Clauses cls;
  getBBAtom(node, cls);
  for (int i = 0; i < cls.size(); ++i) {
    d_solver.addClause(cls[i]); 
  }
}

bool Bitblaster::solve() {
  return d_solver.solve(); 
}

bool Bitblaster::getBBAtom(TNode node, Clauses& cl) {
  AtomClausesHashMap::iterator it = d_atomCache.find(node);
  if (it == d_atomCache.end()) {
    return false; 
  }
  cl = d_atomCache[node];
  return true; 
}

bool Bitblaster::getBBTerm(TNode node, Bits* &bits) {
  TermBitsHashMap::iterator it = d_termCache.find(node);
  if (it == d_termCache.end()) {
    return false; 
  }
  bits = d_termCache[node];
  return true; 
}


void Bitblaster::bbAtom(TNode node) {

  Clauses cls; 
  if(getBBAtom(node, cls)) {
    return; 
  }
  
  switch (node.getKind()) {
  case kind::EQUAL:
    bbEq(node);
    break;
  case kind::NOT:
    bbNeq(node);
    break;
  default:
    // TODO: implement other predicates
    Unhandled(node.getKind());
  }
}

void Bitblaster::bbEq(TNode node) {
  Assert(node.getKind() == kind::EQUAL);
  TNode lhs = node[0];
  TNode rhs = node[1];
  Bits* lhsBits = bbTerm(lhs);
  Bits* rhsBits = bbTerm(rhs);

  Assert(lhsBits->size() == rhsBits->size());
  Clauses eq; 
  for (int i = 0; i < lhsBits->size(); i++) {
    // adding the constraints lhs_i <=> rhs_i as lhs_i => rhs_i and rhs_i => lhs_i
    
    SatClause* clause1 = new SatClause(2);
    clause1->push(lhsBits->operator[](i));
    clause1->push(~rhsBits->operator[](i));

    SatClause* clause2 = new SatClause(2);
    clause2->push(~lhsBits->operator[](i));
    clause2->push(rhsBits->operator[](i));

    eq.push_back(clause1);
    eq.push_back(clause2);
  }
  d_atomCache[node] = eq; 
}

void Bitblaster::bbNeq(TNode node) {
  Assert(node.getKind()    == kind::NOT); 
  Assert(node[0].getKind() == kind::EQUAL);
  
  TNode lhs = node[0][0];
  TNode rhs = node[0][1];
  Bits* lhsBits = bbTerm(lhs);
  Bits* rhsBits = bbTerm(rhs);

  Assert(lhsBits->size() == rhsBits->size());
  Clauses diseq; 
  for (int i = 0; i < lhsBits->size(); i++) {
    // adding the constraints (lhs_i OR rhs_i) and (NOT lhs_i) OR (NOT rhs_i)
    
    SatClause* clause1 = new SatClause(2);
    clause1->push(lhsBits->operator[](i));
    clause1->push(rhsBits->operator[](i));

    SatClause* clause2 = new SatClause(2);
    clause2->push(~lhsBits->operator[](i));
    clause2->push(~rhsBits->operator[](i));

    diseq.push_back(clause1);
    diseq.push_back(clause2);
  }
  d_atomCache[node] = diseq;
}


Bits* Bitblaster::bbConst(TNode node) {
  Assert(node.getKind() == kind::CONST_BITVECTOR);
  for (int i = 0; i < getSize(node); ++i) {
    // TODO : finish!! 
  }
}

Bits* Bitblaster::bbVar(TNode node) {
  Assert (node.getKind() == kind::VARIABLE);
  Bits* bits = new Bits(getSize(node));  
  for (int i= 0; i < getSize(node); ++i) {
    SatVar var = d_solver.newVar();
    SatLit lit = mkLit(var); 
    bits->operator[](i) = lit; 
  }
  d_termCache[node] = bits;
  return bits; 
}

Bits* Bitblaster::bbExtract(TNode node) {
  Assert (node.getKind() == kind::BITVECTOR_EXTRACT);
  Bits* bits = bbTerm(node[0]);
  unsigned high = getExtractHigh(node);
  unsigned low  = getExtractLow(node);
  // TODO: double check this!!
  Bits* extractbits = new Bits(); 
  for (unsigned i = bits->size() - 1 - high; i < bits->size() -1 - low; ++i) {
    extractbits->push_back(bits->operator[](i)); 
  }
  d_termCache[node] = extractbits;
  return extractbits; 
}

Bits* Bitblaster::bbConcat(TNode node) {
  Assert (node.getKind() == kind::BITVECTOR_CONCAT);
  Bits* bv1 = bbTerm(node[0]);
  Bits* bv2 = bbTerm(node[1]);

  Bits* bits = new Bits(bv1->size() + bv2->size());

  for(unsigned i = 0; i < getSize(node[0]); ++i) {
    bits->push_back(bv1->operator[](i));
  }
  
  for(unsigned i = 0; i < getSize(node[1]); ++i) {
    bits->push_back(bv2->operator[](i)); 
  }
  return bits; 
}

Bits* Bitblaster::bbTerm(TNode node) {
  Bits* bits;
  // first check the cache
  if (getBBTerm(node, bits)) {
    return bits; 
  }
  
  switch(node.getKind()) {
    
  case kind::BITVECTOR_CONCAT:
    return bbConcat(node);
    
  case kind::BITVECTOR_EXTRACT:
    return bbExtract(node);
    
  case kind::VARIABLE:
    return bbVar(node);

  case kind::CONST_BITVECTOR:
    return bbConst(node);
    
  default:
    Unhandled(node.getKind());
  }
}

} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/

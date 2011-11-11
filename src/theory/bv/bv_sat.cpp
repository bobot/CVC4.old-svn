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
#include "picosat/picosat.h"
using namespace std;
using namespace BVMinisat; 
using namespace CVC4::theory::bv::utils;
namespace CVC4 {
namespace theory {
namespace bv{



/** Helper methods for printing */

// void printLit (SatLit l) {
//   Debug("bitvector") << (sign(l) ? "-" : "") << var(l) + 1 << std::endl;
// }
// void printClause (SatClause& c) {
//   for (int i = 0; i < c.size(); i++) {
//     Debug("bitvector") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " "; 
//   }
//   Debug("bitvector") << std::endl;
// }

void printBits (Bits& c) {
  for (int i = 0; i < c.size(); i++) {
    Debug("bitvector") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " "; 
  }
  Debug("bitvector") << std::endl;
}


/// CanonicalClause
template <class T, class H, class L> 
void CanonicalClause<T, H, L>::addLiteral(T lit) {
  for (typename list<T>::iterator it = d_data.begin(); it!=d_data.end(); ++it) {
    T elem = *it; 
    if (L::compare(lit, elem)) {
      ++it; 
      d_data.insert(it, lit);
      return; 
    }
  }
}

template <class T, class H, class L> 
bool CanonicalClause<T, H, L> ::operator==(const CanonicalClause<T, H, L>& other) const{
  if (d_data.size() != other.d_data.size()) {
    return false; 
  }
  typename list<T>::const_iterator it1 = d_data.begin();
  typename list<T>::const_iterator it2 = other.d_data.begin();
  for (; it1 != d_data.end(); ++it1, ++it2) {
    if (*it1 != *it2) {
      return false;
    }
  }
  return true; 
}

/// BVSolver 


BVSolver::BVSolver():
  d_solver()
{}

void BVSolver::addClause(SatClause* clause) {
  // TODO add conversion method
  // FIXME! convert from my clause to minisatclause or add new clause adding function to minisat
  // d_solver.addClause(*clause); 
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


/// MinisatClauseManager

int MinisatClauseManager::idCount = 0; 

SatClause* MinisatClauseManager::getClause(ClauseId id) {
  Assert (d_idClauseMap.find(id) != d_idClauseMap.end());
  return d_idClauseMap[id]; 
}

ClauseId MinisatClauseManager::getId(SatClause*cl ) {
  Assert (cl != NULL); 
  Assert (d_clauseIdMap.find(*cl) != d_clauseIdMap.end());
  return d_clauseIdMap[*cl]; 
}

void MinisatClauseManager::assertClause(ClauseId id) {
  SatClause* clause = getClause(id);
  // FIXME!!
  // d_solver->addClause(clause); 
}

bool MinisatClauseManager::solve() {
  return d_solver->solve(); 
}



bool MinisatClauseManager::inPool(SatClause* clause) {
  Assert (clause != NULL); 
  return d_clauseIdMap.find(*clause) != d_clauseIdMap.end();
}


ClauseId MinisatClauseManager::mkClause(SatLit lit1, SatLit lit2) {
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  
  if(inPool(clause)) {
    return getId(clause); 
  }
  
  d_clauseIdMap[*clause]  = ++idCount;
  d_idClauseMap[idCount] = clause;

  return idCount; 
}

ClauseId MinisatClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3) {
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);

  if(inPool(clause)) {
    return getId(clause); 
  }

  d_clauseIdMap[*clause]  = ++idCount;
  d_idClauseMap[idCount] = clause;

  return idCount; 
}

ClauseId MinisatClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4) {
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->addLiteral(lit4); 

  if(inPool(clause)) {
    return getId(clause); 
  }
  
  d_clauseIdMap[*clause]  = ++idCount;
  d_idClauseMap[idCount] = clause;
  
  return idCount; 
}

ClauseId MinisatClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5) {
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->addLiteral(lit4); 
  clause->addLiteral(lit5); 

  if(inPool(clause)) {
    return getId(clause); 
  }
  
  d_clauseIdMap[*clause]  = ++idCount;
  d_idClauseMap[idCount] = clause;

  return idCount; 
}


/** class Bitblaster **/


// void Bitblaster::assertToSat(TNode node) {
//   bbAtom(node);
//   Clauses cls;
//   getBBAtom(node, cls);
//   for (int i = 0; i < cls.size(); ++i) {
//     d_solver.addClause(cls[i]); 
//   }
// }

// bool Bitblaster::solve() {
//   return d_solver.solve(); 
// }

// bool Bitblaster::getBBAtom(TNode node, Clauses& cl) {
//   AtomClausesHashMap::iterator it = d_atomCache.find(node);
//   if (it == d_atomCache.end()) {
//     return false; 
//   }
//   cl = d_atomCache[node];
//   return true; 
// }

// bool Bitblaster::getBBTerm(TNode node, Bits* &bits) {
//   TermBitsHashMap::iterator it = d_termCache.find(node);
//   if (it == d_termCache.end()) {
//     return false; 
//   }
//   bits = d_termCache[node];
//   return true; 
// }


// void Bitblaster::bbAtom(TNode node) {

//   Clauses cls; 
//   if(getBBAtom(node, cls)) {
//     return; 
//   }
  
//   switch (node.getKind()) {
//   case kind::EQUAL:
//     bbEq(node);
//     break;
//   case kind::NOT:
//     bbNeq(node);
//     break;
//   default:
//     // TODO: implement other predicates
//     Unhandled(node.getKind());
//   }
// }

// void Bitblaster::bbEq(TNode node) {
//   Assert(node.getKind() == kind::EQUAL);
//   Bits& lhsBits = bbTerm(node[0])->bits();
//   Bits& rhsBits = bbTerm(node[1])->bits();

//   Assert(lhsBits.size() == rhsBits.size());
//   Clauses eq; 
//   for (int i = 0; i < lhsBits->size(); i++) {
//     // adding the constraints lhs_i <=> rhs_i as lhs_i => rhs_i and rhs_i => lhs_i
//     eq.push_back(mkClause(lhsBits[i], ~rhsBits[i]));
//     eq.push_back(mkClause(~lhsBits[i], rhsBits[i]));
//   }
//   cacheAtom(node, eq); 
// }

// void Bitblaster::bbNeq(TNode node) {
//   Assert(node.getKind() == kind::EQUAL);
//   Bits& lhsBits = bbTerm(node[0])->bits();
//   Bits& rhsBits = bbTerm(node[1])->bits();

//   Assert(lhsBits.size() == rhsBits.size());
//   Clauses eq; 
//   for (int i = 0; i < lhsBits->size(); i++) {
//     // adding the constraints (lhs_i OR rhs_i) and (NOT lhs_i) OR (NOT rhs_i)
//     eq.push_back(mkClause(~lhsBits[i], ~rhsBits[i]));
//     eq.push_back(mkClause( lhsBits[i],  rhsBits[i]));
//   }
//   cacheAtom(node, eq); 
// }


// BVTermDefinition* Bitblaster::bbConst(TNode node) {
//   Assert(node.getKind() == kind::CONST_BITVECTOR);
//   for (int i = 0; i < getSize(node); ++i) {
//     // TODO : finish!!
//     return NULL; 
//   }
// }

// void Bitblaster::freshBits(Bits& bits, unsigned size) {
//   for (int i= 0; i < size; ++i) {
//     SatVar var = d_solver.newVar();
//     SatLit lit = mkLit(var); 
//     bits.push_back(lit); 
//   }
// }

// BVTermDefinition* bbVar(TNode node) {
//   Assert (node.getKind() == kind::VARIABLE);
//   Bits bits;
//   freshBits(bits, getSize(node));
  
//   return def; 
// }


// BVTermDefinition* Bitblaster::bbExtract(TNode node) {
//   Assert (node.getKind() == kind::BITVECTOR_EXTRACT);
//   Bits* bits = bbTerm(node[0]);
//   unsigned high = getExtractHigh(node);
//   unsigned low  = getExtractLow(node);
//   // TODO: double check this!!
//   Bits* extractbits = new Bits(); 
//   for (unsigned i = bits->size() - 1 - high; i <= bits->size() -1 - low; ++i) {
//     extractbits->push_back(bits[i]); 
//   }
//   d_termCache[node] = extractbits;
//   return extractbits; 
// }

// BVTermDefinition* Bitblaster::bbConcat(TNode node) {
//   Assert (node.getKind() == kind::BITVECTOR_CONCAT);
//   Bits& bv1 = bbTerm(node[0])->bits();
//   Bits& bv2 = bbTerm(node[1])->bits();

//   Bits bits;

//   for(unsigned i = 0; i < getSize(node[0]); ++i) {
//     bits.push_back(bv1[i]);
//   }
  
//   for(unsigned i = 0; i < getSize(node[1]); ++i) {
//     bits.push_back(bv2[i]); 
//   }
//   return bits; 
// }



} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/

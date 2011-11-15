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
using namespace CVC4::context; 
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
  for (unsigned i = 0; i < c.size(); i++) {
    Debug("bitvector") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " "; 
  }
  Debug("bitvector") << std::endl;
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
  SatClause* cl = getClause(id);
  assertClause(cl); 
}

void MinisatClauseManager::assertClause(SatClause* cl) {
  Assert (cl);
  SatClause& clause = *cl;
  vec<SatLit> minisat_clause;
  for (unsigned i = 0; i < clause.size(); ++i ) {
    minisat_clause.push(clause[i]); 
  }
  d_solver->addClause(minisat_clause); 
}

bool MinisatClauseManager::solve() {
  d_canAddClause = false; 
  d_solver->solve(); 
  return true; 
}

bool MinisatClauseManager::solve(const CDList<SatLit>& assumptions) {
  /// pass the assumed marker literals to the solver
  context::CDList<SatLit>::const_iterator it = assumptions.begin();
  BVMinisat::vec<SatLit> assump; 
  for(; it!= assumptions.end(); ++it) {
    SatLit lit = *it;
    assump.push(~lit); 
  }
  d_canAddClause = false; 
  bool res = d_solver->solve(assump);
  return res; 
}

void MinisatClauseManager::resetSolver() {
  delete d_solver;
  d_solver = NULL; 
  d_solver = new BVMinisat::Solver(); 
}


bool MinisatClauseManager::inPool(SatClause* clause) {
  Assert (clause != NULL); 
  return d_clauseIdMap.find(*clause) != d_clauseIdMap.end();
}


SatLit MinisatClauseManager::mkLit(SatVar& var) {
  return BVMinisat::mkLit(var); 
}

SatVar MinisatClauseManager::newVar() {
  return d_solver->newVar(); 
}

ClauseId MinisatClauseManager::mkClause(SatLit lit1, SatLit lit2) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->sort(); 
  
  if(inPool(clause)) {
    return getId(clause); 
  }
  
  d_clauseIdMap[*clause]  = ++idCount;
  d_idClauseMap[idCount] = clause;

  assertClause(clause); 
  return idCount; 
}

ClauseId MinisatClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->sort(); 

  if(inPool(clause)) {
    return getId(clause); 
  }

  d_clauseIdMap[*clause]  = ++idCount;
  d_idClauseMap[idCount] = clause;
  assertClause(clause); 
  return idCount; 
}

ClauseId MinisatClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->addLiteral(lit4); 
  clause->sort();
  
  if(inPool(clause)) {
    return getId(clause); 
  }
  
  d_clauseIdMap[*clause]  = ++idCount;
  d_idClauseMap[idCount] = clause;
  assertClause(clause); 
  return idCount; 
}

ClauseId MinisatClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->addLiteral(lit4); 
  clause->addLiteral(lit5); 
  clause->sort(); 
  
  if(inPool(clause)) {
    return getId(clause); 
  }
  
  d_clauseIdMap[*clause]  = ++idCount;
  d_idClauseMap[idCount] = clause;
  assertClause(clause); 
  return idCount; 
}


/** class Bitblaster **/

// template <class Add, class Mult, class Or, class And>
// void Bitblaster<Add, Mult, Or, And>::assertToSat(TNode node) {
//   ClauseIds* def = bbAtom(node);
//   for (int i = 0; i < def->size(); ++i) {
//     d_clauseManager->assertClause(def->operator[](i) ); 
//   }
// }

// template <class Add, class Mult, class Or, class And>
// bool Bitblaster<Add, Mult, Or, And>::solve() {
//   return d_clauseManager->solve(); 
// }

// template <class Add, class Mult, class Or, class And>
// void Bitblaster<Add, Mult, Or, And>::resetSolver() {
//   d_clauseManager->resetSolver(); 
// }








} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/

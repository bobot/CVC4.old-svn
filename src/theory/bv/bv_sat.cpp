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
using namespace std;

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

// void printBits (Bits& c) {
//   for (unsigned i = 0; i < c.size(); i++) {
//     Debug("bitvector") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " "; 
//   }
//   Debug("bitvector") << std::endl;
// }


/// ClauseManager
ClauseManager::ClauseManager():
    d_solver(new SatSolver() ),
    d_clausePool(),
    d_canAddClause(true),
    d_conflict(NULL)
  {}

ClauseManager::~ClauseManager() {
  // TODO: clean up all newly allocated clauses and such 
}

SatClause* ClauseManager::getConflict() {
  return d_solver->getUnsatCore();  
}

void ClauseManager::assertClause(SatClause* cl) {
  Assert (cl);
  d_solver->addClause(cl);
}

bool ClauseManager::solve() {
  d_canAddClause = false; 
  return d_solver->solve(); 
}

bool ClauseManager::solve(const CDList<SatLit>& assumptions) {
  /// the only clauses that should be "active" now are the term definitions
  /// which must be consistent
  Assert (d_solver->solve());
  // do not allow adding more clauses
  d_canAddClause = false;
  // solve with the marker literals as assumptions
  return d_solver->solve(assumptions); 
}

void ClauseManager::resetSolver() {
  delete d_solver;
  d_solver = NULL; 
  d_solver = new SatSolver();
  d_canAddClause = true; 
}


bool ClauseManager::inPool(SatClause* clause) {
  Assert (clause != NULL); 
  return d_clausePool.find(*clause) != d_clausePool.end(); 
}


SatLit ClauseManager::mkLit(SatVar var) {
  return d_solver->mkLit(var); 
}

SatLit ClauseManager::mkMarkerLit() {
  SatLit lit = mkLit(newVar());
  d_solver->setUnremovable(lit);
  return lit; 
}

SatVar ClauseManager::newVar() {
  return d_solver->newVar(); 
}



void ClauseManager::mkClause(const vector<SatLit>& lits) {
  Assert (d_canAddClause); 
  SatClause* clause = new SatClause(); 
  for (unsigned i = 0; i < lits.size(); ++i) {
    clause->addLiteral(lits[i]); 
  }
  clause->sort();

  if(inPool(clause)) {
    return; 
  }

  d_clausePool.insert(*clause); 
  assertClause(clause); 

}

void ClauseManager::mkClause(SatLit lit1) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->sort(); 
  
  if(inPool(clause)) {
    return;
  }
  d_clausePool.insert(*clause); 
  assertClause(clause); 
}



void ClauseManager::mkClause(SatLit lit1, SatLit lit2) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->sort(); 
  
  if(inPool(clause)) {
    return;
  }
  d_clausePool.insert(*clause); 
  assertClause(clause); 
}

void ClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->sort(); 

  if(inPool(clause)) {
    return;
  }

  d_clausePool.insert(*clause); 
  assertClause(clause); 

}

void ClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->addLiteral(lit4); 
  clause->sort();

  if(inPool(clause)) {
    return;
  }
  
  d_clausePool.insert(*clause); 
  assertClause(clause); 
}

void ClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->addLiteral(lit4); 
  clause->addLiteral(lit5); 
  clause->sort(); 

  if(inPool(clause)) {
    return;
  }
  
  d_clausePool.insert(*clause); 
  assertClause(clause); 
}

// void ClauseManager::mkMarkedClause(SatLit marker, SatLit lit1) {
//   Assert (d_canAddClause);
  
//   SatClause* clause = new SatClause();
//   clause->addLiteral(marker); 
//   clause->addLiteral(lit1);
//   clause->sort();
  
//   // make sure the marker literal does not get eliminated 
//   d_solver->setUnremovable(marker); 
//   assertClause(clause); 
// }


// void ClauseManager::mkMarkedClause(SatLit marker, SatLit lit1, SatLit lit2) {
//   Assert (d_canAddClause);
  
//   SatClause* clause = new SatClause();
//   clause->addLiteral(marker); 
//   clause->addLiteral(lit1);
//   clause->addLiteral(lit2);
//   clause->sort(); 

//   // make sure the marker literal does not get eliminated 
//   d_solver->setUnremovable(marker); 
//   assertClause(clause); 
// }

// void ClauseManager::mkMarkedClause(SatLit marker, SatLit lit1, SatLit lit2, SatLit lit3) {
//   Assert (d_canAddClause);
  
//   SatClause* clause = new SatClause();
//   clause->addLiteral(marker); 
//   clause->addLiteral(lit1);
//   clause->addLiteral(lit2);
//   clause->addLiteral(lit3);
//   clause->sort(); 

//   // make sure the marker literal does not get eliminated 
//   d_solver->setUnremovable(marker); 
//   assertClause(clause); 

// }

// void ClauseManager::mkMarkedClause(SatLit marker, SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4) {
//   Assert (d_canAddClause);
  
//   SatClause* clause = new SatClause();
//   clause->addLiteral(marker); 
//   clause->addLiteral(lit1);
//   clause->addLiteral(lit2);
//   clause->addLiteral(lit3);
//   clause->addLiteral(lit4); 
//   clause->sort();

//   // make sure the marker literal does not get eliminated 
//   d_solver->setUnremovable(marker); 
//   assertClause(clause); 
// }

// void ClauseManager::mkMarkedClause(SatLit marker, SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5) {
//   Assert (d_canAddClause);
  
//   SatClause* clause = new SatClause();
//   clause->addLiteral(marker); 
//   clause->addLiteral(lit1);
//   clause->addLiteral(lit2);
//   clause->addLiteral(lit3);
//   clause->addLiteral(lit4); 
//   clause->addLiteral(lit5); 
//   clause->sort(); 

//   // make sure the marker literal does not get eliminated 
//   d_solver->setUnremovable(marker); 
//   assertClause(clause); 
// }




} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/

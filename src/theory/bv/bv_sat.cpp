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

std::string toString(Bits* bits) {
  Assert(bits);
  ostringstream os;
  os << "["; 
  for (unsigned i = 0; i < bits->size(); ++i) {
    os << toStringLit(bits->operator[](i)) << (i == bits->size() - 1 ? "": " "); 
  }
  os << "] \n";
  return os.str(); 
}

void printClause (SatClause& c) {
  Debug("bitvector") << c.toString() <<"\n"; 
}


/// ClauseManager
ClauseManager::ClauseManager():
    d_solver(new SatSolver() ),
    //    d_clausePool(),
    d_canAddClause(true),
    d_conflict(NULL),
    d_statistics()
  {}

ClauseManager::Statistics::Statistics() :
  d_numVariables("theory::bv::NumberOfSatVariables", 0),
  d_numTotalClauses("theory::bv::TotalNumberOfAssertedSatClauses",0),
  d_satSolveTimer("theory::bv::SatSolvingTimer"),
  d_unsatCoreTimer("theory::bv::UnsatCoreTimer"),
  d_avgClauseSize("theory::bv::AvgBVClauseSize"),
  d_numDuplicateClauses("theory::bv::NumberOfDuplicateSatClauses", 0)
{
  StatisticsRegistry::registerStat(&d_numVariables);
  StatisticsRegistry::registerStat(&d_numTotalClauses);
  StatisticsRegistry::registerStat(&d_satSolveTimer);
  StatisticsRegistry::registerStat(&d_unsatCoreTimer);
  StatisticsRegistry::registerStat(&d_avgClauseSize);
  StatisticsRegistry::registerStat(&d_numDuplicateClauses);
}

ClauseManager::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numVariables);
  StatisticsRegistry::unregisterStat(&d_numTotalClauses);
  StatisticsRegistry::unregisterStat(&d_satSolveTimer);
  StatisticsRegistry::unregisterStat(&d_unsatCoreTimer);
  StatisticsRegistry::unregisterStat(&d_avgClauseSize);
  StatisticsRegistry::unregisterStat(&d_numDuplicateClauses);
}


ClauseManager::~ClauseManager() {
  delete d_solver;
  delete d_conflict; 
  // TODO: clean up all newly allocated clauses and such 
}

SatClause* ClauseManager::getConflict() {
  TimerStat::CodeTimer codeTimer(d_statistics.d_unsatCoreTimer);
  return d_solver->getUnsatCore();  
}

void ClauseManager::assertClause(SatClause* cl) {
  Assert (cl);

  ++(d_statistics.d_numTotalClauses);
  d_statistics.d_avgClauseSize.addEntry(cl->size()); 

  d_solver->addClause(cl);
}

bool ClauseManager::solve() {
  TimerStat::CodeTimer codeTimer(d_statistics.d_satSolveTimer);
  d_canAddClause = false; 
  bool res =  d_solver->solve();
  return res; 
}

bool ClauseManager::solve(const CDList<SatLit>& assumptions) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_satSolveTimer);
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


// bool ClauseManager::inPool(SatClause* clause) {
//   Assert (clause != NULL); 
//   bool res = d_clausePool.find(*clause) != d_clausePool.end();
//   if(res) {
//     ++(d_statistics.d_numDuplicateClauses); 
//   }
//   return res; 
// }


SatVar ClauseManager::mkMarkerVar() {
  SatVar var = newVar();
  d_solver->setUnremovable(mkLit(var));
  return var; 
}

SatVar ClauseManager::newVar() {
  ++(d_statistics.d_numVariables); 
  return d_solver->newVar(); 
}

void ClauseManager::mkClause(const vector<SatLit>& lits) {
  Assert (d_canAddClause); 
  SatClause* clause = new SatClause(); 
  for (unsigned i = 0; i < lits.size(); ++i) {
    clause->addLiteral(lits[i]); 
  }
  clause->sort();

  // if(inPool(clause)) {
  //   return; 
  // }

  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 
  // d_clausePool.insert(*clause); 
  assertClause(clause); 

}

void ClauseManager::mkClause(SatLit lit1) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->sort(); 
  
  // if(inPool(clause)) {
  //   return;
  // }
  
  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 
  // d_clausePool.insert(*clause); 
  assertClause(clause); 
}



void ClauseManager::mkClause(SatLit lit1, SatLit lit2) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->sort(); 
  
  // if(inPool(clause)) {
  //   return;
  // }

  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 
  // d_clausePool.insert(*clause); 
  assertClause(clause); 
}

void ClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->sort(); 

  // if(inPool(clause)) {
  //   return;
  // }
  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 
  // d_clausePool.insert(*clause); 
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

  // if(inPool(clause)) {
  //   return;
  // }

  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 
  // d_clausePool.insert(*clause); 
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

  // if(inPool(clause)) {
  //   return;
  // }

  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 
  // d_clausePool.insert(*clause); 
  assertClause(clause); 
}




} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/

/*********************                                                        */
/*! \file sat_proof.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Resolution proof 
 **
 ** Resolution proof
 **/

#ifndef __CVC4__SAT__PROOF_H
#define __CVC4__SAT__PROOF_H

#include <iostream>
#include <stdint.h>
#include <vector>
#include <set>
#include <ext/hash_map>
#include <ext/hash_set>

namespace Minisat {
class Solver;
typedef uint32_t CRef;
}

#include "prop/minisat/core/SolverTypes.h"

namespace std {
using namespace __gnu_cxx;
}

namespace CVC4 {
/** 
 * Helper debugging functions
 * 
 */
void print(Minisat::Lit l);
void print(Minisat::Clause& c); 
// TODO: move in resolution proof class? 
typedef int ClauseId;
typedef std::pair < Minisat::Lit, ClauseId > ResStep; 
typedef std::vector< ResStep > ResSteps; 
typedef std::set < Minisat::Lit> LitSet; 

class ResChain {
private:
  ClauseId       d_start;
  ResSteps       d_steps;
  LitSet*        d_redundantLits;
public:
  ResChain(ClauseId start);
  void addStep(Minisat::Lit, ClauseId);
  void finalizeRes();
  void addRedundantLit(Minisat::Lit lit); 
  ~ResChain();
  // accessor methods
  ClauseId  getStart() { return d_start; }
  ResSteps& getSteps() { return d_steps; }
};
typedef std::hash_map < ClauseId, Minisat::CRef > IdClauseMap;
typedef std::hash_map < Minisat::CRef, ClauseId > ClauseIdMap;
typedef std::hash_map < ClauseId, Minisat::Lit>   IdUnitMap;
typedef std::hash_map < int, ClauseId>            UnitIdMap; //FIXME 
typedef std::hash_map < ClauseId, ResChain*>      IdResMap; 
typedef std::hash_set < ClauseId >                IdSet;
typedef std::vector   < ResChain* >               ResStack; 


class ResolutionProof {
private:
  Minisat::Solver*     d_solver; 
  IdClauseMap d_idClause;
  ClauseIdMap d_clauseId;
  IdUnitMap   d_idUnit;
  UnitIdMap   d_unitId;
  IdResMap    d_resChains;
  IdSet       d_deletedIds;
  IdSet       d_inputClauses; 
  ResStack    d_resStack; 
  bool        d_checkRes; 
  static ClauseId d_idCounter; 
  const ClauseId  d_emptyClauseId;
  const ClauseId  d_nullId; 
public:  
  ResolutionProof(Minisat::Solver* solver, bool checkRes = false);
private:
  bool isInputClause(ClauseId id) {
    return (d_inputClauses.find(id) != d_inputClauses.end()); 
  }
  bool isUnit(ClauseId id);
  bool hasResolution(ClauseId id); 
  void createLitSet(ClauseId id, LitSet& set); 
  
  void     registerResolution(ClauseId id, ResChain* res);

  ClauseId      getClauseId(Minisat::CRef clause);
  Minisat::CRef getClauseRef(ClauseId id);
  Minisat::Lit  getUnit(ClauseId id); 
  void printLFSCProof() const;
  bool checkResolution(ClauseId id);
  /** 
   * Constructs a resolution tree that proves lit
   * and returns the ClauseId for the unit clause lit
   * @param lit the literal we are proving
   * 
   * @return 
   */
  ClauseId resolveUnit(Minisat::Lit lit); 
public:
  void startResChain(Minisat::CRef start);
  void addResolutionStep(Minisat::Lit lit, Minisat::CRef clause);
  void endResChain(Minisat::CRef clause);
  void endUnitResChain(Minisat::Lit lit); 
  
  void updateCRef(Minisat::CRef old_ref, Minisat::CRef new_ref);
  void finishUpdateCRef();
  void storeLitRedundant(Minisat::Lit lit);

  void finalizeProof(Minisat::CRef conflict);

  void markDeleted(Minisat::CRef clause); 

  ClauseId registerClause(const Minisat::CRef clause, bool isInput = false);
  ClauseId registerUnitClause(const Minisat::Lit lit, bool isInput = false);

};
  
}

#endif

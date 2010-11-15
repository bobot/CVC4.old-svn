/*********************                                                        */
/*! \file sat_proof.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A proof class.
 **
 ** A proof class.
 **/

#ifndef Sat_proof_h
#define Sat_proof_h

#include <vector>
#include <ext/hash_map>
#include <ext/hash_set>
#include <iostream>
#include <sstream>
#include <map>

#include <utility>
#include "util/proof.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/core/Solver.h"
#include "util/Assert.h"

namespace Minisat{
  class Solver;
}

namespace std {
using namespace __gnu_cxx;
}


namespace CVC4 {

namespace prop{

typedef int ClauseID;
struct ResStep {
  Minisat::Lit lit;
  ClauseID id;
  bool sign;
};

class SatResolution {
public:
                ClauseID d_start_clause;
                std::vector<ResStep> d_steps;

public:

                SatResolution(){}
                SatResolution (ClauseID clause_id): d_start_clause(clause_id){}

                void addStep(Minisat::Lit lit, ClauseID clause_id, bool sign){
                  ResStep step;
                  step.lit = lit;
                  step.id = clause_id;
                  step.sign = sign;
                  d_steps.push_back(step);
                }

                ClauseID getStart() const {
                        return d_start_clause;
                }

                const std::vector<ResStep> getSteps() const{
                        return d_steps;
                }
};



class Derivation{
public:
  std::hash_set <ClauseID> d_input_clauses;              // the input clauses assumed true
  std::hash_set <ClauseID> d_needed_input; //FIXME!
  std::hash_set <int> d_vars;                            // the set of variables that appear in the proof
  std::set <ClauseID> d_sat_lemmas;      // the resolution chains that will be printed as sat lemmas

  std::map <ClauseID, Minisat::CRef> d_id_clause;             // map from clause id to clauses
  std::map <Minisat::CRef, ClauseID> d_clause_id;             // map from clauses to clause id

  /* temporary for memory reallocation during garbage collection */
  std::map <ClauseID, Minisat::CRef> d_id_clause_tmp;             // map from clause id to clauses
  std::map <Minisat::CRef, ClauseID> d_clause_id_tmp;             // map from clauses to clause id

  std::hash_set <ClauseID> d_deleted;          //  stores the clauses deleted from the minisat database

  std::hash_map <int, ClauseID > d_unit_clauses;          // the set of unit clauses, indexed by value of variable for easy searching
  std::hash_map <ClauseID, int> d_unit_ids;               // reverse map of d_unit_clauses

  std::hash_map <ClauseID, SatResolution*> d_res_map;     // a map from clause id's to the boolean resolution derivation of that respective clause
  Minisat::Solver* d_solver;
  ClauseID d_empty_clause_id;
  SatResolution* d_current;                // stack of resolutions, the top one is the current one

  Minisat::vec<Minisat::Lit> eliminated_lit;      // vector storing the eliminated literals during conflict clause minimization


public:
  ClauseID static id_counter;
  Derivation(Minisat::Solver* solver) : d_solver(solver), d_empty_clause_id(0), d_current(NULL)
    {};

  /*
   * SOLVER INTERFACE
   *
   */
  void updateId(Minisat::CRef cr1, Minisat::CRef cr2);
  void finishUpdateId();

  void newResolution(Minisat::CRef confl, bool is_input=false);
  void newResolution(Minisat::Lit lit);

  void addResStep(Minisat::Lit l, Minisat::CRef cl, bool sign);
  void addResStep(Minisat::Lit l, Minisat::Lit l2, bool sign);
  void addResStepId(Minisat::Lit l, ClauseID id, bool sign);

  void endResolution(Minisat::CRef cl);
  void endResolution(Minisat::Lit lit);

  void orderDFS(Minisat::Lit p, Minisat::vec<Minisat::Lit> & ordered, Minisat::vec<Minisat::Lit> & units);
  void resolveMinimizedCC();
  void addEliminatedLit(Minisat::Lit lit);

  /*
   * REGISTRATION METHODS
   *
   */
  // register unit clause corresponding to lit
  // special case because Minisat does not store unit learned conflicts
  ClauseID registerClause(Minisat::Lit lit, bool is_input_clause = false);
  ClauseID registerClause(Minisat::CRef clause, bool is_input_clause = false);

  void registerResolution(Minisat::CRef clause, SatResolution* res);
  void registerResolution(ClauseID clause_id, SatResolution* res);

  /*
   * HELPER METHODS
   *
   */
  bool isUnit(Minisat::CRef cl);
  bool isUnit(Minisat::Lit lit);
  bool isUnit(ClauseID clause_id);
  bool isStoredClause(Minisat::CRef cl);

  bool isRegistered(Minisat::CRef cl);
  bool isRegistered(ClauseID cl_id);
  bool hasResolution(ClauseID cl_id);

  bool isLearned(ClauseID clause_id);
  bool isSatLemma(ClauseID clause_id);

  ClauseID newId();
  ClauseID getId(Minisat::CRef clause);
  ClauseID getUnitId(Minisat::CRef cl);
  ClauseID getUnitId(Minisat::Lit l);
  ClauseID getClauseId(Minisat::CRef cl);
  Minisat::Lit getUnit(ClauseID cl_id);
  SatResolution* getResolution(ClauseID clause_id);

  void markDeleted(Minisat::CRef clause);
  void storeVars(Minisat::CRef clause);

  /*
   * ACCESS TO THE SOLVER
   *
   */
  Minisat::Clause& getClause(Minisat::CRef cr);
  Minisat::CRef getReason(int v);

  /*
   * PROOF FINALIZING
   *
   */
  void addSatLemma(ClauseID clause_id);
  void lemmaProof(ClauseID clause_id);
  ClauseID getLitReason(Minisat::Lit lit);
  void finish(Minisat::CRef confl);

  /*
   * LFSC PROOF
   *
   */

  std::string printLFSCClause(Minisat::CRef cref);
  void printLFSCProof(Minisat::CRef final_confl);

  std::string printVar(Minisat::Lit l);
  std::string printClauseVar(ClauseID id);
  std::string printResChain(ClauseID id);

  /*
   * PRINTING
   *
   */
  void printLit(Minisat::Lit l);
  void printClause(Minisat::CRef cl);
  void printIdClause(ClauseID id);
  void printAllClauses();
  void printResolution(Minisat::CRef cl);
  void printResolution(ClauseID cl_id);

  /*
   * RESOLUTION CHECKING
   *
   */
  bool checkResolution(ClauseID clause_id);
  bool hasLit(Minisat::Lit l, Minisat::vec<Minisat::Lit>& cl);
  bool compareClauses(ClauseID id, Minisat::vec<Minisat::Lit>& ls2);
  bool resolve(Minisat::vec<Minisat::Lit> &cl1, ClauseID id, Minisat::Lit lit, bool sign);


};


}/* prop namespace */
}/* CVC4 namespace */
#endif

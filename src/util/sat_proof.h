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

//FIXME::no using namespace in header

using namespace Minisat;
namespace Minisat{
  class Solver;
}

namespace std {
using namespace __gnu_cxx;
}

namespace CVC4{
namespace prop{
class LFSCProof;
}
}


namespace CVC4 {

namespace prop{


// helper functions
typedef std::vector<std::pair <Lit, unsigned> >  RSteps;
typedef int ClauseID;


class SatResolution {
public:

                unsigned d_start_clause;
                RSteps d_steps;
                std::vector<bool> d_signs;

public:

                SatResolution(){}
                SatResolution (ClauseID clause_id): d_start_clause(clause_id){}

                void addStep(Lit lit, ClauseID clause_id, bool sign){
                  d_steps.push_back(std::make_pair(lit, clause_id));
                  d_signs.push_back(sign);
                }

                ClauseID getStart() const {
                        return d_start_clause;
                }

                const RSteps& getSteps() const{
                        return d_steps;
                }
                bool getSign(ClauseID i){
                  Assert(i< d_signs.size());
                  return d_signs[i];
                }

};



class Derivation{
public:
  std::hash_set <ClauseID> d_input_clauses;              // the input clauses assumed true
  std::hash_set <int> d_vars;                            // the set of variables that appear in the proof
  std::map <ClauseID, SatResolution*> d_sat_lemmas;      // the resolution chains that will be printed as sat lemmas

  std::map <ClauseID, CRef> d_id_clause;             // map from clause id to clauses
  std::map <CRef, ClauseID> d_clause_id;             // map from clauses to clause id

  /* temporary for memory reallocation during garbage collection */
  std::map <ClauseID, CRef> d_id_clause_tmp;             // map from clause id to clauses
  std::map <CRef, ClauseID> d_clause_id_tmp;             // map from clauses to clause id

  std::hash_set <ClauseID> d_deleted;          // stores the clauses deleted from the minisat database

  std::vector <ClauseID> d_lemma_stack;              // stack to print sat_lemmas in proper order
  std::hash_map <int, ClauseID > d_unit_clauses;          // the set of unit clauses, indexed by value of variable for easy searching
  std::hash_map <ClauseID, int> d_unit_ids;               // reverse map of d_unit_clauses

  std::hash_map <ClauseID, SatResolution*> d_res_map;     // a map from clause id's to the boolean resolution derivation of that respective clause
  Solver* d_solver;
  ClauseID d_empty_clause_id;
  std::vector<SatResolution*> d_current;                // stack of resolutions, the top one is the current one

public:
  ClauseID static id_counter;
  Derivation(Solver* solver) : d_solver(solver), d_empty_clause_id(0), d_current(NULL)
    {};

  /** solver interface **/

  void updateId(CRef cr1, CRef cr2);
  void finishUpdateId();
  void newResolution(CRef confl, bool is_input);
  void newResolution(Lit lit);
  void addResStep(Lit l, CRef cl, bool sign);
  void addResStep(Lit l, Lit l2, bool sign);
  void endResolution(CRef cl);
  void endResolution(Lit lit);
  void traceReason(Lit l, SatResolution* res);

public:

  /** registration methods**/

  // register unit clause corresponding to lit
  // special case because minisat does not store unit learned conflicts
  ClauseID registerClause(Lit lit);
  ClauseID registerClause(CRef clause, bool is_input_clause = false);

  void registerResolution(CRef clause, SatResolution* res);
  void registerResolution(ClauseID clause_id, SatResolution* res);

  /** helper methods **/

  bool isUnit(CRef cl);
  bool isUnit(Lit lit);
  bool isUnit(ClauseID clause_id);
  bool isStoredClause(CRef cl);

  bool isRegistered(CRef cl);
  bool isRegistered(ClauseID cl_id);
  bool hasResolution(ClauseID cl_id);

  bool isLearned(ClauseID clause_id);
  bool isSatLemma(ClauseID clause_id);

  ClauseID newId();
  ClauseID getId(CRef clause);
  ClauseID getUnitId(CRef cl);
  ClauseID getUnitId(Lit l);
  ClauseID getClauseId(CRef cl);
  Lit getUnit(ClauseID cl_id);
  SatResolution* getResolution(ClauseID clause_id);

  void markDeleted(CRef clause);
  void storeVars(CRef clause);

  std::string intToStr(int i);
  /** access to the solver**/

  Clause& cl(CRef cr);
  CRef getReason(int v);

  /** constructing the proof **/


  void addSatLemma(ClauseID clause_id);
  void lemmaProof(ClauseID clause_id);
  ClauseID getLitReason(Lit lit);
  void finish(CRef confl);

  /** constructing LFSC proof **/
  LFSCProof* getInputVariable(ClauseID confl_id);
  LFSCProof* satLemmaVariable(ClauseID clause_id);
  LFSCProof* derivToLFSC(ClauseID clause_id);
  LFSCProof* getProof(ClauseID clause_id);
  LFSCProof* addLFSCSatLemmas(LFSCProof* pf);

  /** debugging **/
  void printLit(Lit l);
  void printClause(CRef cl);
  void printIdClause(ClauseID id);
  void printAllClauses();
  void printResolution(CRef cl);
  void printResolution(ClauseID cl_id);

   /** resolution checking **/
  bool checkResolution(ClauseID clause_id);
  bool compareClauses(vec<Lit> ls1, vec<Lit> ls2);
  vec<Minisat::Lit> resolve(vec<Minisat::Lit> cl1, CRef cl2, Lit lit);
  vec<Minisat::Lit> resolve(vec<Minisat::Lit> cl1, Lit cl2, Lit lit);

  std::string printLFSCClause(CRef cref);
  void printLFSCProof(CRef final_confl);

};


}/* prop namespace */
}/* CVC4 namespace */
#endif

/*********************                                                        */
/*! \file proof.h
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

#include <vector>
#include <ext/hash_map>
#include <ext/hash_set>
#include <iostream>
#include <utility>
// do i need these includes?
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/core/Solver.h"

namespace std {
using namespace __gnu_cxx;
}

#ifndef __CVC4__PROOF_H_
#define __CVC4__PROOF_H_

namespace CVC4 {
namespace prop {
namespace minisat {


// helper functions
typedef std::vector<std::pair <Lit, unsigned> >  RSteps;

class SatResolution {
public:

		unsigned d_start_clause;
		RSteps d_steps;

public:
		
		SatResolution(){};
		SatResolution (int clause_id): d_start_clause(clause_id){};
		
		void addStep(Lit lit, unsigned clause_id){
		  d_steps.push_back(std::make_pair(lit, clause_id));
		} 
		
		int getStart() const {
			return d_start_clause;			
		}
		
		const RSteps& getSteps() const{
			return d_steps;
		}

};




class Derivation {
	private:
		std::hash_map <int, Clause*> d_clauses; 	// map from id's to clauses
		std::hash_set <int> d_input_clauses;		// the input clauses assumed true
		std::hash_map <int, Clause*> d_unit_clauses;		// the set of unit clauses, indexed by value of variable for easy searching
		std::hash_map <int, SatResolution*> d_res_map;	// a map from clause id's to the boolean resolution derivation of that respective clause
		Solver* d_solver;
		Clause* d_emptyClause;
	// TODO: do you need to store clauses removed from derivation? 
	public:
		int static id_counter;
		Derivation(Solver* solver) : d_emptyClause(NULL), d_solver(solver) {};
		void registerClause(Clause* clause, bool is_input_clause);
		void registerDerivation(int clause_id, SatResolution* res);
		// TODO: do we need to allow for duplicate insertion? see minisat_derivation.h in cvc3
		// don't really need to keep clauses, all you need to do is check that it's not the same.
		void finish(Clause* confl);
		int getRootReason(Lit l);
		void printDerivation(int clause_id);
		int new_id();
};

int Derivation::new_id(){
  return id_counter++;
}

void Derivation::registerClause(Clause* clause, bool is_input_clause){
    Debug("proof")<<"Registering clause id "<<clause->id()<<":: ";
    d_solver->printClause(*clause);
    Debug("proof")<<"\n";

    if(d_clauses.find(clause->id()) == d_clauses.end()){
      // if not already registered
      d_clauses[clause->id()] = clause;
      if(is_input_clause){
        // if it's an input clause
        d_input_clauses.insert(clause->id());
      }
    }
    else
      Debug("proof")<<"Clause already registered \n";

}

void Derivation::registerDerivation(int clause_id, SatResolution* res){
  Debug("proof")<<"Registering derivation clausse_id ="<<clause_id<<"\n";
  if(d_res_map.find(clause_id)== d_res_map.end()){
    d_res_map[clause_id] = res;
  }
}

int Derivation::getRootReason(Lit lit){
  Debug("proof")<<"getRootReason lit=";
  d_solver->printLit(lit);
  Debug("proof")<<"\n";

  Clause* reason = d_solver->getReason(lit);
  // TODO: add asserts to check stuff

  if(reason==NULL){
    Debug("proof")<<"Null Root Reason ";
    d_solver->printLit(lit);
    Debug("proof")<<" \n";
    return 0;
  }

  // if implied by an unit clause return the unit clause
  if((*reason).size() == 1)
    return reason->id();

  // if the literal is already an unit clause then it has a computed reason
  std::hash_map<int, Clause*>::const_iterator iter;
  iter = d_unit_clauses.find(toInt(lit));
  if(iter != d_unit_clauses.end()){
    return iter->second->id();
    }

  SatResolution* res = new SatResolution(reason->id());

  // starts from 1 because reason[0] = lit
  for(int i=1; i<(*reason).size();i++){
    //Clause* new_reas = d_solver->getReason((*reason)[i]);
    int root_res = getRootReason((*reason)[i]);
    res->addStep(~((*reason)[i]), root_res);
  }
  // add the literal as a unit clause
  std::vector<Lit> lits;
  lits.push_back(lit);
  Clause* unit = Clause_new(lits);
  d_unit_clauses[toInt(lit)] = unit;
  registerClause(unit, false);
  // add the derivation of the unit
  registerDerivation(unit->id(), res);
  return toInt(lit);
}


void Derivation::finish(Clause* confl){

  SatResolution* res = new SatResolution(confl->id());
  for (int i=0;i<(*confl).size();i++){
    Lit l = (*confl)[i];
    res->addStep(~l, getRootReason(~l));

  }
  registerDerivation(confl->id(), res);

  // printing derivation for debugging
  printDerivation(confl->id());
}

// helper functions

void Derivation::printDerivation(int clause_id){

  Debug("proof")<<"Derivation clause_id="<<clause_id<<": ";
  d_solver->printClause(* d_clauses.find(clause_id)->second);
  SatResolution* res = d_res_map.find(clause_id)->second;

  RSteps step = res->getSteps();
  Clause* cl = d_clauses.find(res->getStart())->second;
  Debug("proof")<<"\n ";

  d_solver->printClause(*cl);
  for(unsigned i=0;i< res->getSteps().size();i++){
    Debug("proof")<<"| ";
    d_solver->printLit(step[i].first);
    Debug("proof")<<"| ";
    Clause* clause = d_clauses.find(step[i].second)->second;
    d_solver->printClause(*clause);
  }
}


}/* CVC4::prop::minisat namespace */
}/* CVC4::prop namespace */
}/* CVC4 namespace */    
    
    
    
#endif /* __CVC4__PROOF_H_ */

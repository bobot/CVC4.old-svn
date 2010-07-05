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
		//void printRes();
		//void printRes(int index);
};


/*
void SatResolution::printRes(){
  printRes(d_steps.size()-1);
}

void SatResolution::printRes(int index){
  for (int i=index; i>=0;i--){
    std::cout<<"R ( ";
    printLit(first(d_steps[i]));
    std::cout<<", ";
    printClause(second(d_steps[i]));
    std::cout<<", ";
    printRes(index-1);
    std::cout<<") \n";
  }
}

*/

class Derivation {
	private:
		std::hash_map <int, Clause*> d_clauses; 	// map from id's to clauses
		std::hash_set <int> d_input_clauses;		// the input clauses assumed true
		std::hash_map <int, Clause*> d_unit_clauses;		// the set of unit clauses, indexed by value of variable for easy searching
		std::hash_map <int, SatResolution*> d_res_map;	// a map from clause id's to the boolean resolution derivation of that respective clause
		
		Clause* d_emptyClause;
	// TODO: do you need to store clauses removed from derivation? 
	public:
		Derivation() : d_emptyClause(NULL) {};
		void registerClause(Clause* clause, bool is_input_clause);
		void registerDerivation(int clause_id, SatResolution* res);
		// TODO: do we need to allow for duplicate insertion? see minisat_derivation.h in cvc3
		// don't really need to keep clauses, all you need to do is check that it's not the same.
		void finish(Clause* confl, Solver* solver);
		int getRootReason(Lit l, Solver* solver);
		void printDerivation(int clause_id, Solver* solver);
};

void Derivation::registerClause(Clause* clause, bool is_input_clause){

    if(d_clauses.find(clause->id()) == d_clauses.end()){
      // if not already registered
      d_clauses[clause->id()] = clause;
      if(is_input_clause){
        // if it's an input clause
        d_input_clauses.insert(clause->id());
      }
    }
}

void Derivation::registerDerivation(int clause_id, SatResolution* res){
  if(d_res_map.find(clause_id)== d_res_map.end()){
    d_res_map[clause_id] = res;
  }
}

int Derivation::getRootReason(Lit lit, Solver* solver){
  Debug("proof")<<"getRootReason for ";
  solver->printLit(lit);
  Clause* reason = solver->getReason(lit);
  // TODO: add asserts to check stuff
  if(reason==NULL){
    std::cout<<"Null Root Reason ";
    solver->printLit(lit);
    std::cout<<" \n";
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
    //Clause* new_reas = solver->getReason((*reason)[i]);
    int root_res = getRootReason((*reason)[i], solver);
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


void Derivation::finish(Clause* confl, Solver* solver){

  SatResolution* res = new SatResolution(confl->id());
  for (int i=0;i<(*confl).size();i++){
    Lit l = (*confl)[i];
    res->addStep(~l, getRootReason(~l, solver));

  }
  registerDerivation(confl->id(), res);

  // printing derivation for debugging
  printDerivation(confl->id(), solver);
}

// helper functions

void Derivation::printDerivation(int clause_id, Solver* solver){
  // TODO:: check that clause_id is in map
  SatResolution* res = d_res_map.find(clause_id)->second;

  RSteps step = res->getSteps();
  int parenCount = 0;
  for(unsigned i=0;i< res->getSteps().size();i++){

    std::cout<<"R ( ";
    solver->printLit(step[i].first);
    std::cout<<"| ";
    Clause* clause = d_clauses.find(step[i].second)->second;
    solver->printClause(*clause);
    parenCount++;
  }
  Clause* clause = d_clauses.find(clause_id)->second;
  std::cout<<"::";
  solver->printClause(*clause);
  for(int i=0;i<=parenCount;i++)
    std::cout<<" )";
}


}/* CVC4::prop::minisat namespace */
}/* CVC4::prop namespace */
}/* CVC4 namespace */    
    
    
    
#endif /* __CVC4__PROOF_H_ */

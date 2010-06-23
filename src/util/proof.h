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

class SatResolution {
public:
		typedef std::vector<std::pair <Lit, unsigned> >  RSteps;
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
  Clause* reason = solver->getReason(lit);
  // TODO: add asserts to check stuff

  // if implied by an unit clause return the unit clause
  if((*reason).size() == 1)
    return reason->id();
  std::hash_map<int, *Clause>::const_iterator iter;
  iter = d_unit_clauses.find(toInt(lit));
  if(iter != d_unit_clauses.end()){
    int a = iter->second;
    return 3;
  }

  SatResolution* res = new SatResolution(reason->id());

  for(int i=0; i<(*reason).size();i++){
    Clause* newreas = solver->getReason((*reason)[i]);
    res->addStep(~((*reason)[i]), getRootReason(newreas->id(), solver));
  }
  // add the literal as a unit clause
  std::vector<Lit> lits;
  lits.push_back(lit);
  Clause* unit = Clause_new(lits);
  d_unit_clauses[toInt(lit)] = unit;
  registerClause(unit, false);
  registerDerivation(unit->id(), res);

}

void Derivation::finish(Clause* confl, Solver* solver){

  SatResolution* res = new SatResolution(confl->id);
  for (int i=;i<(*confl).size();i++){
    Lit l = (*confl)[i];
    res->addStep(~l, getRootReason(~l, solver));
  }
}

}/* CVC4::prop::minisat namespace */
}/* CVC4::prop namespace */
}/* CVC4 namespace */    
    
    
    
#endif /* __CVC4__PROOF_H_ */

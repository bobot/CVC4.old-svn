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
		//typedef std::vector<int>  RSteps;
		unsigned d_start_clause;
		std::vector<std::pair <int, unsigned> > d_steps;

public:
		
		SatResolution(){};
		SatResolution (int clause_id): d_start_clause(clause_id){};
		
		void addStep(unsigned clause_id){
		  //std::vector<int> test;
		  //test.push_back(4);
		  std::pair<int, unsigned> p(3, clause_id);
		  std::cout<<p.first;
		  //std::cout<<d_steps.size();
		  d_steps.push_back(p);
		} 
		
		int getStart() const {
			return d_start_clause;			
		}
		
		//const RSteps& getSteps() const{
		//	return d_steps;
		//}
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
		// FIXME: why do i need them?
		std::hash_set <int> d_unit_clauses;		// the set of unit clauses
		std::hash_map <int, SatResolution*> d_res_map;	// a map from clause id's to the boolean resolution derivation of that respective clause
		
		Clause* d_emptyClause;
	// TODO: do you need to store clauses removed from derivation? 
	public:
		Derivation() : d_emptyClause(NULL) {};
		void registerClause(Clause* clause, bool is_input_clause);
		void registerDerivation(int clause_id, SatResolution* res);
		// TODO: do we need to allow for duplicate insertion? see minisat_derivation.h in cvc3
		// don't really need to keep clauses, all you need to do is check that it's not the same.
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


}/* CVC4::prop::minisat namespace */
}/* CVC4::prop namespace */
}/* CVC4 namespace */    
    
    
    
#endif /* __CVC4__PROOF_H_ */

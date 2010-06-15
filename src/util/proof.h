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

namespace std {
using namespace __gnu_cxx;
}

#ifndef __CVC4__PROOF_H_
#define __CVC4__PROOF_H_

namespace CVC4 {
namespace prop {
namespace minisat {

int id_count=0;

class SatResolution {
public:
		typedef std::vector<std::pair<Lit, int> > RSteps;
private:
		int d_start_clause;
		RSteps d_steps; 

public:
		
		SatResolution (int clause_id): d_start_clause(clause_id){};
		
		void addStep(Lit lit, int clause_id){
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
		std::hash_map<int, Clause*> d_clauses; 	// map from id's to clauses
		std::hash_set <int> d_input_clauses;		// the input clauses assumed true
		std::hash_set <int> d_unit_clauses;			// the set of unit clauses
		std::hash_map <int, SatResolution*> d_res_map;	// a map from clause id's to the boolean resolution derivation of that respective clause
		
		Clause* d_emptyClause;
	// TODO: do you need to store clauses removed from derivation? 
	public:
		Derivation() : d_emptyClause(NULL) {};
		bool isRegistered (Clause* clause);
		void registerClause(Clause* clause);
		int nextID() {} 
		// TODO: do we need to allow for duplicate insertion? see minisat_derivation.h in cvc3
		
		
		// assign ID when you register it
		// don't really need to keep clauses, all you need to do is check that it's not the same.
};

}/* CVC4::prop::minisat namespace */
}/* CVC4::prop namespace */
}/* CVC4 namespace */    
    
    
    
#endif /* __CVC4__PROOF_H_ */

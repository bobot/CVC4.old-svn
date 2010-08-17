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
#include <sstream>

#include <utility>
// do i need these includes?
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/core/Solver.h"
#include "lfsc_proof.h"

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

std::string intToStr(int i){
  std::stringstream ss;
  ss<<i;
  return ss.str();
}

class SatResolution {
public:

		unsigned d_start_clause;
		RSteps d_steps;

public:
		
		SatResolution(){};
		SatResolution (int clause_id): d_start_clause(clause_id){
		  Debug("proof:id")<<"NEW_RES:: start_id:"<<clause_id<<"\n";
		};
		
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
		//std::hash_map <int, Clause*> d_clauses; 	// map from id's to clauses
		std::hash_set <int> d_input_clauses;		// the input clauses assumed true
		std::hash_set <int> d_vars;                     // the set of variables that appear in the proof
		std::vector <Clause*> d_clauses;            // clause with id i will be on position i
		std::hash_map <int, Clause*> d_unit_clauses;		// the set of unit clauses, indexed by value of variable for easy searching (unit clauses are also stored in d_clauses)
		std::hash_map <int, SatResolution*> d_res_map;	// a map from clause id's to the boolean resolution derivation of that respective clause
		Solver* d_solver;
		Clause* d_emptyClause;
	// TODO: do you need to store clauses removed from derivation? 
	public:
		int static id_counter;
		Derivation(Solver* solver) : d_emptyClause(NULL), d_solver(solver) {};
		void registerClause(Clause* clause, bool is_input_clause);
		void registerDerivation(Clause* clause, SatResolution* res);
		// TODO: do we need to allow for duplicate insertion? see minisat_derivation.h in cvc3
		// don't really need to keep clauses, all you need to do is check that it's not the same.
		void finish(Clause* confl);
		int getRootReason(Lit l);
		void printDerivation(Clause* clause);
		void printLFSCProof(Clause* clause);
		int getId(Clause* clause);
		int new_id();
};

int Derivation::getId(Clause* cl){
  int id = -1;
  //store the variables
  for(unsigned i=0; i<cl->size(); i++){
    d_vars.insert(var((*cl)[i])+1);
  }

  for(unsigned i=0; i< d_clauses.size(); i++){
    Clause* cl_i = d_clauses[i];
    if(cl->size() == cl_i->size()){
      id = i;
      // compare clauses
      for(int j=0; j < cl->size(); j++)
        if (cl[j] != cl_i[j]){
          id = -1;
          break;
          }

      if(id!= -1)
        return id;
    }
 }
  return -1;
}

int Derivation::new_id(){
  return id_counter++;
}

void Derivation::registerClause(Clause* clause, bool is_input_clause){
    Debug("proof:id")<<"REG_CL:: ";

    int id = getId(clause);
    if(id == -1){
      // if not already registered
      d_clauses.push_back(clause);
      if(clause->size()==1){
        // if unit clause
        Lit lit = *clause[0];
        d_unit_clauses[toInt(lit)] = clause;
      }
      if(is_input_clause){
        // if it's an input clause
        // id will be the position it has been inserted at
        d_input_clauses.insert(d_clauses.size()-1);
      }
      Debug("proof:id")<<":: id:"<< d_clauses.size()-1<<"\n";
    }
    else
      Debug("proof:id")<<"already reg with id:"<<id<<"\n";

}

void Derivation::registerDerivation(Clause* clause, SatResolution* res){
  int clause_id = getId(clause);
  Debug("proof")<<"REG_DERIV :: id:"<<clause_id<<"\n";
  if(d_res_map.find(clause_id)== d_res_map.end()){
    d_res_map[clause_id] = res;
  }
  else{
   Debug("proof")<<"DERIV:: already registered \n";
  }
}


int Derivation::getRootReason(Lit lit){
  Debug("proof")<<"ROOT_REASON lit:";
  d_solver->printLit(lit);
  Debug("proof")<<"\n";

  Clause* reason = d_solver->getReason(lit);
  // TODO: add asserts to check stuff

  if(reason==NULL){
    /*
    Debug("proof")<<"Null Root Reason ";
    d_solver->printLit(lit);
    Debug("proof")<<" \n";
    return 0;
    */
    return toInt(lit);
  }

  Debug("proof")<<"reason: ";
  d_solver->printClause(*reason);
  Debug("proof")<<"\n";

  // if implied by an unit clause return the unit clause
  if((*reason).size() == 1)
    return getId(reason);

  // if the literal is already an unit clause then it has a computed reason

  std::hash_map<int, Clause*>::const_iterator iter;
  iter = d_unit_clauses.find(toInt(lit));
  if(iter != d_unit_clauses.end()){
    return getId(iter->second);
    }

  int resId = getId(reason);

  // if the reason is an input clause
  //if(d_input_clauses.find(resId)!= d_input_clauses.end())
  //  return resId;

  SatResolution* res = new SatResolution(resId);

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
  registerDerivation(unit, res);
  return toInt(lit);
}



void Derivation::new_finish(Clause* confl){
  LFSCProof confl_pf;
  if (confl.isLearned())
    // is learned
    confl_pf = addSatLemma(confl); // will return the variable name
  else
    // is input clause
    confl_pf = getInputVariable(confl);

  for(int i=0; i< confl->size(); i++){
    LFSCProof* var = LFSCProofSym::make(toString(confl[i]));
    LFSCProof* pf = LFSCProof::make_R(confl_pf, getProof(reason[confl[i]]), var);
    confl_pf = pf;
  }
}

LFSCProof* Derivation::addSatLemma(int clause_id){
  if(sat_lemmas.find(clause_id) != sat_lemmas.end()){
    sat_lemmas.push(make_pair(clause_id, getProof(clause_id)));
   }
  return LFSCProofSym::make("pf_"+intToStr(clause_id));
}

LFSCProof* Derivation::getProof(int clause_id){
  // constructs an LFSCProof of the clause
  if (isLemma(clause_id))
    return lemmaVariable(clause_id);
  // does it have to have a derivation?
  if(hasDeriv(clause_id)){
    return derivToLFSC(clause_id);
  }
  if(isInput(clause_id)){
    return getInputClauseVar(clause_id);
  }
}

LFSCProof* Derivation::derivToLFSC(int clause_id){
  // assert it has deriv
  SatResolution* res = getRes(clause_id);
  LFSCProof* pf1 = getProof(res->getStart());
  RSteps steps = res->getSteps();

  for(int i=0; i< steps.size(); i++){
    Lit var = steps[i].first;
    int c_id = steps[i].second;
    LFSCProof* pf2 = LFSCProof::make_R(pf1, getProof(c_id), LFSCSymb::make(var));
    pf1 = pf2;
  }
}

void Derivation::finish(Clause* confl){

  SatResolution* res = new SatResolution(getId(confl));
  for (int i=0;i<(*confl).size();i++){
    Lit l = (*confl)[i];
    res->addStep(~l, getRootReason(~l));

  }
  registerDerivation(confl, res);

  // printing derivation for debugging
  printDerivation(confl);
}

// helper functions

void Derivation::printDerivation(Clause* clause){
  int clause_id = getId(clause);
  Debug("proof")<<"Derivation clause_id="<<clause_id<<": ";
  d_solver->printClause(* d_clauses[clause_id]);
  SatResolution* res = d_res_map.find(clause_id)->second;

  RSteps step = res->getSteps();
  Clause* cl = d_clauses[res->getStart()];
  Debug("proof")<<"\n ";

  d_solver->printClause(*cl);
  for(unsigned i=0;i< res->getSteps().size();i++){
    Debug("proof")<<"| ";
    d_solver->printLit(step[i].first);
    Debug("proof")<<"| ";
    Clause* clause = d_clauses[step[i].second];
    d_solver->printClause(*clause);
  }
  Debug("proof")<<"\n";
}


//TODO: move to lfsc_proof.h

std::string printLFSCClause(Clause* clause){
  std::stringstream ss;
  std::stringstream end;
  for(int i=0; i< clause->size(); i++){
    ss<<"( clc ";
    if(sign((*clause)[i]))
      ss<<"(neg v"<<var((*clause)[i])+1<<") ";
    else
      ss<<"(pos v"<<var((*clause)[i])+1<<") ";
    end<<")";
  }
  ss<<" cln";
  return (ss.str()+end.str());
}

void Derivation::printLFSCProof(Clause* clause){
  std::stringstream os;
  std::stringstream end;
  LFSCProof::init();

  os<<"\n(check \n";
  end<<")";

  //printing variables

  for (std::hash_set<int>::iterator i = d_vars.begin(); i!=d_vars.end(); ++i){
    os<<"(% v"<<*i<<" var \n";
    end<<")";
   }

  int clause_id = getId(clause);
  SatResolution* res = d_res_map.find(clause_id)->second;

  RSteps step = res->getSteps();
  Clause* cl = d_clauses[res->getStart()];

  // printing start clause
  os<<"(% k"<<res->getStart()<<" (holds";
  os<<printLFSCClause(cl);
  os<<") \n";
  end<<")";

  // printing other clauses
  for(unsigned i=0;i< res->getSteps().size();i++){
    os<<"(% k"<<step[i].second<<" (holds ";
    os<<printLFSCClause(d_clauses[step[i].second]);
    os<<")\n";
    end<<")";
  }

  // printing type checking

  os<<"(: (holds ";
  os<<printLFSCClause(clause);
  os<<")";
  end<<")";

  LFSCProof* k1 = LFSCProofSym::make( "k"+intToStr(res->getStart()) );
  LFSCProof* v= NULL;
  LFSCProof* k2 = NULL;
  LFSCProof* k3 = NULL;
  for(unsigned i=0; i< res->getSteps().size(); i++){
    v = LFSCProofSym::make("v"+intToStr(var(step[i].first)+1));
    k2 = LFSCProofSym::make("k"+intToStr(step[i].second));
    k3 = LFSCProof::make_Q(k1, k2, v);
    k1 = k3;
  }

  std::cout<<os.str();
  k1->print(std::cout);
  std::cout<<end.str();

  }


}/* CVC4::prop::minisat namespace */
}/* CVC4::prop namespace */
}/* CVC4 namespace */    
    
    
    
#endif /* __CVC4__PROOF_H_ */

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
#include <map>

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
typedef int ClauseID;

std::string intToStr(int i){
  std::stringstream ss;
  ss<<i;
  return ss.str();
}

class SatResolution {
public:

		unsigned d_start_clause;
		RSteps d_steps;
		std::vector<bool> d_signs;

public:
		
		SatResolution(){};
		SatResolution (ClauseID clause_id): d_start_clause(clause_id){
		  Debug("proof:id")<<"NEW_RES:: start_id:"<<clause_id<<"\n";
		};
		
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



class Derivation {
	private:
		std::hash_set <ClauseID> d_input_clauses;		// the input clauses assumed true
		std::hash_set <int> d_vars;                     // the set of variables that appear in the proof
		std::map <ClauseID, SatResolution*> d_sat_lemmas;    // the resolution chains that will be outputed as sat lemmmas
		//std::set <Clause*> d_clauses;            // clause with id i will be on position i

		std::map <ClauseID, Clause*> d_id_clause;
		std::map <Clause*, ClauseID> d_clause_id;
		std::hash_map <ClauseID, Clause*> d_deleted;

		std::vector <ClauseID> d_lemma_stack;              // stack to print sat_lemmas in proper order
		std::hash_map <int, ClauseID > d_unit_clauses;		// the set of unit clauses, indexed by value of variable for easy searching (unit clauses are also stored in d_clauses)
		std::hash_map <ClauseID, SatResolution*> d_res_map;	// a map from clause id's to the boolean resolution derivation of that respective clause
		Solver* d_solver;
		Clause* d_empty_clause;
		ClauseID d_empty_clause_id;
	// TODO: do you need to store clauses removed from derivation? 
	public:
		ClauseID static id_counter;
		Derivation(Solver* solver) : d_solver(solver), d_empty_clause(NULL), d_empty_clause_id(0) {d_id_clause[0]=(d_empty_clause); };
		void registerClause(Clause* clause, bool is_input_clause);
		void registerDerivation(Clause* clause, SatResolution* res);
		// TODO: do we need to allow for duplicate insertion? see minisat_derivation.h in cvc3
		// don't really need to keep clauses, all you need to do is check that it's not the same.
		LFSCProof* getInputVariable(ClauseID confl_id);
		SatResolution* getRes(ClauseID clause_id);
		bool isLearned(ClauseID clause_id);
		bool isEq(Clause* cl1, Clause* cl2);
		bool isSatLemma(ClauseID clause_id);
		void addSatLemma(ClauseID clause_id);
		LFSCProof* satLemmaVariable(ClauseID clause_id);
		LFSCProof* derivToLFSC(ClauseID clause_id);
		LFSCProof* getProof(ClauseID clause_id);
		void finish(Clause* confl);
		void lemmaProof(ClauseID clause_id);
		ClauseID getLitReason(Lit lit);
		void printDerivation(ClauseID clause_id);
		void printDerivation(Clause* clause);
		void printLFSCProof(Clause* clause);
		LFSCProof* addLFSCSatLemmas(LFSCProof* pf);
		void printAllClauses();
		ClauseID getUnitId(Lit l);
		ClauseID getId(Clause* clause);
		ClauseID new_id();
		void markDeleted(Clause* clause);
		void dummy();
};

void Derivation::markDeleted(Clause* clause){
  //Assert(d_clause_id.find(clause)!= d_clause_id.end());
  if(d_clause_id.find(clause)!= d_clause_id.end()){
    int id;
    id = d_clause_id[clause];
    d_deleted[id] = clause;
    d_id_clause.erase(id);
    d_clause_id.erase(clause);
  }

}

bool Derivation::isEq(Clause* cl1, Clause* cl2){
  Assert(cl1!= NULL && cl2!=NULL);
  if (cl1->size() != cl2->size())
    return false;

  for(int i = 0; i< cl1->size(); i++)
    if((*cl1)[i]!= (*cl2)[i])
      return false;

  return true;
}

// returns -1 if the clause has not been registered

ClauseID Derivation::getId(Clause* cl){
  if(cl == d_empty_clause)
    return d_empty_clause_id;

  //FIXME: move this - store the variables
  for(int i=0; i<cl->size(); i++){
    d_vars.insert(var((*cl)[i])+1);
  }

  // some unit clauses might be only stored in d_unit_clauses
  if(cl->size()==1){
    if(d_unit_clauses.end()!= d_unit_clauses.find(toInt((*cl)[0])))
      return d_unit_clauses[toInt((*cl)[0])];
  }

  if(d_clause_id.find(cl)!= d_clause_id.end())
    return d_clause_id[cl];
  return -1;
}

ClauseID Derivation::new_id(){
  return id_counter++;
}

void Derivation::registerClause(Clause* clause, bool is_input_clause){
    Assert(clause != NULL);
    Debug("proof:id")<<"REG_CL:: ";

    ClauseID id = getId(clause);
    if(id == -1){
      // if not already registered
      id = new_id();
      d_clause_id[clause] = id;
      d_id_clause[id] = clause;


      if(clause->size()==1){
        // if unit clause
        Lit lit = *clause[0];
        d_unit_clauses[toInt(lit)] = id;
      }
      if(is_input_clause){
        // if it's an input clause
        // id will be the position it has been inserted at
        d_input_clauses.insert(id);
      }
      Debug("proof:id")<<":: id:"<< id<<"\n";
    }
    else{
      Debug("proof:id")<<"already reg with id:"<<id<<"\n";
    }

}

void Derivation::registerDerivation(Clause* clause, SatResolution* res){
  Assert(clause!= NULL);
  ClauseID clause_id = getId(clause);
  // invariant: always register the clause first

  Assert(clause_id != -1);

  Debug("proof")<<"REG_DERIV :: id:"<<clause_id<<"\n";
  if(d_res_map.find(clause_id)== d_res_map.end()){
    d_res_map[clause_id] = res;
    Assert(d_res_map.find(clause_id)!= d_res_map.end());
    // because minisat does not store the reason if the reason is a unit clause
    if(clause->size()==1)
      d_unit_clauses[toInt((*clause)[0])] = clause_id;
  }
  else{
   Debug("proof")<<"DERIV:: already registered \n";
  }
}


// helper methods

LFSCProof* Derivation::getInputVariable(ClauseID confl_id){
  return LFSCProofSym::make("P"+intToStr(confl_id));
}

bool Derivation::isLearned(ClauseID clause_id){
  // if it's not an input clause, it has to have been learned
  return (d_input_clauses.find(clause_id) == d_input_clauses.end());
}

void Derivation::addSatLemma(ClauseID clause_id){
  SatResolution* res = getRes(clause_id);
  Assert(res!= NULL);
  d_sat_lemmas[clause_id] = res;
  return;
}

SatResolution* Derivation::getRes(ClauseID clause_id){
  if(d_res_map.find(clause_id)== d_res_map.end())
    return NULL;
  else
    return (d_res_map.find(clause_id))->second;
}
ClauseID Derivation::getUnitId(Lit lit){
  Assert(d_unit_clauses.find(toInt(lit))!=d_unit_clauses.end());
  ClauseID id = d_unit_clauses[toInt(lit)];
  return id;
}

LFSCProof* Derivation::derivToLFSC(ClauseID clause_id){
  // TODO: cache getVar and getLam and something else
  SatResolution* res = getRes(clause_id);
  Assert(res!= NULL);
  LFSCProof* pf1 = getProof(res->getStart());
  RSteps steps = res->getSteps();

  for(unsigned i=0; i< steps.size(); i++){
    int v = var(steps[i].first);
    ClauseID c_id = steps[i].second;
    // checking the second clause, hence invert Q and R
    LFSCProof* pf2;
    if(res->getSign(i))
      pf2 = LFSCProof::make_R(pf1, getProof(c_id), LFSCProofSym::make("v"+intToStr(v+1)));
    else
      pf2 = LFSCProof::make_Q(pf1, getProof(c_id), LFSCProofSym::make("v"+intToStr(v+1)));
    pf1 = pf2;
  }
  return pf1;
}

bool Derivation::isSatLemma(ClauseID clause_id){
  return (d_sat_lemmas.find(clause_id)!= d_sat_lemmas.end());
}

LFSCProof* Derivation::satLemmaVariable(ClauseID clause_id){
  return LFSCProofSym::make("m"+intToStr(clause_id));
}


void Derivation::lemmaProof(ClauseID clause_id){
  if(!isSatLemma(clause_id)){
    printDerivation(clause_id);
    SatResolution* res = getRes(clause_id);
    Assert(res!= NULL);

    RSteps steps = res->getSteps();
    ClauseID start_id = res->getStart();
    if(!isSatLemma(start_id) && isLearned(start_id))
      lemmaProof(start_id);

    for(unsigned i=0; i< steps.size();i++){
      ClauseID c_id = steps[i].second;
      int v = var(steps[i].first);
      if(!isSatLemma(c_id) && isLearned(c_id)){
        lemmaProof(c_id);
      }
    }
    d_sat_lemmas[clause_id] = res;
  }
}

ClauseID Derivation::getLitReason(Lit lit){
  if(var(lit) == 27)
    dummy();
  if(d_unit_clauses.find(toInt(~lit)) != d_unit_clauses.end()){
    // check if reason already computed
    ClauseID id = d_unit_clauses[toInt(~lit)];
    if(!isSatLemma(id))
      lemmaProof(id);
    return d_unit_clauses[toInt(~lit)];
  }

  Clause* cl = d_solver->getReason(lit);
  if(cl == NULL){
    // must be implied by a unit clause
    Assert(d_unit_clauses.find(toInt(~lit))!= d_unit_clauses.end());
    lemmaProof(d_unit_clauses[toInt(~lit)]);
    return d_unit_clauses[toInt(~lit)];
  }

  ClauseID clause_id = getId(cl);
  SatResolution* res = new SatResolution(clause_id);
  for(int i= 1; i < cl->size(); i++){
    Lit lit = (*cl)[i];
    // flips the literal so that the Q/R invariant works
    res->addStep(lit, getLitReason(lit), !(sign(lit)));
  }

  ClauseID id = new_id();
  d_unit_clauses[toInt(~lit)] = id;
  d_res_map[id] = res;
  return id;

}

LFSCProof* Derivation::getProof(ClauseID clause_id){
  // constructs an LFSCProof of the clause
  if (isSatLemma(clause_id))
    return satLemmaVariable(clause_id);
  // does it have to have a derivation?
  // check if it's an unit clause

  if(getRes(clause_id)!=NULL){
    return derivToLFSC(clause_id);
  }
  if(!isLearned(clause_id)){
    // then has to be input clause
    return getInputVariable(clause_id);
  }
}

void Derivation::finish(Clause* confl){
  Assert(confl!= NULL);

  ClauseID confl_id = getId(confl);
  SatResolution* res = new SatResolution(confl_id);

  if (isLearned(confl_id)){
    // is learned
    addSatLemma(confl_id);
  }

  for(int i=0; i< confl->size(); i++){
    Lit lit = (*confl)[i];
    ClauseID res_id = getLitReason(lit);
    Assert(getRes(res_id)!=NULL);
    res->addStep(lit, res_id, !sign(lit));
  }
  d_res_map[d_empty_clause_id] = res;
}




// helper functions

void Derivation::printAllClauses(){
  Debug("proof")<<"d_clauses \n";
  for(std::map<ClauseID, Clause*>::iterator it = d_id_clause.begin(); it!= d_id_clause.end();it++){
    Debug("proof")<<"id: "<<(*it).first<<" = ";
    if((*it).second!= 0){
      Clause* cl = (*it).second;
      d_solver->printClause(*cl);
      Debug("proof")<<"\n";
    }
  }
/*
  Debug("proof")<<"d_res_map \n";
  for(std::hash_map<ClauseID, SatResolution*>::iterator it = d_res_map.begin(); it!= d_res_map.end();it++){
    Debug("proof")<<"id: "<<(*it).first<<" = ";
    if((*it).first == NULL)
      Debug("proof")<<" NULL ";
  }
*/
  Debug("proof")<<"d_unit_clauses \n";
  for(std::hash_map<int, ClauseID>::iterator i = d_unit_clauses.begin(); i!=d_unit_clauses.end();i++){
    int lit = (*i).first;
    ClauseID id = (*i).second;
    Debug("proof")<<"var "<<var(toLit(lit))+1 <<"id: "<<id <<" = ";
    Clause* cl = d_id_clause[id];
    d_solver->printClause(*cl);
    Debug("proof")<<"\n";
  }

}

void Derivation::printDerivation(Clause* clause){
  ClauseID clause_id = getId(clause);
  printDerivation(clause_id);
}

void Derivation::dummy(){
  Debug("proof")<<"adasdA";
}

void Derivation::printDerivation(ClauseID clause_id){
  Assert(clause_id >= 0);
  Debug("proof")<<"Derivation clause_id="<<clause_id<<": ";
  if(clause_id == 0)
    Debug("proof")<<" empty ";
  else{
    if(d_id_clause.find(clause_id)!=d_id_clause.end())
      d_solver->printClause(* d_id_clause[clause_id]);
    else if(d_deleted.find(clause_id)==d_deleted.end()){
      Debug("proof")<<" unit? ";
    }
    else
      Debug("proof")<<" del"<<clause_id;
  }

  SatResolution* res = getRes(clause_id);
  Assert(res!= NULL);

  RSteps step = res->getSteps();

  if(d_id_clause.find(res->getStart())!=d_id_clause.end()){
    Clause* cl = d_id_clause[res->getStart()];
    Debug("proof")<<"\n ";
    d_solver->printClause(*cl);
  }
  else
    Debug("proof")<<" del"<<res->getStart();

  for(unsigned i=0;i< res->getSteps().size();i++){
    Debug("proof")<<"| ";
    d_solver->printLit(step[i].first);
    Debug("proof")<<"| ";
    if(d_deleted.find(step[i].second)!= d_deleted.end()){
      Debug("proof")<<" del"<<step[i].second;
    }
    else if(d_id_clause.find(step[i].second)!= d_id_clause.end()){
      Clause* clause = d_id_clause[step[i].second];
      d_solver->printClause(*clause);
    }
    else{// must be an unit clause, hence must be the literal we are resolving on
      Assert(step[i].second == d_unit_clauses[toInt(~(step[i].first))]);
      d_solver->printLit(~step[i].first);
    }
  }
  Debug("proof")<<"\n";
}




//TODO: move to lfsc_proof.h

std::string printLFSCClause(Clause* clause){
  std::stringstream ss;
  std::stringstream end;
  if(clause == NULL)
    return "cln";
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


LFSCProof* Derivation::addLFSCSatLemmas(LFSCProof* pf){
  // the iterator traverses the set in order of the keys which corresponds to the order in which the clauses were registered
  // to ensure that the sat lemmas are printed in the appropriate order
  LFSCProof* u1, * u2;
  LFSCProofSym* lam_var = LFSCProofSym::make("done");
  u2 = LFSCProofLam::make(lam_var, lam_var);
  pf = LFSCProof::make_satlem(pf, u2);

  for(std::map<ClauseID, SatResolution*>::reverse_iterator i =  d_sat_lemmas.rbegin(); i!=d_sat_lemmas.rend();i++){
    u1 = derivToLFSC((*i).first); // make sure it doesn't call addSatlemma anymore
    lam_var = LFSCProofSym::make("m"+intToStr((*i).first));
    u2 = LFSCProofLam::make(lam_var, pf);
    pf = LFSCProof::make_satlem(u1, u2);
  }
  return pf;
}

void Derivation::printLFSCProof(Clause* confl){
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

   // printing input clauses
   for(std::hash_set<ClauseID>::iterator i=d_input_clauses.begin();i!= d_input_clauses.end();i++){
     os<<"(% P"<<*i<<" (holds ";
     os<<printLFSCClause(d_id_clause[*i]);
     os<<")\n";
     end<<")";
   }
   printAllClauses();
   Debug("proof")<<" Final Conflict ";
   d_solver->printClause(*confl);
   Debug("proof")<<"\n";
   finish(confl);

   printDerivation(d_empty_clause_id);



   os<<"(: (holds cln)";
   end<<")";
   std::cout<<os.str();
   //int confl_id = getId(confl);
   //Assert(confl_id > 0 && confl_id < d_clauses.size());
   Assert(getRes(d_empty_clause_id)!=NULL);
   LFSCProof* pf = derivToLFSC(d_empty_clause_id);
   pf = addLFSCSatLemmas(pf);
   pf->print(std::cout);
   std::cout<<end.str()<<";";
}




}/* CVC4::prop::minisat namespace */
}/* CVC4::prop namespace */
}/* CVC4 namespace */    
    
    
    
#endif /* __CVC4__PROOF_H_ */

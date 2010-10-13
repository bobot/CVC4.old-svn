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
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/core/Solver.h"
#include "lfsc_proof.h"

using namespace Minisat;
namespace std {
using namespace __gnu_cxx;
}

#ifndef __CVC4__PROOF_H_
#define __CVC4__PROOF_H_

namespace CVC4 {

namespace prop{


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
private:
  std::hash_set <ClauseID> d_input_clauses;              // the input clauses assumed true
  std::hash_set <int> d_vars;                            // the set of variables that appear in the proof
  std::map <ClauseID, SatResolution*> d_sat_lemmas;      // the resolution chains that will be printed as sat lemmas

  std::map <ClauseID, Clause*> d_id_clause;             // map from clause id to clauses
  std::map <Clause*, ClauseID> d_clause_id;             // map from clauses to clause id

  std::hash_map <ClauseID, Clause*> d_deleted;          // stores the clauses deleted from the minisat database

  std::vector <ClauseID> d_lemma_stack;              // stack to print sat_lemmas in proper order
  std::hash_map <int, ClauseID > d_unit_clauses;          // the set of unit clauses, indexed by value of variable for easy searching
  std::hash_map <ClauseID, int> d_unit_ids;               // reverse map of d_unit_clauses

  std::hash_map <ClauseID, SatResolution*> d_res_map;     // a map from clause id's to the boolean resolution derivation of that respective clause
  Solver* d_solver;
  Clause* d_empty_clause;
  ClauseID d_empty_clause_id;
public:
  ClauseID static id_counter;
  Derivation(Solver* solver) : d_solver(solver), d_empty_clause(NULL), d_empty_clause_id(0)
    {d_id_clause[0]=(d_empty_clause); };

  /** registration methods**/

  // register unit clause corresponding to lit
  // special case because minisat does not store unit learned conflicts
  ClauseID registerClause(Lit lit);
  ClauseID registerClause(Clause* clause, bool is_input_clause);

  void registerResolution(Clause* clause, SatResolution* res);
  void registerResolution(ClauseID clause_id, SatResolution* res);

  /** helper methods **/

  bool isUnit(Clause* cl);
  bool isUnit(Lit lit);
  bool isUnit(ClauseID clause_id);
  bool isStoredClause(Clause* cl);

  bool isRegistered(Clause* cl);
  bool isRegistered(ClauseID cl_id);
  bool hasResolution(ClauseID cl_id);

  bool isLearned(ClauseID clause_id);
  bool isSatLemma(ClauseID clause_id);

  ClauseID newId();
  ClauseID getId(Clause* clause);
  ClauseID getUnitId(Clause* cl);
  ClauseID getUnitId(Lit l);
  ClauseID getClauseId(Clause* cl);
  Lit getUnit(ClauseID cl_id);
  SatResolution* getResolution(ClauseID clause_id);

  void markDeleted(Clause* clause);


  /** methods for putting the proof together **/

  void addSatLemma(ClauseID clause_id);
  void lemmaProof(ClauseID clause_id);
  ClauseID getLitReason(Lit lit);
  void finish(Clause* confl);

  /** constructing lfsc proof **/

  LFSCProof* getInputVariable(ClauseID confl_id);
  LFSCProof* satLemmaVariable(ClauseID clause_id);
  LFSCProof* derivToLFSC(ClauseID clause_id);
  LFSCProof* getProof(ClauseID clause_id);
  LFSCProof* addLFSCSatLemmas(LFSCProof* pf);

  /** debugging methods **/

   /** resolution checking methods **/
  bool checkDerivation(ClauseID clause_id);
  bool compareClauses(Clause* cl1, Clause* cl2);
  Clause* resolve(Clause* cl1, Clause* cl2, Lit lit);
  Clause* resolve(Clause* cl1, Lit cl2, Lit lit);


};

/***** helper methods *****/

/** id-clause methods **/

bool Derivation::isUnit(Clause* cl){
  Assert(cl!= NULL);
  Assert(cl->size() == 1);
  return d_unit_clauses.end()!= d_unit_clauses.find(toInt((*cl)[0]));
}

bool Derivation::isUnit(Lit lit){
  return d_unit_clauses.end()!= d_unit_clauses.find(toInt(lit));
}

bool Derivation::isUnit(ClauseID cl_id){
  return d_unit_ids.end()!=d_unit_ids.find(cl_id);
}

bool Derivation::isStoredClause(Clause* cl){
  return d_clause_id.find(cl)!= d_clause_id.end();
}

bool Derivation::isRegistered(Clause* cl){
  return isStoredClause(cl) || isUnit(cl);
}

bool Derivation::isRegistered(ClauseID cl_id){
  return d_id_clause.find(cl_id)!= d_id_clause.end();
}

bool Derivation::hasResolution(ClauseID cl_id){
  return d_res_map.find(cl_id)!=d_res_map.end();
}

ClauseID Derivation::getUnitId(Clause* cl){
  Assert(isUnit(cl));
  return d_unit_clauses[toInt((*cl)[0])];
}

ClauseID Derivation::getUnitId(Lit lit){
  Assert(isUnit(lit));
  return d_unit_clauses[toInt(lit)];
}

Lit Derivation::getUnit(ClauseID cl_id){
 Assert(isUnit(cl_id));
 return toLit(d_unit_ids[cl_id]);
}

ClauseID Derivation::getClauseId(Clause* cl){
  Assert(isStoredClause(cl));
  return d_clause_id[cl];
}

// returns -1 if the clause has not been registered
ClauseID Derivation::getId(Clause* cl){
   if(cl == d_empty_clause)
    return d_empty_clause_id;
   //FIXME: maybe check if all unit clauses are in d_unit so then merge isUnit and getUnit?
  if(isUnit(cl))
      return getUnitId(cl);

  if(isStoredClause(cl))
    return d_clause_id[cl];
  //FIXME: define a constant for this
  return -1;
}

SatResolution* Derivation::getResolution(ClauseID clause_id){
  Assert(hasResolution(clause_id));
  return (d_res_map.find(clause_id))->second;
}

/** **/


ClauseID Derivation::newId(){
  return id_counter++;
}

void Derivation::markDeleted(Clause* clause){
  if(isStoredClause(clause)){
    ClauseID id;
    id = d_clause_id[clause];
    d_deleted[id] = clause;
    d_id_clause.erase(id);
    d_clause_id.erase(clause);
  }

}


/**** registration methods *****/

/** clause registration **/

// register the unit clause containing the literal
// note that the clause is not created it only exists as a mapping
ClauseID Derivation::registerClause(Lit lit){
  if(isUnit(lit))
    // if already registered return current id
    return getUnitId(lit);

  ClauseID id = newId();
  d_unit_clauses[toInt(lit)]= id;
  d_unit_ids[id] = toInt(lit);
  return id;
}

ClauseID Derivation::registerClause(Clause* clause, bool is_input_clause){
    Assert(clause != NULL);
    Assert(clause->size() > 1); // minisat does not store unit clauses

    ClauseID id = getId(clause);
    if(id == -1){
      // if not already registered
      id = newId();
      d_clause_id[clause] = id;
      d_id_clause[id] = clause;

      if(is_input_clause)
        d_input_clauses.insert(id);
    }
    return id;
}

/** resolution registration **/

void Derivation::registerResolution(ClauseID clause_id, SatResolution* res){
  Assert(clause_id != -1);
  Debug("proof")<<"Derivation::registerDerivation::clause_id::"<<clause_id<<"\n";
  if(!hasResolution(clause_id)){
    d_res_map[clause_id] = res;
  }
  else{
   Debug("proof")<<"DERIV:: already registered \n";
  }
  //Assert(checkDerivation(clause_id));
}

void Derivation::registerResolution(Clause* clause, SatResolution* res){
  Assert(clause!= NULL);
  ClauseID clause_id = getId(clause);

  Assert(clause_id != -1);
  Debug("proof")<<"Derivation::registerResolution::clause_id::"<<clause_id<<"\n";
  if(!hasResolution(clause_id))
    d_res_map[clause_id] = res;
  else
   Debug("proof")<<"Derivation::registerResolution::already registered clause_id::"<<clause_id<<"\n";

  //Assert(checkDerivation(clause_id));
}

/** helper methods for proof construction **/

bool Derivation::isLearned(ClauseID clause_id){
  return (d_input_clauses.find(clause_id) == d_input_clauses.end());
}

bool Derivation::isSatLemma(ClauseID clause_id){
  return (d_sat_lemmas.find(clause_id)!= d_sat_lemmas.end());
}

/**** constructing the proof *****/

void Derivation::addSatLemma(ClauseID clause_id){
  SatResolution* res = getResolution(clause_id);
  d_sat_lemmas[clause_id] = res;
  return;
}


void Derivation::lemmaProof(ClauseID clause_id){
  if(!isSatLemma(clause_id)){
    SatResolution* res = getResolution(clause_id);
    //printDerivation(clause_id);

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
  if(isUnit(~lit)){
    // check if reason already computed
    ClauseID id = getUnitId(~lit);
    if(!isSatLemma(id))
      lemmaProof(id);
    return id;
  }

  //FIXME:!
  Clause* cl = &(d_solver->ca)[d_solver->reason(var(lit))];

  // if it was NULL then should have been derived by an unit clause
  // and isUnit would have been true

  Assert(cl!=NULL);
  ClauseID clause_id = getId(cl);
  SatResolution* res = new SatResolution(clause_id);
  for(int i= 1; i < cl->size(); i++){
    Lit lit = (*cl)[i];
    // flips the literal so that the Q/R invariant works
    res->addStep(lit, getLitReason(lit), !(sign(lit)));
  }

  if(!isSatLemma(clause_id)&& isLearned(clause_id))
    lemmaProof(clause_id);

  ClauseID id = newId();
  d_unit_clauses[toInt(~lit)] = id;
  d_res_map[id] = res;
  return id;
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
    Assert(hasResolution(res_id));
    res->addStep(lit, res_id, !sign(lit));
  }
  d_res_map[d_empty_clause_id] = res;
}


/***** debugging printing *****/

/*
void Derivation::printDerivation(Clause* clause){
  ClauseID clause_id = getId(clause);
  printDerivation(clause_id);
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

  SatResolution* res = getResolution(clause_id);

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
*/

/*
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

// register the unit clause that is the reason for the literal
// note that the clause is not created it only exists as a mapping

ClauseID Derivation::registerClause(Lit lit){
  if(d_unit_clauses.find(toInt(~lit))!= d_unit_clauses.end()){
    // already registered unit clause
    return d_unit_clauses[toInt(~lit)];
  }

  ClauseID id = new_id();
  d_unit_clauses[toInt(~lit)]= id;
  Assert(d_unit_clauses.find(toInt(~lit))!= d_unit_clauses.end());
  return id;
}

ClauseID Derivation::registerClause(Clause* clause, bool is_input_clause){
    Assert(clause != NULL);
    if(clause->size() == 0)
         Debug("proof")<<"clause of size 0 \n";

    Assert(clause->size() > 0);
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
    return id;

}


void Derivation::registerDerivation(ClauseID clause_id, SatResolution* res){
  Assert(clause_id != -1);

  Debug("proof")<<"REG_DERIV :: id:"<<clause_id<<"\n";
  if(d_res_map.find(clause_id)== d_res_map.end()){
    d_res_map[clause_id] = res;
    Assert(d_res_map.find(clause_id)!= d_res_map.end());

  }
  else{
   Debug("proof")<<"DERIV:: already registered \n";
  }

  //Assert(checkDerivation(clause_id));
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
  //Assert(checkDerivation(clause_id));
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
    SatResolution* res = getRes(clause_id);
    Assert(res!= NULL);
    printDerivation(clause_id);

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
  if(d_unit_clauses.find(toInt(~lit)) != d_unit_clauses.end()){
    // check if reason already computed
    ClauseID id = d_unit_clauses[toInt(~lit)];
    if(!isSatLemma(id))
      lemmaProof(id);
    return d_unit_clauses[toInt(~lit)];
  }

  CRef cl = d_solver->reason(var(lit));

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
  if(!isSatLemma(clause_id)&& isLearned(clause_id))
    lemmaProof(clause_id);


  ClauseID id = new_id();
  d_unit_clauses[toInt(~lit)] = id;
  d_res_map[id] = res;
  return id;

}

LFSCProof* Derivation::getProof(ClauseID clause_id){
  // constructs an LFSCProof of the clause
  // does it have to have a derivation?
  // check if it's an unit clause

 if(!isLearned(clause_id))
    // then has to be input clause
    return getInputVariable(clause_id);


 if (isSatLemma(clause_id))
   return satLemmaVariable(clause_id);

 if(getRes(clause_id)!=NULL)
   return derivToLFSC(clause_id);

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


  Debug("proof")<<"d_unit_clauses \n";
  for(std::hash_map<int, ClauseID>::iterator i = d_unit_clauses.begin(); i!=d_unit_clauses.end();i++){
    int lit = (*i).first;
    ClauseID id = (*i).second;
    Debug("proof")<<"var "<<var(toLit(lit))+1 <<"id: "<<id <<" = ";
    //if(d_id_clause.find(id)!= d_id_clause.end()){
    //  Clause* cl = d_id_clause[id];
     // d_solver->printClause(*cl);
   // }

    Debug("proof")<<"\n";
  }

}

bool Derivation::compareClauses(Clause* cl1, Clause* cl2){
  Assert(cl1 != NULL && cl2 != NULL);
  if(cl1->size()!= cl2->size())
    return false;

  bool eq = false;
  for (int i=0; i<cl1->size();i++){
    Lit l = (*cl1)[i];
    eq = false;
    for(int j=0;j< cl2->size();j++)
      if(l == (*cl2)[j])
        eq = true;
  }

  return eq;
}

Clause* Derivation::resolve(Clause* cl1, Clause* cl2, Lit lit){
  vec<Lit> lits;

  for(int i=0; i< cl1->size(); i++){
    if(var((*cl1)[i])!=var(lit))
     lits.push((*cl1)[i]);
  }

  for(int i=0; i< cl2->size(); i++){
    bool found = false;

    for(int j=0;j < lits.size(); j++)
      if(var(lits[j]) == var((*cl2)[i])){
        found = true;
        break;
      }

    if(!found && var((*cl2)[i])!= var(lit))
      lits.push((*cl2)[i]);
  }
  return Clause_new(lits);
}

Clause* Derivation::resolve(Clause* cl1, Lit l2, Lit lit){
  Assert(var(l2) == var(lit));

  vec<Lit> lits;
  for (int i=0; i< cl1->size();i++)
    if(var((*cl1)[i])!= var(lit))
      lits.push((*cl1)[i]);

  return Clause_new(lits);
}

bool Derivation::checkDerivation(ClauseID clause_id){
  if(clause_id == d_empty_clause_id)
    return true;

  Debug("proof")<<"Checking Derivation \n";
  printDerivation(clause_id);

  SatResolution* res = getRes(clause_id);
  Assert(res!= NULL);

  ClauseID start_id = res->getStart();
  Assert(d_id_clause.find(start_id)!=d_id_clause.end());
  Clause* start = d_id_clause[start_id];

  RSteps steps = res->getSteps();
  for(int i=0;i <steps.size(); i++){
    if(d_id_clause.find(steps[i].second)!= d_id_clause.end()){
      start = resolve(start,d_id_clause[steps[i].second],  steps[i].first);
      Debug("proof")<<"CHECK:: ";
      d_solver->printClause(*start);
      Debug("proof")<<"\n";
    }
    else{
      Assert(d_unit_clauses.find(toInt(~(steps[i].first)))!= d_unit_clauses.end());
      start = resolve(start, steps[i].first,  steps[i].first);
    }

  }

  if(d_id_clause.find(clause_id)!= d_id_clause.end()){
    Clause* concl = d_id_clause[clause_id];
    return compareClauses(concl, start);
  }

  // should be an unit clause then
  Assert(start->size() == 1);
  Lit lit = (*start)[0];
  Lit lit2 = ~lit;
  //ClauseID id_lit1 = getUnitId(lit);
  ClauseID id_lit2 = getUnitId(lit2);
  return clause_id == id_lit2;

}

void Derivation::printDerivation(Clause* clause){
  ClauseID clause_id = getId(clause);
  printDerivation(clause_id);
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

void Derivation::printDerivation2(ClauseID clause_id){
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

    if(isSatLemma(step[i].second))
      Debug("proof")<<"::lem";
    else if(!isLearned(step[i].second)){
      Debug("proof")<<"::inp";
    }
    else{
      Debug("proof")<<"::(";
      printDerivation2(step[i].second);
      Debug("proof")<<")";
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
   std::cout<<"\n \n";
   pf = addLFSCSatLemmas(pf);
   pf->print(std::cout);
   std::cout<<end.str()<<";";
}*/


}/* prop namespace */
}/* CVC4 namespace */
#endif

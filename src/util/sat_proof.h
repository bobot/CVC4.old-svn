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
  SatResolution* d_current;
  Solver* d_solver;
  Clause* d_empty_clause;
  ClauseID d_empty_clause_id;

public:
  ClauseID static id_counter;
  Derivation(Solver* solver) : d_solver(solver), d_empty_clause(NULL), d_empty_clause_id(0),d_current(NULL)
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
  void storeVars(Clause* clause);


  /** solver interface **/
  /*
  TODO: make all other private

  void startResolution(Clause* confl);
  void addStep(Lit l, Clause* cl);
  void endResolution();
  */

  /** constructing the proof **/


  void addSatLemma(ClauseID clause_id);
  void lemmaProof(ClauseID clause_id);
  ClauseID getLitReason(Lit lit);
  void finish(Clause* confl);

  /** constructing LFSC proof **/
  LFSCProof* getInputVariable(ClauseID confl_id);
  LFSCProof* satLemmaVariable(ClauseID clause_id);
  LFSCProof* derivToLFSC(ClauseID clause_id);
  LFSCProof* getProof(ClauseID clause_id);
  LFSCProof* addLFSCSatLemmas(LFSCProof* pf);

  /** debugging **/
  void printLit(Lit l);
  void printClause(Clause* cl);
  void printAllClauses();
  void printResolution(Clause* cl);
  void printResolution(ClauseID cl_id);

   /** resolution checking **/
  bool checkDerivation(ClauseID clause_id);
  bool compareClauses(Clause* cl1, Clause* cl2);
  Clause* resolve(Clause* cl1, Clause* cl2, Lit lit);
  Clause* resolve(Clause* cl1, Lit cl2, Lit lit);

  void printLFSCProof(Clause* final_confl);

};

/***** helper methods *****/

/** id-clause methods **/

bool Derivation::isUnit(Clause* cl){
  Assert(cl!= NULL);
  if (cl->size()>1)
    return false;
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

void Derivation::storeVars(Clause* clause){
  Assert(clause!=NULL);
  for(int i=0; i<clause->size(); i++)
    d_vars.insert(var(*clause[i])+1);
}


/**** registration methods *****/

/** clause registration **/

// register the unit clause containing the literal
// note that the clause is not created it only exists as a mapping
ClauseID Derivation::registerClause(Lit lit){
  if(isUnit(~lit))
    // if already registered return current id
    return getUnitId(~lit);

  ClauseID id = newId();
  d_unit_clauses[toInt(~lit)]= id;
  d_unit_ids[id] = toInt(~lit);
  return id;
}

ClauseID Derivation::registerClause(Clause* clause, bool is_input_clause){
    Assert(clause != NULL);
    Assert(clause->size() > 1); // minisat does not store unit clauses

    ClauseID id = getId(clause);
    if(id == -1){
      //FIXME: better way to do this?
      storeVars(clause);
      // if not already registered
      id = newId();
      d_clause_id[clause] = id;
      d_id_clause[id] = clause;
      if(clause->size()==1){
        d_unit_clauses[toInt(~(*clause[0]))] = id;
        d_unit_ids[id] = toInt(~(*clause[0]));
      }
      if(is_input_clause)
        d_input_clauses.insert(id);
    }
    return id;
}

/** resolution registration **/

void Derivation::registerResolution(ClauseID clause_id, SatResolution* res){
  Assert(clause_id != -1);
  Debug("proof")<<"Derivation::registerResolution::clause_id::"<<clause_id<<"\n";
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
    //printResolution(clause_id);
    //Debug("proof")<<"lemmaProof::id "<<clause_id<<"\n";
    RSteps steps = res->getSteps();
    ClauseID start_id = res->getStart();
    if(!isSatLemma(start_id) && isLearned(start_id))
      lemmaProof(start_id);

    for(unsigned i=0; i< steps.size();i++){
      ClauseID c_id = steps[i].second;
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

  ClauseID id = registerClause(lit);
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

inline void Derivation::printLit(Lit l)
{
    Debug("proof")<<(sign(l) ? "-" : "")<<var(l)+1<<" ";
}


inline void Derivation::printClause(Clause* c)
{
  Assert(c!= NULL);
  for (int i = 0; i < c->size(); i++){
        printLit((*c)[i]);
        Debug("proof")<<" ";
    }
    Debug("proof")<<"\n";
}


void Derivation::printAllClauses(){
  Debug("proof")<<"d_clauses \n";
  for(std::map<ClauseID, Clause*>::iterator it = d_id_clause.begin(); it!= d_id_clause.end();it++){
    Debug("proof")<<"id: "<<(*it).first<<" = ";
    if((*it).second!= 0){
      Clause* cl = (*it).second;
      printClause(cl);
    }
  }

  Debug("proof")<<"d_unit_clauses \n";
  for(std::hash_map<int, ClauseID>::iterator i = d_unit_clauses.begin(); i!=d_unit_clauses.end();i++){
    int lit = (*i).first;
    ClauseID id = (*i).second;
    Debug("proof")<<"var "<<var(toLit(lit))+1 <<"id: "<<id <<" = ";
    Debug("proof")<<"\n";
  }

}

void Derivation::printResolution(Clause* clause){
  ClauseID clause_id = getId(clause);
  printResolution(clause_id);
}


void Derivation::printResolution(ClauseID clause_id){
  Assert(clause_id >= 0);
  Debug("proof")<<"Derivation clause_id="<<clause_id<<": ";
  if(clause_id == 0)
    Debug("proof")<<" empty ";
  else{
    if(d_id_clause.find(clause_id)!=d_id_clause.end())
      printClause(d_id_clause[clause_id]);
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
    printClause(cl);
  }
  else
    Debug("proof")<<" del"<<res->getStart();

  for(unsigned i=0;i< res->getSteps().size();i++){
    Debug("proof")<<"| ";
    printLit(step[i].first);
    Debug("proof")<<"| ";
    if(d_deleted.find(step[i].second)!= d_deleted.end()){
      Debug("proof")<<" del"<<step[i].second;
    }
    else if(d_id_clause.find(step[i].second)!= d_id_clause.end()){
      Clause* clause = d_id_clause[step[i].second];
      printClause(clause);
    }
    else{// must be an unit clause, hence must be the literal we are resolving on
      Assert(step[i].second == getUnitId(~(step[i].first)));
      printLit(~step[i].first);
    }
  }
  Debug("proof")<<"\n";
}

/***** LFSC Proof *****/

/** helper methods **/

LFSCProof* Derivation::getInputVariable(ClauseID confl_id){
  return LFSCProofSym::make("P"+intToStr(confl_id));
}

LFSCProof* Derivation::satLemmaVariable(ClauseID clause_id){
  return LFSCProofSym::make("m"+intToStr(clause_id));
}

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

/** constructing the lfsc proof **/

LFSCProof* Derivation::getProof(ClauseID clause_id){
  // constructs an LFSCProof of the clause
  // does it have to have a derivation?
  // check if it's an unit clause

 if(!isLearned(clause_id))
    // then has to be input clause
    return getInputVariable(clause_id);


 if (isSatLemma(clause_id))
   return satLemmaVariable(clause_id);

 Assert(hasResolution(clause_id));
 return derivToLFSC(clause_id);

}


LFSCProof* Derivation::derivToLFSC(ClauseID clause_id){
  // TODO: cache getVar and getLam and something else
  SatResolution* res = getResolution(clause_id);
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
   printClause(confl);
   Debug("proof")<<"\n";
   finish(confl);

   printResolution(d_empty_clause_id);

   os<<"(: (holds cln)";
   end<<")";
   std::cout<<os.str();
   Assert(hasResolution(d_empty_clause_id));
   LFSCProof* pf = derivToLFSC(d_empty_clause_id);
   std::cout<<"\n \n";
   pf = addLFSCSatLemmas(pf);
   pf->print(std::cout);
   std::cout<<end.str()<<";";
}

}/* prop namespace */
}/* CVC4 namespace */
#endif

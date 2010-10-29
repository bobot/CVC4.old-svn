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

#ifndef Sat_proof_inline_h
#define Sat_proof_inline_h

#include <vector>
#include <ext/hash_map>
#include <ext/hash_set>
#include <iostream>
#include <sstream>
#include <map>

#include <utility>
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/core/Solver.h"
#include "util/Assert.h"
#include "lfsc_proof.h"
#include "util/sat_proof.h"

//FIXME:: namespace in header

using namespace Minisat;
namespace Minisat{
  class Solver;
}

namespace std {
using namespace __gnu_cxx;
}



namespace CVC4 {

namespace prop{

/*
 * Interface to Solver
 */

void Derivation::updateId(CRef old_ref, CRef new_ref){
  /*
   * called in relocAll in minisat during garbage collection
   */
  if(isRegistered(old_ref)){
    ClauseID id = getId(old_ref);
    d_clause_id_tmp[new_ref] = id;
    d_id_clause_tmp[id] = new_ref;
  }
}

void Derivation::finishUpdateId(){
  // copy the things that might have gotten deleted because there were no more references to them
  for (std::map<ClauseID, CRef>::iterator i = d_id_clause.begin(); i!=d_id_clause.end(); ++i)
    if(d_id_clause_tmp.find((*i).first) == d_id_clause_tmp.end()){
      d_deleted.insert((*i).first);
      //Debug("proof")<<"new-del"<<(*i).first<<" ";
    }
  //Debug("proof")<<"\n";
  d_clause_id = d_clause_id_tmp;
  d_id_clause = d_id_clause_tmp;
  d_clause_id_tmp.clear();
  d_id_clause_tmp.clear();
}

void Derivation::newResolution(CRef cref, bool is_problem_clause= false){
  // adds a new resolution on the resolution stack
  // starting with clause cref
  ClauseID id = registerClause(cref, is_problem_clause);
  Debug("proof")<<"newResolution "<<id<<"\n";
  printClause(cref);
  SatResolution* res = new SatResolution(id);
  d_current.push_back(res);
}

void Derivation::newResolution(Lit lit){
  ClauseID id = registerClause(lit);
  SatResolution* res = new SatResolution(id);
  d_current.push_back(res);
}

void Derivation::addResStep(Lit l, CRef cl, bool sign){
  Assert(!d_current.empty());

  ClauseID id = registerClause(cl, false);
  int n = d_current.size();
  (d_current[n-1])->addStep(l, id, sign);
}


void Derivation::addResStep(Lit l, Lit l2, bool sign){
  Assert(!d_current.empty());

  ClauseID id = registerClause(l2);
  int n = d_current.size();
  (d_current[n-1])->addStep(l, id, sign);
}

void Derivation::endResolution(CRef cl){
  Assert(!d_current.empty());
  SatResolution* res = d_current[d_current.size()-1];
  ClauseID id = registerClause(cl);
  registerResolution(id, res);
  d_current.pop_back();
}


void Derivation::endResolution(Lit lit){
  Assert(!d_current.empty());
  SatResolution* res = d_current[d_current.size()-1];
  ClauseID id = registerClause(lit);
  registerResolution(id, res);

  printResolution(id);

  d_current.pop_back();
}

/*
 * construct a resolution that proves (q)
 * returns the ID of the unit clause (q)
 */

ClauseID Derivation::traceReason(Lit q){

  Assert(d_solver->level(var(q))==0);

  if(getReason(var(q))==CRef_Undef || (isUnit(q) && hasResolution(getUnitId(q))) ) {
    // must be an unit clause
    Debug("proof")<<"traceReason:: q is unit:";
    printLit(q);
    Debug("proof")<<"\n";
    return getUnitId(q);
  }

  else {
     // must be propagated at 0 and must recursively trace the reasons
     printLit(q);
     Debug("proof")<<"traceReason:: propagated at 0 \n";
     printClause(getReason(var(q)));

     ClauseID unit_id = registerClause(q);

     ClauseID id_r = registerClause(getReason(var(q)), false);
     Debug("proof")<<"tarceReason::id_r="<<id_r<<"\n";
     // create new resolution proving ~q
     SatResolution* res_unit = new SatResolution(id_r);
/*
     vec<char> seen2;
     seen2.growTo(d_solver->seen.size());
     for (int j = 0;j < d_solver->seen.size(); j++)
       seen2[j] = 0;
*/
     vec<Lit> stack;
     stack.push(q);
     //seen2[var(q)] = 1;

     do{
       Lit l = stack.last();
       stack.pop();

       Clause* reason = &cl(getReason(var(l)));
       ClauseID r_id = registerClause(getReason(var(l)), false);
       if(l!=q)
         res_unit->addStep(l, r_id, !sign(l));

       for (int i = 1; i< reason->size();i++){
         Lit li = (*reason)[i];
         if(getReason(var(li))== CRef_Undef) {
           // must be an unit clause
           Debug("proof")<<"traceReason:: li unit clause level"<<d_solver->level(var(li))<<" ";
           printLit(li);
           Debug("proof")<<"\n";
           Assert(isUnit(~li));
           res_unit->addStep(li, getUnitId(~li), !sign(li));
         }
         else {
           // add to stack to resolve
           stack.push(li);
         }
       }
     }
     while(stack.size()>0);

     registerResolution(unit_id, res_unit);
     return unit_id;
  }

}

/***** helper methods *****/

/** id-clause methods **/

std::string Derivation::intToStr(int i){
  std::stringstream ss;
  ss<<i;
  return ss.str();
}

bool Derivation::isUnit(CRef cref){
  Assert(cref!= CRef_Undef);
  Clause& clause = cl(cref);
  if (clause.size()>1)
    return false;
  Assert(clause.size()>0);
  return d_unit_clauses.end()!= d_unit_clauses.find(toInt(clause[0]));
}

bool Derivation::isUnit(Lit lit){
  return d_unit_clauses.end()!= d_unit_clauses.find(toInt(lit));
}

bool Derivation::isUnit(ClauseID cl_id){
  return d_unit_ids.end()!=d_unit_ids.find(cl_id);
}

bool Derivation::isStoredClause(CRef cl){
  return d_clause_id.find(cl)!= d_clause_id.end();
}

bool Derivation::isRegistered(CRef cl){
  return isStoredClause(cl) || isUnit(cl);
}

bool Derivation::isRegistered(ClauseID cl_id){
  return d_id_clause.find(cl_id)!= d_id_clause.end();
}

bool Derivation::hasResolution(ClauseID cl_id){
  return (d_res_map.find(cl_id)!=d_res_map.end());
}

ClauseID Derivation::getUnitId(CRef cref){
  Assert(isUnit(cref));
  return d_unit_clauses[toInt((cl(cref))[0])];
}

ClauseID Derivation::getUnitId(Lit lit){
  Assert(isUnit(lit));
  return d_unit_clauses[toInt(lit)];
}

Lit Derivation::getUnit(ClauseID cl_id){
 Assert(isUnit(cl_id));
 return toLit(d_unit_ids[cl_id]);
}

ClauseID Derivation::getClauseId(CRef cl){
  Assert(isStoredClause(cl));
  return d_clause_id[cl];
}

// returns -1 if the clause has not been registered
ClauseID Derivation::getId(CRef cl){

  if(isStoredClause(cl))
    return d_clause_id[cl];

  if(isUnit(cl))
      return getUnitId(cl);

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

void Derivation::markDeleted(CRef clause){
  if(isStoredClause(clause)){
    //Debug("proof")<<"("<<clause<<")";
    ClauseID id;
    id = d_clause_id[clause];
    d_deleted.insert(id);
    d_id_clause.erase(id);
    d_clause_id.erase(clause);
    //Debug("proof")<<"deleted::"<<id<<" ";
  }

}

//TODO: print actual variable names
void Derivation::storeVars(CRef cref){
  Assert(cref!=CRef_Undef);
  Clause& clause = cl(cref);
  for(int i=0; i<clause.size(); i++)
    d_vars.insert(var(clause[i])+1);
}

/*
 * Access to the solver
 */

Clause& Derivation::cl(CRef cref){
  Assert(cref!= CRef_Undef);

  Clause& c = d_solver->ca[cref];

  return c;
}



CRef Derivation::getReason(int v){
  return d_solver->reason(v);
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

ClauseID Derivation::registerClause(CRef cref, bool is_input_clause){
    Clause& clause = cl(cref);
    Assert(clause.size() > 1); // minisat does not store unit clauses

    ClauseID id = getId(cref);
    if(id == -1){
      //FIXME: better way to do this?
      storeVars(cref);
      // if not already registered
      id = newId();
      d_clause_id[cref] = id;
      d_id_clause[id] = cref;
      if(clause.size()==1){
        d_unit_clauses[toInt(~(clause[0]))] = id;
        d_unit_ids[id] = toInt(~(clause[0]));
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

  //checkResolution(clause_id);
  Assert(checkResolution(clause_id));
}

void Derivation::registerResolution(CRef clause, SatResolution* res){
  Assert(clause!= CRef_Undef);
  ClauseID clause_id = getId(clause);

  Assert(clause_id != -1);
  Debug("proof")<<"Derivation::registerResolution::clause_id::"<<clause_id<<"\n";
  if(!hasResolution(clause_id))
    d_res_map[clause_id] = res;
  else
   Debug("proof")<<"Derivation::registerResolution::already registered clause_id::"<<clause_id<<"\n";

  //checkResolution(clause_id);
  Assert(checkResolution(clause_id));
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
  if(!isSatLemma(clause_id) && isLearned(clause_id)){
    SatResolution* res = getResolution(clause_id);
    printResolution(clause_id);
    Debug("proof")<<"lemmaProof::id "<<clause_id<<"\n";
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

  CRef cref = getReason(var(lit));

  // if it was NULL then should have been derived by an unit clause
  // and isUnit would have been true

  Assert(cref!=CRef_Undef);
  ClauseID clause_id = getId(cref);
  SatResolution* res = new SatResolution(clause_id);
  Clause& clause = cl(cref);
  for(int i= 1; i < clause.size(); i++){
    Lit lit = clause[i];
    // flips the literal so that the Q/R invariant works
    res->addStep(lit, getLitReason(lit), !(sign(lit)));
  }

  if(!isSatLemma(clause_id)&& isLearned(clause_id))
    lemmaProof(clause_id);

  ClauseID id = registerClause(~lit);
  d_res_map[id] = res;
  return id;
}

void Derivation::finish(CRef confl){
  Assert(confl!= CRef_Undef);

  ClauseID confl_id = getId(confl);
  SatResolution* res = new SatResolution(confl_id);

  if (isLearned(confl_id)){
    // is learned
    addSatLemma(confl_id);
  }
  Clause& conflc = cl(confl);
  for(int i=0; i< conflc.size(); i++){
    Lit lit = conflc[i];
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


inline void Derivation::printClause(CRef cref)
{
  Assert(cref != CRef_Undef);
  Clause& c = cl(cref);
  Debug("proof")<<"("<<cref<<")";
  for (int i = 0; i < c.size(); i++){
        printLit(c[i]);
        Debug("proof")<<" ";
    }
    Debug("proof")<<"\n";
}

inline void Derivation::printIdClause(ClauseID id){
  if(id == d_empty_clause_id)
    Debug("proof")<<" empty ";
  else
  if(d_deleted.count(id))
    Debug("proof")<<"del"<<id<<"\n ";
  else
  if(isUnit(id)){
    Debug("proof")<<"( unit"<<id<<":";
    printLit(getUnit(id));
    Debug("proof")<<") \n";
    }
  else{
    Assert(d_id_clause.find(id)!=d_id_clause.end());
    printClause(d_id_clause[id]);
    }
}

void Derivation::printAllClauses(){
  Debug("proof")<<"d_clauses \n";
  for(std::map<ClauseID, CRef>::iterator it = d_id_clause.begin(); it!= d_id_clause.end();it++){
    Debug("proof")<<"id: "<<(*it).first<<" = ";
    if((*it).first!= 0){
      CRef cl = (*it).second;
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

  Debug("proof")<<"d_deleted \n";
  for(std::hash_set<ClauseID>::iterator i = d_deleted.begin(); i!=d_deleted.end();i++){
    Debug("proof")<<"del id"<<(*i)<<"\n";
  }

}

void Derivation::printResolution(CRef clause){
  ClauseID clause_id = getId(clause);
  printResolution(clause_id);
}


void Derivation::printResolution(ClauseID clause_id){
  Assert(clause_id >= 0);
  Debug("proof")<<"Derivation clause_id="<<clause_id<<": ";
  printIdClause(clause_id);
  Debug("proof")<<":\n";
  SatResolution* res = getResolution(clause_id);

  RSteps step = res->getSteps();
  ClauseID start_id = res->getStart();

  printIdClause(start_id);

  for(unsigned i=0;i< res->getSteps().size();i++){
    Debug("proof")<<"| ";
    printLit(step[i].first);
    Debug("proof")<<"| ";
    printIdClause(step[i].second);
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

std::string Derivation::printLFSCClause(CRef cref){
  std::stringstream ss;
  std::stringstream end;
  if(cref == CRef_Undef)
    return "cln";
  Clause& clause = cl(cref);
  for(int i=0; i< clause.size(); i++){
    ss<<"( clc ";
    if(sign(clause[i]))
      ss<<"(neg v"<<var(clause[i])+1<<") ";
    else
      ss<<"(pos v"<<var(clause[i])+1<<") ";
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
  //Debug("proof")<<"derivToLFSC "<<clause_id<<" ";
  SatResolution* res = getResolution(clause_id);
  LFSCProof* pf1 = getProof(res->getStart());
  //Debug("proof")<<"derivToLFSC::"<<clause_id;
  Assert(clause_id > res->getStart() || clause_id == 0 );

  RSteps steps = res->getSteps();

  for(unsigned i=0; i< steps.size(); i++){
    int v = var(steps[i].first);
    ClauseID c_id = steps[i].second;
    // checking the second clause, hence invert Q and R
    Assert( clause_id > c_id || clause_id == 0);

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

void Derivation::printLFSCProof(CRef confl){
   std::stringstream os;
   std::stringstream end;
   LFSCProof::init();


   //printAllClauses();
   /*
   for (std::hash_map<int, SatResolution*>::iterator i = d_res_map.begin(); i!=d_res_map.end(); ++i){
     printResolution((*i).first);
    }
   */
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


/*
 * Debugging derivation checking
 */


void Derivation::resolve(vec<Lit> &clause, ClauseID id, Lit lit){
  vec<Lit> result;
  bool s = true;
  Lit l1, l2;
  if(s) {
    l1 = sign(lit)?~lit:lit;
    l2 = sign(lit)?lit:~lit;
  }
  else {
    l1 = sign(lit)?lit:~lit;
    l2 = sign(lit)?~lit:lit;
  }

  if(isUnit(id)){
    Lit unit = getUnit(id);
    for(int i=0; i<clause.size(); i++){
      if(var(clause[i])!=var(lit))
       result.push(clause[i]);
    }
    result.copyTo(clause);
    return;
  }
  else{
    Clause& clause2 = cl(d_id_clause[id]);
    for(int i=0; i<clause.size(); i++){
      // would also need to check that it has a resolution, presumably it has one
      if(var(clause[i])!=var(lit) )
       result.push(clause[i]);
    }
    for(int i=0; i<clause2.size(); i++)
      if(var(clause2[i])!= var(lit) && !hasLit(clause2[i], result))
        result.push(clause2[i]);
    result.copyTo(clause);
    return;
  }

}

bool Derivation::hasLit(Lit l, vec<Lit>& cl){
  for(int i=0; i<cl.size(); i++)
    if(var(cl[i])==var(l))
      return true;

  return false;
}

bool Derivation::compareClauses(ClauseID clause_id, vec<Lit>& cl2){

  if(!isUnit(clause_id)){
    Assert(d_id_clause.find(clause_id)!=d_id_clause.end());
    Clause& cl1 = cl(d_id_clause[clause_id]);
    if(cl1.size()!=cl2.size())
      return false;

    for(int i=0; i< cl1.size(); i++){
       if(!hasLit(cl1[i], cl2))
         return false;
    }
    return true;
  }
  else{
    Lit l = getUnit(clause_id);
    if(cl2.size()==1)
      return l == cl2[0];

    return false;
  }
}

bool Derivation::checkResolution(ClauseID clause_id){
  //Debug("proof:cr")<<"checkResolution "<<clause_id<<"\n";
  SatResolution* res = getResolution(clause_id);
  //printResolution(clause_id);

  ClauseID start_id = res->getStart();
  Clause& start_cl = cl(d_id_clause[start_id]);
  vec<Lit> start;
  for(int i=0;i<start_cl.size();i++)
    start.push(start_cl[i]);

  RSteps steps = res->getSteps();
  for(unsigned i=0; i < steps.size(); i++){
    ClauseID id = steps[i].second;
    Lit l = steps[i].first;
    resolve(start, id, l);
  }

  /*
  Debug("proof")<<"result ";
  for(int i=0;i<start.size();i++)
    printLit(start[i]);
  Debug("proof")<<"\n";
  */
  if(isUnit(clause_id)){
   Lit unit = getUnit(clause_id);
   if(start.size()==1 && start[0]==unit)
     return true;
   else
     return false;
  }

  return compareClauses(clause_id, start);
}


}/* prop namespace */
}/* CVC4 namespace */
#endif

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
#include "util/sat_proof.h"


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

/**
 * Updates the ClauseIDs when Minisat does garbage collection
 * and clauses are reallocated in memory
 */

void Derivation::updateId(Minisat::CRef old_ref, Minisat::CRef new_ref){
  if(isRegistered(old_ref)){
    ClauseID id = getId(old_ref);
    d_clause_id_tmp[new_ref] = id;
    d_id_clause_tmp[id] = new_ref;
  }
}

/**
 * Deletes the temporary maps used in updating IDs
 *
 */

void Derivation::finishUpdateId(){
  // copy the things that might have gotten deleted because there were no more references to them
  for (std::map<ClauseID, Minisat::CRef>::iterator i = d_id_clause.begin(); i!=d_id_clause.end(); ++i)
    if(d_id_clause_tmp.find((*i).first) == d_id_clause_tmp.end()){
      d_deleted.insert((*i).first);
    }
  d_clause_id = d_clause_id_tmp;
  d_id_clause = d_id_clause_tmp;
  d_clause_id_tmp.clear();
  d_id_clause_tmp.clear();
}

/**
 * Creates a new resolution starting from cref
 * must only be called when d_current == NULL
 */

void Derivation::newResolution(Minisat::CRef cref, bool is_problem_clause){
  ClauseID id = registerClause(cref, is_problem_clause);
  Debug("proof")<<"newResolution "<<id<<"\n";
  Assert(d_current == NULL);
  d_current = new SatResolution(id);

}

void Derivation::newResolution(Minisat::Lit lit){
  ClauseID id = registerClause(lit);
  Assert(d_current == NULL);
  d_current = new SatResolution(id);
}

/**
 * Adds a step to the current resolution
 */
void Derivation::addResStep(Minisat::Lit l, Minisat::CRef cl, bool sign){
  Assert(d_current != NULL);
  ClauseID id = registerClause(cl, false);
  d_current->addStep(l, id, sign);
}

void Derivation::addResStep(Minisat::Lit l, Minisat::Lit l2, bool sign){
  Assert(d_current!=NULL);
  ClauseID id = registerClause(l2);
  d_current->addStep(l, id, sign);
}

void Derivation::addResStepId(Minisat::Lit l, ClauseID id, bool sign){
  Assert(d_current != NULL);
  d_current->addStep(l, id, sign);
}

/**
 * Stores the resolution proving cl in the resolution map
 * and rested d_current
 */
void Derivation::endResolution(Minisat::CRef cl){
  Assert(d_current!=NULL);
  ClauseID id = registerClause(cl);
  registerResolution(id, d_current);
  d_current = NULL;
}

void Derivation::endResolution(Minisat::Lit lit){
  Assert(d_current!=NULL);
  ClauseID id = registerClause(lit);
  registerResolution(id, d_current);
  d_current = NULL;
}

/**
 * Depth first search starting from removed literal p
 * used in conflict clause minimization. Because it does
 * not matter which order we resolve unit clauses we can
 * resolve them only once in the end
 * IMPORTANT: alters seen in Solver.cc
 */
void Derivation::orderDFS(Minisat::Lit p, Minisat::vec<Minisat::Lit> & ordered, Minisat::vec<Minisat::Lit> & units){
  //constants used as bit masks
  char inconfl = 1, removable = 2, processed = 4;

  // check if already seen
  if(d_solver->seen[var(p)]&processed)
    return;
  // mark it as seen
  if(d_solver->seen[var(p)]== 0)
    // make sure Minisat will reset seen[var(p)] to 0 when clearing seen[]
    d_solver->analyze_toclear.push(p);

  d_solver->seen[var(p)]|= processed;
  Assert(getReason(var(p))!= Minisat::CRef_Undef);

  Minisat::Clause& clause = getClause(getReason(var(p)));
  for(int i=1; i < clause.size(); i++){
    if(getReason(var(clause[i]))== Minisat::CRef_Undef && (d_solver->seen[var(clause[i])]&inconfl) == 0){
      // if has no reason and not in original conflict
      // must be deduced by a unit clause
      if(! (d_solver->seen[var(clause[i])]&processed)) {
        units.push(clause[i]);

        if(d_solver->seen[var(clause[i])]==0)
          d_solver->analyze_toclear.push(clause[i]);
        // mark it as processed by this method
        d_solver->seen[var(clause[i])]|=processed;
      }
    }
    else
    if((d_solver->seen[var(clause[i])] & removable) || d_solver->level(var(clause[i]))==0 )
      orderDFS(clause[i], ordered, units);
  }

  if((d_solver->seen[var(p)] & removable) || d_solver->level(var(p)) == 0)
    // if it is removable or propagated at level 0 we can push it on the stack
    // because all of the literals it added will be removed after it
    ordered.push(p);

}

/**
 * Adds lit to the eliminated lit stack to resolve it out
 */
void Derivation::addEliminatedLit(Minisat::Lit lit){
  eliminated_lit.push(lit);
}

/**
 * Resolve out the literals that have been removed from out_learnt
 * during conflict clause minimization (works only for ccmin_mode == 2)
 */
void Derivation::resolveMinimizedCC(){
  Assert(d_current!=NULL);
  if(eliminated_lit.size() > 0){
    Minisat::vec<Minisat::Lit> order;
    Minisat::vec<Minisat::Lit> units;
    int k;
    // dfs starting from each eliminated literal
    // the literals get added to order and units
    // in the order they have to be resolved on
    for(k = 0; k< eliminated_lit.size(); k++) {
      orderDFS(eliminated_lit[k], order, units);
    }

    // resolve out literals from unminimized learned clause
    for(k = order.size()-1; k>=0; k--){
      Minisat::CRef cref = getReason(var(order[k]));
      ClauseID cl_id;
      if(cref == Minisat::CRef_Undef) {
        cl_id = registerClause(~(order[k]));
      }
      else {
        cl_id = registerClause(cref);
      }
      d_current->addStep(order[k], cl_id, !(sign(order[k])));

    }

    // resolve out the unit clauses (may be units that appear in the original
    // learned clause, or added by resolving out other eliminated literals)
    for(k = 0; k< units.size(); k++){
      ClauseID cl_id = registerClause(~(units[k]));
      d_current->addStep(units[k], cl_id, !(sign(units[k])));
    }

  }
  eliminated_lit.clear();
}

/***** helper methods *****/

/** id-clause methods **/



bool Derivation::isUnit(Minisat::CRef cref){
  Assert(cref!= Minisat::CRef_Undef);
  Minisat::Clause& clause = getClause(cref);
  if (clause.size()>1)
    return false;
  Assert(clause.size()>0);
  return d_unit_clauses.end()!= d_unit_clauses.find(toInt(clause[0]));
}

bool Derivation::isUnit(Minisat::Lit lit){
  return d_unit_clauses.end()!= d_unit_clauses.find(toInt(lit));
}

bool Derivation::isUnit(ClauseID cl_id){
  return d_unit_ids.end()!=d_unit_ids.find(cl_id);
}

bool Derivation::isStoredClause(Minisat::CRef cl){
  return d_clause_id.find(cl)!= d_clause_id.end();
}

bool Derivation::isRegistered(Minisat::CRef cl){
  return isStoredClause(cl) || isUnit(cl);
}

bool Derivation::isRegistered(ClauseID cl_id){
  return d_id_clause.find(cl_id)!= d_id_clause.end();
}

bool Derivation::hasResolution(ClauseID cl_id){
  return (d_res_map.find(cl_id)!=d_res_map.end());
}

ClauseID Derivation::getUnitId(Minisat::CRef cref){
  Assert(isUnit(cref));
  return d_unit_clauses[toInt((getClause(cref))[0])];
}

ClauseID Derivation::getUnitId(Minisat::Lit lit){
  Assert(isUnit(lit));
  return d_unit_clauses[toInt(lit)];
}

Minisat::Lit Derivation::getUnit(ClauseID cl_id){
 Assert(isUnit(cl_id));
 return Minisat::toLit(d_unit_ids[cl_id]);
}

ClauseID Derivation::getClauseId(Minisat::CRef cl){
  Assert(isStoredClause(cl));
  return d_clause_id[cl];
}

/**
 * Returns the ClauseID corresponding to cl if it has been registered
 * and -1 otherwise
 */

ClauseID Derivation::getId(Minisat::CRef cl){

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


ClauseID Derivation::newId(){
  return id_counter++;
}

/**
 * Stores the IDs of deleted clauses and removes the clauses
 * from the id to Minisat::CRef maps
 */
void Derivation::markDeleted(Minisat::CRef clause){
  if(isStoredClause(clause)){
    ClauseID id;
    id = d_clause_id[clause];
    d_deleted.insert(id);
    d_id_clause.erase(id);
    d_clause_id.erase(clause);
  }

}

//TODO: print actual variable names
void Derivation::storeVars(Minisat::CRef cref){
  Assert(cref!=Minisat::CRef_Undef);
  Minisat::Clause& clause = getClause(cref);
  for(int i=0; i<clause.size(); i++)
    d_vars.insert(var(clause[i])+1);
}

/**
 * Returns the actual close pointed to by cref
 */

Minisat::Clause& Derivation::getClause(Minisat::CRef cref){
  Assert(cref!= Minisat::CRef_Undef);
  Assert(d_solver!= NULL);

  Minisat::Clause& c = d_solver->ca[cref];

  return c;
}

/**
 * Returns the reason for a variable by calling
 * Minisat's reason()
 * IMPORTANT: theory reasons are computed lazily and
 * calling getReason may cause a new clause to be created
 * and thus garbage collection
 */

Minisat::CRef Derivation::getReason(int v){
  return d_solver->reason(v);
}

/**** registration methods *****/

/** clause registration **/

/**
 * register the unit clause containing the literal
 * note that the clause is not created it only exists
 * as a mapping, because Minisat does not store unit clauses
 */

ClauseID Derivation::registerClause(Minisat::Lit lit,  bool is_input) {
  if(isUnit(lit))
    // if already registered return current id
    return getUnitId(lit);

  d_vars.insert(var(lit)+1);
  ClauseID id = newId();
  d_unit_clauses[toInt(lit)]= id;
  d_unit_ids[id] = toInt(lit);
  if(is_input) {
      d_input_clauses.insert(id);
  }
  return id;
}

ClauseID Derivation::registerClause(Minisat::CRef cref, bool is_input_clause) {
    Minisat::Clause& clause = getClause(cref);
    Assert(clause.size() > 1); // minisat does not store unit clauses

    ClauseID id = getId(cref);
    if(id == -1){
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
  Debug("proof:regres")<<"Derivation::registerResolution::clause_id::"<<clause_id<<"\n";
  Assert(!hasResolution(clause_id));

  d_res_map[clause_id] = res;

  //Assert(checkResolution(clause_id));
}

void Derivation::registerResolution(Minisat::CRef clause, SatResolution* res){
  Assert(clause!= Minisat::CRef_Undef);
  ClauseID clause_id = getId(clause);

  Assert(clause_id != -1);
  Debug("proof:regres")<<"Derivation::registerResolution::clause_id::"<<clause_id<<"\n";
  Assert(!hasResolution(clause_id));

  d_res_map[clause_id] = res;

  //Assert(checkResolution(clause_id));

}

/** helper methods for proof construction **/

bool Derivation::isLearned(ClauseID clause_id){
  return (d_input_clauses.find(clause_id) == d_input_clauses.end());
}

bool Derivation::isSatLemma(ClauseID clause_id){
  return d_sat_lemmas.count(clause_id) != 0;
}

/**** constructing the proof *****/

void Derivation::addSatLemma(ClauseID clause_id){
  d_sat_lemmas.insert(clause_id);
  return;
}

/**
 * Recursively traces the resolution proving the clause and
 * marks all the clauses needed to prove it, that must be
 * printed as sat lemmas (we might not need all the stored
 * resolutions)
 */

void Derivation::lemmaProof(ClauseID clause_id){
  if(!isLearned(clause_id)){
    d_needed_input.insert(clause_id);
    return;
  }
  if(!isSatLemma(clause_id)){
    SatResolution* res = getResolution(clause_id);
    Debug("proof")<<"lemmaProof::id "<<clause_id<<"\n";

    std::vector<ResStep> steps = res->getSteps();
    ClauseID start_id = res->getStart();
    lemmaProof(start_id);

    for(unsigned i=0; i< steps.size();i++){
      ClauseID c_id = steps[i].id;
      lemmaProof(c_id);
      }
    d_sat_lemmas.insert(clause_id);
  }

}


/**
 * Recursively constructs the resolution that proves
 * the unit clause ~lit
 */

ClauseID Derivation::getLitReason(Minisat::Lit lit){
  if(isUnit(~lit)){
    // check if reason already computed
    ClauseID id = getUnitId(~lit);
    return id;
  }

  Minisat::CRef cref = getReason(var(lit));

  // if it was CRef_Undef then should have been derived by an unit clause
  // and isUnit would have been true

  Assert(cref!=Minisat::CRef_Undef);
  ClauseID clause_id = getId(cref);
  SatResolution* res = new SatResolution(clause_id);
  Minisat::Clause& clause = getClause(cref);
  for(int i= 1; i < clause.size(); i++){
    Minisat::Lit lit = clause[i];
    // flips the literal so that the Q/R invariant works
    res->addStep(lit, getLitReason(lit), !(sign(lit)));
  }

  ClauseID id = registerClause(~lit);
  d_res_map[id] = res;
  return id;
}


/**
 * Constructs the final resolution proving the empty clause
 * by resolving out all of the literals in the final conflict
 */

void Derivation::finish(Minisat::CRef confl){
  Assert(confl!= Minisat::CRef_Undef);

  ClauseID confl_id = getId(confl);
  SatResolution* res = new SatResolution(confl_id);

  if (isLearned(confl_id)){
    lemmaProof(confl_id);
  }
  else {
    d_needed_input.insert(confl_id);
  }

  Minisat::Clause& conflc = getClause(confl);
  for(int i=0; i< conflc.size(); i++){
    Minisat::Lit lit = conflc[i];
    ClauseID res_id = getLitReason(lit);
    Assert(hasResolution(res_id));
    lemmaProof(res_id);
    res->addStep(lit, res_id, !sign(lit));
  }
  d_res_map[d_empty_clause_id] = res;
}


/***** debugging printing *****/

inline void Derivation::printLit(Minisat::Lit l)
{
    Debug("proof:res")<<(sign(l) ? "-" : "")<<var(l)+1<<" ";
}


inline void Derivation::printClause(Minisat::CRef cref)
{
  Assert(cref != Minisat::CRef_Undef);
  Minisat::Clause& c = getClause(cref);
  Debug("proof:res")<<"("<<cref<<")";
  if(isRegistered(cref))
    Debug("proof:res")<<"["<<getId(cref)<<"]";
  for (int i = 0; i < c.size(); i++){
        printLit(c[i]);
        Debug("proof:res")<<" ";
    }
    Debug("proof:res")<<"\n";
}

inline void Derivation::printIdClause(ClauseID id){
  if(id == d_empty_clause_id)
    Debug("proof:res")<<" empty ";
  else
  if(d_deleted.count(id))
    Debug("proof:res")<<"del"<<id<<"\n ";
  else
  if(isUnit(id)){
    Debug("proof:res")<<"( unit"<<id<<":";
    printLit(getUnit(id));
    Debug("proof:res")<<") \n";
    }
  else{
    Assert(d_id_clause.find(id)!=d_id_clause.end());
    printClause(d_id_clause[id]);
    }
}

void Derivation::printAllClauses(){
  Debug("proof")<<"d_clauses \n";
  for(std::map<ClauseID, Minisat::CRef>::iterator it = d_id_clause.begin(); it!= d_id_clause.end();it++){
    Debug("proof")<<"id: "<<(*it).first<<" = ";
    if((*it).first!= 0){
      Minisat::CRef cl = (*it).second;
      printClause(cl);
    }
  }

  Debug("proof")<<"d_unit_clauses \n";
  for(std::hash_map<int, ClauseID>::iterator i = d_unit_clauses.begin(); i!=d_unit_clauses.end();i++){
    int lit = (*i).first;
    ClauseID id = (*i).second;
    Debug("proof")<<"var "<<Minisat::var(Minisat::toLit(lit))+1 <<"id: "<<id <<" = ";
    Debug("proof")<<"\n";
  }

  Debug("proof")<<"d_deleted \n";
  for(std::hash_set<ClauseID>::iterator i = d_deleted.begin(); i!=d_deleted.end();i++){
    Debug("proof")<<"del id"<<(*i)<<"\n";
  }

}

void Derivation::printResolution(Minisat::CRef clause){
  ClauseID clause_id = getId(clause);
  printResolution(clause_id);
}


void Derivation::printResolution(ClauseID clause_id){
  Assert(clause_id >= 0);
  Debug("proof:res")<<"Derivation clause_id="<<clause_id<<": ";
  printIdClause(clause_id);
  Debug("proof:res")<<":\n";
  SatResolution* res = getResolution(clause_id);

  vector<ResStep> steps = res->getSteps();
  ClauseID start_id = res->getStart();

  printIdClause(start_id);

  for(unsigned i=0;i< steps.size();i++){
    Debug("proof:res")<<"| ";
    printLit(steps[i].lit);
    Debug("proof:res")<<" "<<(steps[i].sign?"R":"Q");
    Debug("proof:res")<<"| ";
    printIdClause(steps[i].id);
    }
  Debug("proof:res")<<"\n";
}

/***** LFSC Proof *****/

/** helper methods **/


std::string Derivation::printVar(Minisat::Lit l){
  std::stringstream out;
  out<<" v"<<var(l)+1;
  return out.str();
}

std::string Derivation::printClauseVar(ClauseID id){
  std::stringstream out;
  if(isLearned(id))
    out<<"m"<<id;
  else
    out<<"P"<<id;

  return out.str();
}

std::string Derivation::printResChain(ClauseID id){
  std::stringstream start;
  std::stringstream end;
  start<<"satlem _ _ _ ";
  SatResolution* res = getResolution(id);
  std::vector<ResStep> steps =res->getSteps();

  end<<(steps[0].sign? "(R _ _": "(Q _ _");
  end<<printClauseVar(res->getStart())<<" "<<printClauseVar(steps[0].id);
  end<<" "<<printVar(steps[0].lit)<<") ";

  for (unsigned i = 1; i < steps.size() ; i++ ) {
    if(steps[steps.size()-i].sign)
      start<<"(R _ _ ";
    else
      start<<"(Q _ _ ";
    end<<printClauseVar(steps[i].id)<<" ";
    end<<printVar(steps[i].lit)<<") ";
  }

  end<<"(\\"<<printClauseVar(id)<<" \n";
  return (start.str()+end.str());
}

std::string Derivation::printLFSCClause(Minisat::CRef cref){
  std::stringstream ss;
  std::stringstream end;
  if(cref == Minisat::CRef_Undef)
    return "cln";
  Minisat::Clause& clause = getClause(cref);
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

void Derivation::printLFSCProof(Minisat::CRef confl){
   std::stringstream os;
   std::stringstream end;

   finish(confl);
   Assert(hasResolution(d_empty_clause_id));

   os<<"\n(check \n";
   end<<")";

   //printing variables

   for (std::hash_set<int>::iterator i = d_vars.begin(); i!=d_vars.end(); ++i){
     os<<"(% v"<<*i<<" var \n";
     end<<")";
    }

   // printing input clauses
   for(std::hash_set<ClauseID>::iterator i=d_needed_input.begin();i!= d_needed_input.end();i++){
     os<<"(% P"<<*i<<" (holds ";
     if(isUnit(*i)) {
       Minisat::Lit unit = getUnit(*i);
       os<<"( clc ("<<(sign(unit)? " neg ": " pos ")<<"v"<<var(unit)+1<<" ) cln )";
     }
     else {
       os<<printLFSCClause(d_id_clause[*i]);
     }
     os<<")\n";
     end<<")";
   }


   os<<"(: (holds cln) \n";
   end<<")";
   std::cout<<os.str();

   // printing sat lemmas
   for(std::set<ClauseID>::iterator i = d_sat_lemmas.begin(); i!= d_sat_lemmas.end(); i++) {
     std::cout<<"(";
     std::cout<<printResChain(*i);
     end<<"))";
   }
   std::cout<<"(";
   std::cout<<printResChain(d_empty_clause_id);
   std::cout<<" m0";
   end<<"))";
   std::cout<<end.str()<<";";

}


/*
 * Debugging derivation checking
 */


bool Derivation::resolve(Minisat::vec<Minisat::Lit> &clause, ClauseID id, Minisat::Lit lit, bool s){
  Minisat::vec<Minisat::Lit> result;
  bool found = false;
  Minisat::Lit l1, l2;
  if(s) {
    l1 = sign(lit)? ~lit : lit;
    l2 = sign(lit)? lit : ~lit;
  }
  else {
    l1 = sign(lit)? lit: ~lit;
    l2 = sign(lit)? ~lit: lit;
  }

  if(isUnit(id)){
    Minisat::Lit unit = getUnit(id);
    Assert(unit == l2);
    for(int i=0; i<clause.size(); i++){
      if(clause[i]!=l1)
       result.push(clause[i]);
      else
       found = true;
    }
    if(!found)
      return false;
    result.copyTo(clause);
    return true;
  }
  else{
    Minisat::Clause& clause2 = getClause(d_id_clause[id]);
    for(int i=0; i<clause.size(); i++){
      // would also need to check that it has a resolution, presumably it has one
      if(clause[i]!=l1)
       result.push(clause[i]);
      else
        found = true;
    }
    if(!found)
      return false;
    found = false;
    for(int i=0; i<clause2.size(); i++) {
      if(clause2[i]!= l2) {
        if(!hasLit(clause2[i], result))
          result.push(clause2[i]);
      }
      else
        found = true;
    }

    if(!found)
      return false;
    result.copyTo(clause);
    return true;
  }

}

bool Derivation::hasLit(Minisat::Lit l, Minisat::vec<Minisat::Lit>& cl){
  for(int i=0; i<cl.size(); i++)
    if(cl[i]==l)
      return true;

  return false;
}

bool Derivation::compareClauses(ClauseID clause_id, Minisat::vec<Minisat::Lit>& cl2){

  if(!isUnit(clause_id)){
    Assert(d_id_clause.find(clause_id)!=d_id_clause.end());
    Minisat::Clause& cl1 = getClause(d_id_clause[clause_id]);
    if(cl1.size()!=cl2.size())
      return false;

    for(int i=0; i< cl1.size(); i++){
       if(!hasLit(cl1[i], cl2))
         return false;
    }
    return true;
  }
  else{
    Minisat::Lit l = getUnit(clause_id);
    if(cl2.size()==1)
      return l == cl2[0];

    return false;
  }
}

bool Derivation::checkResolution(ClauseID clause_id){
  SatResolution* res = getResolution(clause_id);

  ClauseID start_id = res->getStart();

  Assert(hasResolution(start_id)||!isLearned(start_id));

  Minisat::Clause& start_cl = getClause(d_id_clause[start_id]);
  Minisat::vec<Minisat::Lit> start;
  for(int i=0;i<start_cl.size();i++)
    start.push(start_cl[i]);

  std::vector<ResStep> steps = res->getSteps();
  for(unsigned i=0; i < steps.size(); i++){
    ClauseID id = steps[i].id;
    Assert(hasResolution(id)||!isLearned(id));

    Minisat::Lit l = steps[i].lit;
    if(!resolve(start, id, l, steps[i].sign)){
      Debug("proof:res")<<"Start "<<start<<" id "<<id<<" lit ";
      printLit(l);
      Debug("proof:res")<<"\n";
      printResolution(clause_id);
      return false;
    }
  }

  /*
  Debug("proof")<<"result ";
  for(int i=0;i<start.size();i++)
    printLit(start[i]);
  Debug("proof")<<"\n";
  */
  if(isUnit(clause_id)){
   Minisat::Lit unit = getUnit(clause_id);
   if(start.size()==1 && start[0]==unit)
     return true;
   else {
     Debug("proof:res")<<"checkResolution::FAIL \n";
     printResolution(clause_id);
     return false;
   }
  }

  bool eq = compareClauses(clause_id, start);
  if(!eq) {
    Debug("proof:res")<<"checkResolution::FAIL \n";
    printResolution(clause_id);
    return false;
  }
  return true;
}


}/* prop namespace */
}/* CVC4 namespace */
#endif

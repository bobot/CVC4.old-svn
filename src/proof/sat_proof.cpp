#include "proof/sat_proof.h"
#include "prop/minisat/core/Solver.h"

using namespace std;
using namespace Minisat;

namespace CVC4 {

/// some helper functions 

void printLit (Minisat::Lit l) {
  Debug("proof:sat") << (sign(l) ? "-" : "") << var(l) + 1;
}

void printClause (Minisat::Clause& c) {
  for (int i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " "; 
  }
}

void printLitSet(const LitSet& s) {
  for(LitSet::iterator it = s.begin(); it != s.end(); ++it) {
    printLit(*it);
    Debug("proof:sat") << " "; 
  }
  Debug("proof:sat") << endl; 
}

// purely debugging functions
void printDebug (Minisat::Lit l) {
  Debug("proof:sat") << (sign(l) ? "-" : "") << var(l) + 1 << endl;
}

void printDebug (Minisat::Clause& c) {
  for (int i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " "; 
  }
  Debug("proof:sat") << endl;
}


/** 
 * Converts the clause associated to id to a set of literals
 * 
 * @param id the clause id
 * @param set the clause converted to a set of literals 
 */
void ResolutionProof::createLitSet(ClauseId id, LitSet& set) {
  Assert (set.empty());
  if(isUnit(id)) {
    set.insert(getUnit(id));
    return;
  }
  if ( id == d_emptyClauseId) {
    return; 
  }
  CRef ref = getClauseRef(id);
  Assert (ref != CRef_Undef); 
  Clause& c = d_solver->ca[ref];
  for (int i = 0; i < c.size(); i++) {
    set.insert(c[i]); 
  }
}


/** 
 * Resolves clause1 and clause2 on variable var and stores the
 * result in clause1
 * @param var 
 * @param clause1 
 * @param clause2 
 */
bool resolve(const Lit v, LitSet& clause1, LitSet& clause2, bool s) {
  Assert(!clause1.empty());
  Assert(!clause2.empty()); 
  Lit var = sign(v) ? ~v : v; 
  if (s) {
    // literal appears positive in the first clause
    if( !clause2.count(~var)) {
      Debug("proof:sat") << "proof:resolve: Missing literal ";
      printLit(var);
      Debug("proof:sat") << endl; 
      return false; 
    }
    clause1.erase(var);
    clause2.erase(~var);
    for (LitSet::iterator it = clause2.begin(); it!= clause2.end(); ++it) {
      clause1.insert(*it); 
    }
  } else {
    // literal appears negative in the first clause
    if( !clause1.count(~var) || !clause2.count(var)) {
      Debug("proof:sat") << "proof:resolve: Mising literal ";
      printLit(var);
      Debug("proof:sat") << endl; 
      return false; 
    }
    clause1.erase(~var);
    clause2.erase(var);
    for (LitSet::iterator it = clause2.begin(); it!= clause2.end(); ++it) {
      clause1.insert(*it); 
    }
  }
  return true; 
}

/// ResChain

ResChain::ResChain(ClauseId start) :
    d_start(start),
    d_steps(),
    d_redundantLits(NULL)
  {}

void ResChain::addStep(Lit lit, ClauseId id, bool sign) {
  ResStep step(lit, id, sign);
  d_steps.push_back(step); 
}


void ResChain::addRedundantLit(Lit lit) {
  if (d_redundantLits) {
    d_redundantLits->insert(lit); 
  } else {
    d_redundantLits = new LitSet();
    d_redundantLits->insert(lit); 
  }
}


/// ProxyProof

ProofProxy::ProofProxy(ResolutionProof* proof):
  d_proof(proof)
{}

void ProofProxy::updateCRef(CRef oldref, CRef newref) {
  d_proof->updateCRef(oldref, newref); 
}


/// ResolutionProof

ResolutionProof::ResolutionProof(Minisat::Solver* solver, bool checkRes) :
    d_solver(solver),
    d_idClause(),
    d_clauseId(),
    d_idUnit(),
    d_deleted(),
    d_inputClauses(), 
    d_resChains(),
    d_resStack(),
    d_checkRes(checkRes),
    d_emptyClauseId(-1),
    d_nullId(-2),
    d_temp_clauseId(),
    d_temp_idClause()
  {
    d_proxy = new ProofProxy(this); 
  }


/** 
 * Returns true if the resolution chain corresponding to id
 * does resolve to the clause associated to id
 * @param id 
 * 
 * @return 
 */
bool ResolutionProof::checkResolution(ClauseId id) {
  if(d_checkRes) {
    bool validRes = true; 
    Assert (d_resChains.find(id) != d_resChains.end());
    ResChain* res = d_resChains[id];
    LitSet clause1;
    createLitSet(res->getStart(), clause1);
    ResSteps& steps = res->getSteps(); 
    for (unsigned i = 0; i < steps.size(); i++) {
      Lit    var = steps[i].lit;
      LitSet clause2; 
      createLitSet (steps[i].id, clause2);
      bool res = resolve (var, clause1, clause2, steps[i].sign);
      if(res == false) {
        validRes = false;
        break;
      }
    }
    // compare clause we claimed to prove with the resolution result
    if (isUnit(id)) {
      // special case if it was a unit clause
      Lit unit = getUnit(id);
      validRes = clause1.size() == clause1.count(unit) && !clause1.empty(); 
      return validRes; 
    }
    if (id == d_emptyClauseId) {
      return clause1.empty(); 
    }
    CRef ref = getClauseRef(id);
    Assert (ref != CRef_Undef);
    Clause& c = d_solver->ca[ref];
    for (int i = 0; i < c.size(); ++i) {
      int count = clause1.erase(c[i]);
      if (count == 0) {
        Debug("proof:sat") << "proof:checkResolution::literal not in computed result ";
        printLit(c[i]);
        Debug("proof:sat") << "\n";
        validRes = false; 
      }
    }
    validRes = clause1.empty();
    if (! validRes) {
      Debug("proof:sat") << "proof:checkResolution::Invalid Resolution, unremoved literals: \n";
      printLitSet(clause1);
      Debug("proof:sat") << "proof:checkResolution:: result should be: \n";
      printClause(c); 
    }
    return validRes; 
    
  } else {
    return true; 
  }
}




/// helper methods

ClauseId ResolutionProof::getClauseId(CRef ref) {
  if(d_clauseId.find(ref) == d_clauseId.end()) {
    Debug("proof:sat") << "Missing clause \n"; 
  }
  Assert(d_clauseId.find(ref) != d_clauseId.end());
  return d_clauseId[ref]; 
}


ClauseId ResolutionProof::getClauseId(Lit lit) {
  Assert(d_unitId.find(toInt(lit)) != d_unitId.end());
  return d_unitId[toInt(lit)]; 
}

CRef ResolutionProof::getClauseRef(ClauseId id) {
  if (d_idClause.find(id) == d_idClause.end()) {
    Debug("proof:sat") << "proof:getClauseRef cannot find clause "<<id<<" "
                       << ((d_deleted.find(id) != d_deleted.end()) ? "deleted" : "")
                       << (isUnit(id)? "Unit" : "") << endl;
  }
  Assert(d_idClause.find(id) != d_idClause.end());
  return d_idClause[id]; 
}

Clause& ResolutionProof::getClause(ClauseId id) {
  return d_solver->ca[id]; 
}
Lit ResolutionProof::getUnit(ClauseId id) {
  Assert (d_idUnit.find(id) != d_idUnit.end());
  return d_idUnit[id]; 
}

bool ResolutionProof::isUnit(ClauseId id) {
  return d_idUnit.find(id) != d_idUnit.end(); 
}

bool ResolutionProof::isUnit(Lit lit) {
  return d_unitId.find(toInt(lit)) != d_unitId.end(); 
}

ClauseId ResolutionProof::getUnitId(Lit lit) {
  Assert(isUnit(lit)); 
  return d_unitId[toInt(lit)]; 
}

bool ResolutionProof::hasResolution(ClauseId id) {
  return d_resChains.find(id) != d_resChains.end(); 
}

bool ResolutionProof::isInputClause(ClauseId id) {
  return (d_inputClauses.find(id) != d_inputClauses.end()); 
}


void ResolutionProof::print(ClauseId id) {
  if (d_deleted.find(id) != d_deleted.end()) {
    Debug("proof:sat") << "del"<<id; 
  } else if (isUnit(id)) {
    printLit(getUnit(id)); 
  } else if (id == d_emptyClauseId) {
    Debug("proof:sat") << "empty "<< endl; 
  }
  else {
    CRef ref  = getClauseRef(id);
    Assert (ref != CRef_Undef);
    printClause(d_solver->ca[ref]);
  }
}

void ResolutionProof::printRes(ClauseId id) {
  Assert(hasResolution(id));
  Debug("proof:sat") << "id "<< id <<": ";
  printRes(d_resChains[id]); 
}

void ResolutionProof::printRes(ResChain* res) {
  ClauseId start_id = res->getStart();

  Debug("proof:sat") << "(";
  print(start_id); 

  ResSteps& steps = res->getSteps();
  for(unsigned i = 0; i < steps.size(); i++ ) {
    Lit v = steps[i].lit;
    ClauseId id = steps[i].id;

    Debug("proof:sat") << "[";
    printLit(v);
    Debug("proof:sat") << "] ";
    print(id); 
  }
  Debug("proof:sat") << ") \n";
}

/// registration methods

ClauseId ResolutionProof::registerClause(CRef clause, bool isInput) {
  Assert(clause != CRef_Undef); 
  ClauseIdMap::iterator it = d_clauseId.find(clause);
   if (it == d_clauseId.end()) {
     ClauseId newId = d_idCounter++; 
     d_clauseId[clause]= newId;
     d_idClause[newId] =clause;
     if (isInput) {
       Assert (d_inputClauses.find(newId) == d_inputClauses.end()); 
       d_inputClauses.insert(newId); 
     }
   }
   return d_clauseId[clause]; 
}

ClauseId ResolutionProof::registerUnitClause(Lit lit, bool isInput) {
  UnitIdMap::iterator it = d_unitId.find(toInt(lit));
  if (it == d_unitId.end()) {
    ClauseId newId = d_idCounter++;
    d_unitId[toInt(lit)] = newId;
    d_idUnit[newId] = lit; 
    if (isInput) {
      Assert (d_inputClauses.find(newId) == d_inputClauses.end());
      d_inputClauses.insert(newId); 
    }
  }
  return d_unitId[toInt(lit)]; 
}

void ResolutionProof::removedDfs(Lit lit, LitSet* removedSet, LitVector& removeStack, LitSet& inClause, LitSet& seen){
  // if we already added the literal return
  if (seen.count(lit)) {
    return; 
  }

  CRef reason_ref = d_solver->reason(var(lit));
  if (reason_ref == CRef_Undef) {
    seen.insert(lit);
    removeStack.push_back(lit); 
    return; 
  }

  Assert (reason_ref != CRef_Undef); 
  int size = d_solver->ca[reason_ref].size();
  for (int i = 1; i < size; i++ ) {
    Lit v = d_solver->ca[reason_ref][i];
    if(inClause.count(v) == 0 && seen.count(v) == 0) {
      removedDfs(v, removedSet, removeStack, inClause, seen);
    }
  }
  if(seen.count(lit) == 0) {
    seen.insert(lit); 
    removeStack.push_back(lit);
  }
}

// FIXME: problem with the seen, too strict. Need to fix removing the same literal twice:


// void ResolutionProof::resolveOutRedundant(ResChain* res, CRef reason_ref, LitSet* removed, LitSet& inClause, LitSet& seen) {
//   Assert (reason_ref != CRef_Undef);
  
//   int size = d_solver->ca[reason_ref].size(); 
//   for (int i = 1; i < size; ++i) {
//     Lit v = d_solver->ca[reason_ref][i];
//     if (removed->count(v) == 0 && inClause.count(v) == 0 && seen.count(v) == 0) {
//       CRef cl_ref = d_solver->reason(var(v));
//       if(cl_ref != CRef_Undef) {
//         ClauseId cl_id = registerClause(cl_ref);
//         res->addStep(v, cl_id, !sign(v));
//         seen.insert(v); 
//         resolveOutRedundant(res, cl_ref, removed, inClause, seen);
//       } else {
//         Assert(isUnit(~v));
//         ClauseId cl_id = getUnitId(~v);
//         res->addStep(v, cl_id, !sign(v));
//         seen.insert(v); 
//       }
//     }
    
//   }
// }

void ResolutionProof::removeRedundantFromRes(ResChain* res, ClauseId id) {
  LitSet* removed = res->getRedundant();
  if (removed == NULL) {
    return;
  }

  LitSet inClause;
  createLitSet(id, inClause); 
  
  LitVector removeStack;
  LitSet seen; 
  for (LitSet::iterator it = removed->begin(); it != removed->end(); ++it) {
    removedDfs(*it, removed, removeStack, inClause, seen); 
  }
  
  for (int i = removeStack.size()-1; i >= 0; --i) {
    Lit lit = removeStack[i];
    CRef reason_ref = d_solver->reason(var(lit));
    ClauseId reason_id; 

    if (reason_ref == CRef_Undef) {
      Assert(isUnit(~lit));
      reason_id = getUnitId(~lit); 
    } else {
      reason_id = registerClause(reason_ref);
    }
    res->addStep(lit, reason_id, !sign(lit));
  }
  removed->clear(); 
}

void ResolutionProof::registerResolution(ClauseId id, ResChain* res) {
  Assert(res != NULL);

  removeRedundantFromRes(res, id);
  Assert(res->redundantRemoved()); 

  d_resChains[id] = res;
  printRes(id); 
  if (d_checkRes) {
    if (!checkResolution(id)) {
      Debug("proof:sat") << "Failed resolution \n"; 
    }
    Assert(checkResolution(id));
  }
}


/// recording resolutions

void ResolutionProof::startResChain(CRef start) {
  ClauseId id = getClauseId(start); 
  ResChain* res = new ResChain(id);
  d_resStack.push_back(res); 
}

void ResolutionProof::addResolutionStep(Lit lit, CRef clause, bool sign) {
  ClauseId id = registerClause(clause);
  ResChain* res = d_resStack.back();
  res->addStep(lit, id, sign); 
}

void ResolutionProof::endResChain(CRef clause) {
  Assert(d_resStack.size() > 0);
  ClauseId  id = registerClause(clause); 
  ResChain* res = d_resStack.back();
  registerResolution(id, res);
  d_resStack.pop_back(); 
}


void ResolutionProof::endResChain(Lit lit) {
  Assert(d_resStack.size() > 0);
  ClauseId  id = registerUnitClause(lit); 
  ResChain* res = d_resStack.back();
  

  registerResolution(id, res);
  d_resStack.pop_back(); 
}

void ResolutionProof::storeLitRedundant(Lit lit) {
  Assert(d_resStack.size() > 0);
  ResChain* res = d_resStack.back();
  res->addRedundantLit(lit);  
}

/// constructing resolutions 

ClauseId ResolutionProof::resolveRedundant(ResChain* res) {
  // TODO 
  return d_nullId; 
}

void ResolutionProof::resolveOutUnit(Lit lit) {
  ClauseId id = resolveUnit(~lit);
  ResChain* res = d_resStack.back();
  res->addStep(lit, id, !sign(lit)); 
}

void ResolutionProof::storeUnitResolution(Lit lit) {
  resolveUnit(lit);
}

ClauseId ResolutionProof::resolveUnit(Lit lit) {
  // first check if we already have a resolution for lit
  if(isUnit(lit)) {
    ClauseId id = getClauseId(lit);
    if(hasResolution(id) || isInputClause(id)) {
      return id; 
    }
    Assert (false); 
  }
  CRef reason_ref = d_solver->reason(var(lit));
  Assert (reason_ref != CRef_Undef);
  
  ClauseId reason_id = registerClause(reason_ref); 

  ResChain* res = new ResChain(reason_id); 
  Clause& reason  = d_solver->ca[reason_ref];
  for (int i = 0; i < reason.size(); i++) {
    Lit l = reason[i];
    if(lit != l) { 
      ClauseId res_id = resolveUnit(~l);
      res->addStep(l, res_id, !sign(l));
    }
  }
  ClauseId unit_id = registerUnitClause(lit); 
  registerResolution(unit_id, res);
  return unit_id; 
}

void ResolutionProof::printProof() {
  Debug("proof:sat") << "ResolutionProof::printProof\n";
}

void ResolutionProof::finalizeProof(CRef conflict_ref) {
  Assert(d_resStack.size() == 0);
  //ClauseId conflict_id = getClauseId(conflict_ref); 
  ClauseId conflict_id = registerClause(conflict_ref); //FIXME
  Debug("proof:sat") << "proof::finalizeProof Final Conflict ";
  print(conflict_id);
  
  ResChain* res = new ResChain(conflict_id);
  Clause& conflict = d_solver->ca[conflict_ref] ;
  for (int i = 0; i < conflict.size(); ++i) {
    Lit lit = conflict[i];
    ClauseId res_id = resolveUnit(~lit);
    res->addStep(lit, res_id, !sign(lit)); 
  }
  registerResolution(d_emptyClauseId, res);
  printProof(); 
}

/// CRef manager

void ResolutionProof::updateCRef(CRef oldref, CRef newref) {
  if (d_clauseId.find(oldref) == d_clauseId.end()) {
    return; 
  }
  ClauseId id = getClauseId(oldref);
  Assert (d_temp_clauseId.find(newref) == d_temp_clauseId.end());
  Assert (d_temp_idClause.find(id) == d_temp_idClause.end()); 
  d_temp_clauseId[newref] = id;
  d_temp_idClause[id] = newref;
}

void ResolutionProof::finishUpdateCRef() {
  d_clauseId.swap(d_temp_clauseId);
  d_temp_clauseId.clear();

  d_idClause.swap(d_temp_idClause);
  d_temp_idClause.clear(); 
}

void ResolutionProof::markDeleted(CRef clause) {
  if (d_clauseId.find(clause) != d_clauseId.end()) {
    ClauseId id = getClauseId(clause);
    Assert (d_deleted.find(id) == d_deleted.end()); 
    d_deleted.insert(id); 
  }
}

/// LFSCResolutionProof class

string LFSCResolutionProof::varName(Lit lit) {
  ostringstream os;
  if (sign(lit)) {
    os << "(neg v"<<var(lit) << ")" ; 
  }
  else {
    os << "(pos v"<<var(lit) << ")"; 
  }
  return os.str(); 
}


string LFSCResolutionProof::clauseName(ClauseId id) {
  ostringstream os;
  if (isInputClause(id)) {
    os << "p"<<id;
    return os.str(); 
  } else {
    os << "l"<<id;
    return os.str(); 
  }
}

void LFSCResolutionProof::collectLemmas(ClauseId id) {
  if (d_seenLemmas.find(id) != d_seenLemmas.end()) {
    return; 
  }
  if (d_seenInput.find(id) != d_seenInput.end()) {
    return; 
  }

  if (isInputClause(id)) {
    d_seenInput.insert(id);
    return; 
  } else {
    d_seenLemmas.insert(id); 
  }

  ResChain* res = d_resChains[id];
  ClauseId start = res->getStart();
  collectLemmas(start);

  ResSteps steps = res->getSteps(); 
  for(unsigned i = 0; i < steps.size(); i++) {
    collectLemmas(steps[i].id); 
  }
}



void LFSCResolutionProof::printResolution(ClauseId id) {
  d_lemmaSS << "(satlem _ _ _ ";

  ResChain* res = d_resChains[id];  
  ResSteps& steps = res->getSteps();
  
  for (int i = steps.size()-1; i >= 0; i--) {
    d_lemmaSS << "(";
    d_lemmaSS << (steps[i].sign? "R" : "Q") << " _ _ ";
              
  }
  
  ClauseId start_id = res->getStart();
  if(isInputClause(start_id)) {
    d_seenInput.insert(start_id); 
  }
  d_lemmaSS << clauseName(start_id) << " ";
  
  for(unsigned i = 0; i < steps.size(); i++) {
    d_lemmaSS << clauseName(steps[i].id) << " v" << var(steps[i].lit) <<")"; 
  }
  
  if (id == d_emptyClauseId) {
    d_lemmaSS <<"(\\empty empty)";
    return; 
  }

  d_lemmaSS << "(\\" << clauseName(id) << "\n";   // bind to lemma name
  d_paren << "))";                                // closing parethesis for lemma binding and satlem
}


void LFSCResolutionProof::printInputClause(ClauseId id){
  ostringstream os;
  CRef ref = getClauseRef(id);
  Assert (ref != CRef_Undef);
  Clause& c = getClause(ref);

  d_clauseSS << "(% " << clauseName(id) << " (holds ";
  os << ")"; // closing paren for holds
  d_paren << ")"; // closing paren for (%

  for(int i = 0; i < c.size(); i++) {
    d_clauseSS << " (clc " << varName(c[i]) <<" ";
    os <<")";
    d_seenVars.insert(var(c[i])); 
  }
  d_clauseSS << "cln";
  d_clauseSS << os.str() << "\n";  
} 


void LFSCResolutionProof::printClauses() {
  for (IdHashSet::iterator it = d_seenInput.begin(); it!= d_seenInput.end(); ++it) {
    printInputClause(*it);
  }
}

void LFSCResolutionProof::printVariables() {
  for (VarSet::iterator it = d_seenVars.begin(); it != d_seenVars.end(); ++it) {
    d_varSS << "(% v" << *it <<" var \n";
    d_paren << ")"; 
  }
}


void LFSCResolutionProof::flush() {
  ostringstream out;
  out << "(check \n";
  d_paren <<")"; 
  out << d_varSS.str();
  out << d_clauseSS.str();
  out << "(: (holds cln) \n"; 
  out << d_lemmaSS.str(); 
  d_paren << "))";
  out << d_paren.str();
  out << ";"; //to comment out the solver's answer 
  std::cout << out.str(); 
}

void LFSCResolutionProof::printProof() {
  Debug("proof:sat") << " LFSCResolutionProof::printProof \n";

  // first collect lemmas to print in reverse order
  collectLemmas(d_emptyClauseId); 
  for(IdSet::iterator it = d_seenLemmas.begin(); it!= d_seenLemmas.end(); ++it) {
    if(*it != d_emptyClauseId) {
      printResolution(*it);
    }
  }
  // last resolution to be printed is the empty clause
  printResolution(d_emptyClauseId);

  printClauses();
  printVariables();
  flush();
  
}

} /* CVC4 namespace */


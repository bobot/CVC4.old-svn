/*********************                                                        */
/*! \file bv_sat.cpp
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** 
 **/

#include "bv_sat.h"
#include "theory_bv_utils.h"
using namespace std;

using namespace CVC4::theory::bv::utils;
using namespace CVC4::context; 
namespace CVC4 {
namespace theory {
namespace bv{



/** Helper methods for printing */

std::string toString(Bits* bits) {
  Assert(bits);
  ostringstream os;
  os << "["; 
  for (unsigned i = 0; i < bits->size(); ++i) {
    os << toStringLit(bits->operator[](i)) << (i == bits->size() - 1 ? "": " "); 
  }
  os << "] \n";
  return os.str(); 
}

void printClause (SatClause& c) {
  Debug("bitvector") << c.toString() <<"\n"; 
}


/// ClauseManager
ClauseManager::ClauseManager():
    d_solver(new SatSolver() ),
    //    d_clausePool(),
    d_canAddClause(true),
    d_conflict(NULL),
    d_statistics()
  {}

ClauseManager::Statistics::Statistics() :
  d_numVariables("theory::bv::NumberOfSatVariables", 0),
  d_numTotalClauses("theory::bv::TotalNumberOfAssertedSatClauses",0),
  d_satSolveTimer("theory::bv::SatSolvingTimer"),
  d_unsatCoreTimer("theory::bv::UnsatCoreTimer"),
  d_avgClauseSize("theory::bv::AvgBVClauseSize"),
  d_numDuplicateClauses("theory::bv::NumberOfDuplicateSatClauses", 0)
{
  StatisticsRegistry::registerStat(&d_numVariables);
  StatisticsRegistry::registerStat(&d_numTotalClauses);
  StatisticsRegistry::registerStat(&d_satSolveTimer);
  StatisticsRegistry::registerStat(&d_unsatCoreTimer);
  StatisticsRegistry::registerStat(&d_avgClauseSize);
  StatisticsRegistry::registerStat(&d_numDuplicateClauses);
}

ClauseManager::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numVariables);
  StatisticsRegistry::unregisterStat(&d_numTotalClauses);
  StatisticsRegistry::unregisterStat(&d_satSolveTimer);
  StatisticsRegistry::unregisterStat(&d_unsatCoreTimer);
  StatisticsRegistry::unregisterStat(&d_avgClauseSize);
  StatisticsRegistry::unregisterStat(&d_numDuplicateClauses);
}


ClauseManager::~ClauseManager() {
  delete d_solver;
  delete d_conflict; 
  // TODO: clean up all newly allocated clauses and such 
}

SatClause* ClauseManager::getConflict() {
  TimerStat::CodeTimer codeTimer(d_statistics.d_unsatCoreTimer);
  return d_solver->getUnsatCore();  
}

void ClauseManager::assertClause(SatClause* cl) {
  Assert (cl);

  ++(d_statistics.d_numTotalClauses);
  d_statistics.d_avgClauseSize.addEntry(cl->size()); 

  d_solver->addClause(cl);
}

bool ClauseManager::solve() {
  TimerStat::CodeTimer codeTimer(d_statistics.d_satSolveTimer);
  d_canAddClause = true; 
  bool res =  d_solver->solve();
  return res; 
}

bool ClauseManager::solve(const CDList<SatLit>& assumptions) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_satSolveTimer);
  /// the only clauses that should be "active" now are the term definitions
  /// which must be consistent
  Assert (d_solver->solve());
  // do not allow adding more clauses
  d_canAddClause = true;
  // solve with the marker literals as assumptions
  return d_solver->solve(assumptions); 
}

void ClauseManager::resetSolver() {
  delete d_solver;
  d_solver = NULL; 
  d_solver = new SatSolver();
  d_canAddClause = true; 
}




SatVar ClauseManager::mkMarkerVar() {
  SatVar var = newVar();
  d_solver->setUnremovable(mkLit(var));
  return var; 
}

SatVar ClauseManager::newVar() {
  ++(d_statistics.d_numVariables); 
  return d_solver->newVar(); 
}

void ClauseManager::mkClause(const vector<SatLit>& lits) {
  Assert (d_canAddClause); 
  SatClause* clause = new SatClause(); 
  for (unsigned i = 0; i < lits.size(); ++i) {
    clause->addLiteral(lits[i]); 
  }
  clause->sort();

  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 

  assertClause(clause); 

}

void ClauseManager::mkClause(SatLit lit1) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->sort(); 
  
  
  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 

  assertClause(clause); 
}



void ClauseManager::mkClause(SatLit lit1, SatLit lit2) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->sort(); 
  
  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 

  assertClause(clause); 
}

void ClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->sort(); 

  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 

  assertClause(clause); 

}

void ClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->addLiteral(lit4); 
  clause->sort();


  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 

  assertClause(clause); 
}

void ClauseManager::mkClause(SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5) {
  Assert (d_canAddClause);
  
  SatClause* clause = new SatClause();
  clause->addLiteral(lit1);
  clause->addLiteral(lit2);
  clause->addLiteral(lit3);
  clause->addLiteral(lit4); 
  clause->addLiteral(lit5); 
  clause->sort(); 


  Debug("bitvector-clauses") << "Bitvector::mkClause "<< clause->toString(); 
  assertClause(clause); 
}


/////// CnfConversion


BoolExpr mkBoolVar(SatLit lit) {
  return BoolVar(lit); 
}
BoolExpr mkAnd(BoolExpr e1, BoolExpr e2) {
  return BoolOpExpr(And, e1, e2); 
}
BoolExpr  mkExpr(BoolOp op, BoolExpr e1, BoolExpr e2) {
  return BoolOpExpr(op, e1, e2); 
}

void assertToSat(Node expr, SatLit l1, SatLit l2) {
  BoolExpr e = mkAnd(mkBoolVar(l1), mkBoolVar(l2)); 

}


/////// Bitblaster 


/** 
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 * 
 */
void Bitblaster::bbAtom(TNode node) {

    
  if (hasMarkerVar(node)) {
    return; 
  }

  SatVar markerVar = mkMarkerVar(node);
  d_atomBBStrategies[node.getKind()](node, markerVar, this); 
}
  
Bits* Bitblaster::bbTerm(TNode node) {
  Bits* def = getBBTerm(node);
  if (def) {
    return def; 
  }

  def = d_termBBStrategies[node.getKind()] (node, this);
  Assert (def != NULL);
  Assert (def->size() == utils::getSize(node)); 
  cacheTermDef(node, def); 
  return def; 
}

/// Public methods

/** 
 * Called from preregistration bitblasts the node
 * 
 * @param node 
 * 
 * @return 
 */
void Bitblaster::bitblast(TNode node) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_bitblastTimer);

  /// strip the not
  if (node.getKind() == kind::NOT) {
    node = node[0];
  }
  
  if (node.getKind() == kind::EQUAL ||
      node.getKind() == kind::BITVECTOR_ULT ||
      node.getKind() == kind::BITVECTOR_SLT ||
      node.getKind() == kind::BITVECTOR_ULE || 
      node.getKind() == kind::BITVECTOR_SLE )
    {
    bbAtom(node); 
    }
  else if (node.getKind() == kind::BITVECTOR_UGT ||
           node.getKind() == kind::BITVECTOR_UGE ||
           node.getKind() == kind::BITVECTOR_SGT ||
           node.getKind() == kind::BITVECTOR_SGE )
    {
      Unhandled(node.getKind()); 
    }
  else
    {
      bbTerm(node); 
    }
}

/** 
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * by turning on the marker literal (i.e. setting it to false)
 * @param node the atom to be aserted
 * 
 */
 
void Bitblaster::assertToSat(TNode lit) {
  // strip the not
  TNode node = lit.getKind() == kind::NOT? lit[0] : lit;

  Assert (d_atomMarkerVar.find(node) != d_atomMarkerVar.end()); 
  SatVar markerVar = d_atomMarkerVar[node];
  SatLit markerLit = lit.getKind() == kind::NOT? neg(mkLit(markerVar)) : mkLit(markerVar); 

  Debug("bitvector-bb") << "TheoryBV::Bitblaster::assertToSat asserting node: " << lit <<"\n";
  Debug("bitvector-bb") << "TheoryBV::Bitblaster::assertToSat with literal:   " << toStringLit(markerLit) << "\n";  

  d_assertedAtoms.push_back(markerLit);
}

/** 
 * Calls the solve method for the Sat Solver. 
 * passing it the marker literals to be asserted
 * 
 * @return true for sat, and false for unsat
 */
 
bool Bitblaster::solve() {
  return d_clauseManager->solve(d_assertedAtoms); 
}

void Bitblaster::getConflict(std::vector<TNode>& conflict) {
  SatClause* conflictClause = d_clauseManager->getConflict();
  Assert(conflictClause); 
  
  for (unsigned i = 0; i < conflictClause->size(); i++) {
    SatLit lit = conflictClause->operator[](i);
    SatVar var = mkVar(lit);
    Assert (d_markerVarAtom.find(var) != d_markerVarAtom.end());
    
    TNode atom;
    if(!polarity(lit)) {
      atom = d_markerVarAtom[var];
    }
    else {
      atom = NodeManager::currentNM()->mkNode(kind::NOT, d_markerVarAtom[var]); 
    }
    conflict.push_back(atom); 
  }
}

/** 
 * Resets the Sat solver by creating a new instace of it (Minisat)
 * 
 * 
 */
 
void Bitblaster::resetSolver() {
  d_clauseManager->resetSolver(); 
}


/// Helper methods


void Bitblaster::initAtomBBStrategies() {
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_atomBBStrategies[i] = UndefinedAtomBBStrategy; 
  }
  
  /// setting default bb strategies for atoms
  d_atomBBStrategies [ kind::EQUAL ]           = DefaultEqBB;
  d_atomBBStrategies [ kind::BITVECTOR_ULT ]   = DefaultUltBB;
  d_atomBBStrategies [ kind::BITVECTOR_ULE ]   = DefaultUleBB;
  d_atomBBStrategies [ kind::BITVECTOR_UGT ]   = DefaultUgtBB;
  d_atomBBStrategies [ kind::BITVECTOR_UGE ]   = DefaultUgeBB;
  d_atomBBStrategies [ kind::BITVECTOR_SLT ]   = DefaultSltBB;
  d_atomBBStrategies [ kind::BITVECTOR_SLE ]   = DefaultSleBB;
  d_atomBBStrategies [ kind::BITVECTOR_SGT ]   = DefaultSgtBB;
  d_atomBBStrategies [ kind::BITVECTOR_SGE ]   = DefaultSgeBB;
  
}

void Bitblaster::initTermBBStrategies() {
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_termBBStrategies[i] = UndefinedTermBBStrategy; 
  }
  
  /// setting default bb strategies for terms:
  d_termBBStrategies [ kind::VARIABLE ]               = DefaultVarBB;
  d_termBBStrategies [ kind::CONST_BITVECTOR ]        = DefaultConstBB;
  d_termBBStrategies [ kind::BITVECTOR_NOT ]          = DefaultNotBB;
  d_termBBStrategies [ kind::BITVECTOR_CONCAT ]       = DefaultConcatBB;
  d_termBBStrategies [ kind::BITVECTOR_AND ]          = DefaultAndBB;
  d_termBBStrategies [ kind::BITVECTOR_OR ]           = DefaultOrBB;
  d_termBBStrategies [ kind::BITVECTOR_XOR ]          = DefaultXorBB;
  d_termBBStrategies [ kind::BITVECTOR_NAND ]         = DefaultNandBB ;
  d_termBBStrategies [ kind::BITVECTOR_NOR ]          = DefaultNorBB;
  d_termBBStrategies [ kind::BITVECTOR_COMP ]         = DefaultCompBB ;
  d_termBBStrategies [ kind::BITVECTOR_MULT ]         = DefaultMultBB;
  d_termBBStrategies [ kind::BITVECTOR_PLUS ]         = DefaultPlusBB;
  d_termBBStrategies [ kind::BITVECTOR_SUB ]          = DefaultSubBB;
  d_termBBStrategies [ kind::BITVECTOR_NEG ]          = DefaultNegBB;
  d_termBBStrategies [ kind::BITVECTOR_UDIV ]         = DefaultUdivBB;
  d_termBBStrategies [ kind::BITVECTOR_UREM ]         = DefaultUremBB;
  d_termBBStrategies [ kind::BITVECTOR_SDIV ]         = DefaultSdivBB;
  d_termBBStrategies [ kind::BITVECTOR_SREM ]         = DefaultSremBB;
  d_termBBStrategies [ kind::BITVECTOR_SMOD ]         = DefaultSmodBB;
  d_termBBStrategies [ kind::BITVECTOR_SHL ]          = DefaultShlBB;
  d_termBBStrategies [ kind::BITVECTOR_LSHR ]         = DefaultLshrBB;
  d_termBBStrategies [ kind::BITVECTOR_ASHR ]         = DefaultAshrBB;
  d_termBBStrategies [ kind::BITVECTOR_EXTRACT ]      = DefaultExtractBB;
  d_termBBStrategies [ kind::BITVECTOR_REPEAT ]       = DefaultRepeatBB;
  d_termBBStrategies [ kind::BITVECTOR_ZERO_EXTEND ]  = DefaultZeroExtendBB;
  d_termBBStrategies [ kind::BITVECTOR_SIGN_EXTEND ]  = DefaultSignExtendBB;
  d_termBBStrategies [ kind::BITVECTOR_ROTATE_RIGHT ] = DefaultRotateRightBB;
  d_termBBStrategies [ kind::BITVECTOR_ROTATE_LEFT ]  = DefaultRotateLeftBB;

}
 
bool Bitblaster::hasMarkerVar(TNode atom) {
  return d_atomMarkerVar.find(atom) != d_atomMarkerVar.end();
}

 
SatVar Bitblaster::mkMarkerVar(TNode atom) {
  Assert (d_atomMarkerVar.find(atom) == d_atomMarkerVar.end());
  SatVar var = d_clauseManager->mkMarkerVar(); 
  d_atomMarkerVar[atom] = var;
  d_markerVarAtom[var] = atom;
  return var; 
}

 
void Bitblaster::cacheTermDef(TNode term, Bits* def) {
  Assert (d_termCache.find(term) == d_termCache.end());
  d_termCache[term] = def; 
}

 
Bits* Bitblaster::getBBTerm(TNode node) {
  TermDefMap::iterator it = d_termCache.find(node);
  if (it == d_termCache.end()) {
    return NULL; 
  }
  return d_termCache[node];
}

 
Bits* Bitblaster::freshBits(unsigned size) {
  Bits* newbits = new Bits(); 
  for (unsigned i= 0; i < size; ++i) {
    SatVar var = d_clauseManager->newVar();
    SatLit lit = mkLit(var); 
    newbits->push_back(lit); 
  }
  return newbits; 
}

void Bitblaster::mkClause (const std::vector<SatLit>& lits) {
  d_clauseManager->mkClause(lits);
}

void Bitblaster::mkClause (SatLit lit1){
  d_clauseManager->mkClause(lit1);
}

void Bitblaster::mkClause (SatLit lit1, SatLit lit2){
  d_clauseManager->mkClause(lit1, lit2);
}

void Bitblaster::mkClause (SatLit lit1, SatLit lit2, SatLit lit3){
  d_clauseManager->mkClause(lit1, lit2, lit3);
}

void Bitblaster::mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4){
  d_clauseManager->mkClause(lit1, lit2, lit3, lit4);
}

void Bitblaster::mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5){
  d_clauseManager->mkClause(lit1, lit2, lit3, lit4, lit5);
}

SatVar Bitblaster::newVar() {
  return d_clauseManager->newVar(); 
}
 
Bitblaster::Statistics::Statistics() :
  d_numTermClauses("theory::bv::NumberOfTermSatClauses", 0),
  d_numAtomClauses("theory::bv::NumberOfAtomSatClauses", 0), 
  d_bitblastTimer("theory::bv::BitblastTimer")
{
  StatisticsRegistry::registerStat(&d_numTermClauses);
  StatisticsRegistry::registerStat(&d_numAtomClauses);
  StatisticsRegistry::registerStat(&d_bitblastTimer);
}



Bitblaster::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numTermClauses);
  StatisticsRegistry::unregisterStat(&d_numAtomClauses);
  StatisticsRegistry::unregisterStat(&d_bitblastTimer);
}




} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/

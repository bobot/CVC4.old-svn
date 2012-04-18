/*********************                                                        */
/*! \file bvminisat.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat for cvc4 (bitvectors).
 **/

#include "prop/bvminisat/bvminisat.h"
#include "prop/bvminisat/simp/SimpSolver.h"

using namespace CVC4;
using namespace prop;

BVMinisatSatSolver::BVMinisatSatSolver(context::Context* mainSatContext)
: context::ContextNotifyObj(mainSatContext, false),
  d_minisat(new BVMinisat::SimpSolver(mainSatContext)),
  d_minisatNotify(0),
  d_solveCount(0),
  d_assertionsCount(0),
  d_assertionsRealCount(mainSatContext, 0),
  d_lastPropagation(mainSatContext, 0)
{
  d_statistics.init(d_minisat); 
}


BVMinisatSatSolver::~BVMinisatSatSolver() throw(AssertionException) {
  delete d_minisat;
  delete d_minisatNotify;
}

void BVMinisatSatSolver::setNotify(Notify* notify) {
  d_minisatNotify = new MinisatNotify(notify);
  d_minisat->setNotify(d_minisatNotify);
}

void BVMinisatSatSolver::addClause(SatClause& clause, bool removable) {
  Debug("sat::minisat") << "Add clause " << clause <<"\n";
  BVMinisat::vec<BVMinisat::Lit> minisat_clause;
  toMinisatClause(clause, minisat_clause);
  // for(unsigned i = 0; i < minisat_clause.size(); ++i) {
  //   d_minisat->setFrozen(BVMinisat::var(minisat_clause[i]), true);
  // }
  d_minisat->addClause(minisat_clause);
}

void BVMinisatSatSolver::addMarkerLiteral(SatLiteral lit) {
  d_minisat->addMarkerLiteral(BVMinisat::var(toMinisatLit(lit)));
}

void BVMinisatSatSolver::explain(SatLiteral lit, std::vector<SatLiteral>& explanation) {
  std::vector<BVMinisat::Lit> minisat_explanation;
  d_minisat->explain(toMinisatLit(lit), minisat_explanation);
  for (unsigned i = 0; i < minisat_explanation.size(); ++i) {
    explanation.push_back(toSatLiteral(minisat_explanation[i])); 
  }
}

SatValue BVMinisatSatSolver::assertAssumption(SatLiteral lit, bool propagate) {
  d_assertionsCount ++;
  d_assertionsRealCount = d_assertionsRealCount + 1;
  return toSatLiteralValue(d_minisat->assertAssumption(toMinisatLit(lit), propagate));
}

void BVMinisatSatSolver::notify() {
  while (d_assertionsCount > d_assertionsRealCount) {
    popAssumption();
    d_assertionsCount --;
  }
}

void BVMinisatSatSolver::popAssumption() {
  d_minisat->popAssumption();
}

SatVariable BVMinisatSatSolver::newVar(bool freeze){
  return d_minisat->newVar(true, true, freeze);
}

void BVMinisatSatSolver::markUnremovable(SatLiteral lit){
  d_minisat->setFrozen(BVMinisat::var(toMinisatLit(lit)), true);
}

void BVMinisatSatSolver::interrupt(){
  d_minisat->interrupt();
}

SatValue BVMinisatSatSolver::solve(){
  return toSatLiteralValue(d_minisat->solve());
}

SatValue BVMinisatSatSolver::solve(long unsigned int& resource){
  Trace("limit") << "MinisatSatSolver::solve(): have limit of " << resource << " conflicts" << std::endl;
  if(resource == 0) {
    d_minisat->budgetOff();
  } else {
    d_minisat->setConfBudget(resource);
  }
  BVMinisat::vec<BVMinisat::Lit> empty;
  unsigned long conflictsBefore = d_minisat->conflicts;
  SatValue result = toSatLiteralValue(d_minisat->solveLimited(empty));
  d_minisat->clearInterrupt();
  resource = d_minisat->conflicts - conflictsBefore;
  Trace("limit") << "<MinisatSatSolver::solve(): it took " << resource << " conflicts" << std::endl;
  return result;
}

// SatValue BVMinisatSatSolver::solve(const context::CDList<SatLiteral> & assumptions, bool only_bcp){
//   ++d_solveCount;
//   ++d_statistics.d_statCallsToSolve;

//   Debug("sat::minisat") << "Solve with assumptions ";
//   context::CDList<SatLiteral>::const_iterator it = assumptions.begin();
//   BVMinisat::vec<BVMinisat::Lit> assump;
//   for(; it!= assumptions.end(); ++it) {
//     SatLiteral lit = *it;
//     Debug("sat::minisat") << lit <<" ";
//     assump.push(toMinisatLit(lit));
//   }
//   Debug("sat::minisat") <<"\n";

//   clock_t begin, end;
//   begin = clock();
//   d_minisat->setOnlyBCP(only_bcp); 
//   SatLiteralValue result = toSatLiteralValue(d_minisat->solve(assump));
//   end = clock();
//   d_statistics.d_statSolveTime = d_statistics.d_statSolveTime.getData() + (end - begin)/(double)CLOCKS_PER_SEC; 
//  return result;
// }


void BVMinisatSatSolver::getUnsatCore(SatClause& unsatCore) {
  // TODO add assertion to check the call was after an unsat call
  for (int i = 0; i < d_minisat->conflict.size(); ++i) {
    unsatCore.push_back(toSatLiteral(d_minisat->conflict[i]));
  }
}

SatValue BVMinisatSatSolver::value(SatLiteral l){
	return toSatLiteralValue(d_minisat->value(toMinisatLit(l)));
}

SatValue BVMinisatSatSolver::modelValue(SatLiteral l){
	return toSatLiteralValue(d_minisat->modelValue(toMinisatLit(l)));
}

void BVMinisatSatSolver::unregisterVar(SatLiteral lit) {
  // this should only be called when user context is implemented
  // in the BVSatSolver
  Unreachable();
}

void BVMinisatSatSolver::renewVar(SatLiteral lit, int level) {
  // this should only be called when user context is implemented
  // in the BVSatSolver

  Unreachable();
}

unsigned BVMinisatSatSolver::getAssertionLevel() const {
  // we have no user context implemented so far
  return 0;
}

// converting from internal Minisat representation

SatVariable BVMinisatSatSolver::toSatVariable(BVMinisat::Var var) {
  if (var == var_Undef) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

BVMinisat::Lit BVMinisatSatSolver::toMinisatLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return BVMinisat::lit_Undef;
  }
  return BVMinisat::mkLit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral BVMinisatSatSolver::toSatLiteral(BVMinisat::Lit lit) {
  if (lit == BVMinisat::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(BVMinisat::var(lit)),
                    BVMinisat::sign(lit));
}

SatValue BVMinisatSatSolver::toSatLiteralValue(bool res) {
  if(res) return SAT_VALUE_TRUE;
  else return SAT_VALUE_FALSE;
}

SatValue BVMinisatSatSolver::toSatLiteralValue(BVMinisat::lbool res) {
  if(res == (BVMinisat::lbool((uint8_t)0))) return SAT_VALUE_TRUE;
  if(res == (BVMinisat::lbool((uint8_t)2))) return SAT_VALUE_UNKNOWN;
  Assert(res == (BVMinisat::lbool((uint8_t)1)));
  return SAT_VALUE_FALSE;
}

void BVMinisatSatSolver::toMinisatClause(SatClause& clause,
                                           BVMinisat::vec<BVMinisat::Lit>& minisat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    minisat_clause.push(toMinisatLit(clause[i]));
  }
  Assert(clause.size() == (unsigned)minisat_clause.size());
}

void BVMinisatSatSolver::toSatClause(BVMinisat::vec<BVMinisat::Lit>& clause,
                                       SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
}


// Satistics for BVMinisatSatSolver

BVMinisatSatSolver::Statistics::Statistics() :
  d_statStarts("theory::bv::bvminisat::starts"),
  d_statDecisions("theory::bv::bvminisat::decisions"),
  d_statRndDecisions("theory::bv::bvminisat::rnd_decisions"),
  d_statPropagations("theory::bv::bvminisat::propagations"),
  d_statConflicts("theory::bv::bvminisat::conflicts"),
  d_statClausesLiterals("theory::bv::bvminisat::clauses_literals"),
  d_statLearntsLiterals("theory::bv::bvminisat::learnts_literals"),
  d_statMaxLiterals("theory::bv::bvminisat::max_literals"),
  d_statTotLiterals("theory::bv::bvminisat::tot_literals"),
  d_statEliminatedVars("theory::bv::bvminisat::eliminated_vars"),
  d_statCallsToSolve("theory::bv::bvminisat::calls_to_solve", 0),
  d_statSolveTime("theory::bv::bvminisat::solve_time", 0)
{
  StatisticsRegistry::registerStat(&d_statStarts);
  StatisticsRegistry::registerStat(&d_statDecisions);
  StatisticsRegistry::registerStat(&d_statRndDecisions);
  StatisticsRegistry::registerStat(&d_statPropagations);
  StatisticsRegistry::registerStat(&d_statConflicts);
  StatisticsRegistry::registerStat(&d_statClausesLiterals);
  StatisticsRegistry::registerStat(&d_statLearntsLiterals);
  StatisticsRegistry::registerStat(&d_statMaxLiterals);
  StatisticsRegistry::registerStat(&d_statTotLiterals);
  StatisticsRegistry::registerStat(&d_statEliminatedVars);
  StatisticsRegistry::registerStat(&d_statCallsToSolve);
  StatisticsRegistry::registerStat(&d_statSolveTime);
}

BVMinisatSatSolver::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_statStarts);
  StatisticsRegistry::unregisterStat(&d_statDecisions);
  StatisticsRegistry::unregisterStat(&d_statRndDecisions);
  StatisticsRegistry::unregisterStat(&d_statPropagations);
  StatisticsRegistry::unregisterStat(&d_statConflicts);
  StatisticsRegistry::unregisterStat(&d_statClausesLiterals);
  StatisticsRegistry::unregisterStat(&d_statLearntsLiterals);
  StatisticsRegistry::unregisterStat(&d_statMaxLiterals);
  StatisticsRegistry::unregisterStat(&d_statTotLiterals);
  StatisticsRegistry::unregisterStat(&d_statEliminatedVars);
  StatisticsRegistry::unregisterStat(&d_statCallsToSolve);
  StatisticsRegistry::unregisterStat(&d_statSolveTime);
}

void BVMinisatSatSolver::Statistics::init(BVMinisat::SimpSolver* minisat){
  d_statStarts.setData(minisat->starts);
  d_statDecisions.setData(minisat->decisions);
  d_statRndDecisions.setData(minisat->rnd_decisions);
  d_statPropagations.setData(minisat->propagations);
  d_statConflicts.setData(minisat->conflicts);
  d_statClausesLiterals.setData(minisat->clauses_literals);
  d_statLearntsLiterals.setData(minisat->learnts_literals);
  d_statMaxLiterals.setData(minisat->max_literals);
  d_statTotLiterals.setData(minisat->tot_literals);
  d_statEliminatedVars.setData(minisat->eliminated_vars);
}

//*********************                                                        */
/*! \file bv_solver_types.h
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
 ** \brief Definitions of the SatSolver literal and clause types 
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BV__SOLVER__TYPES_H 
#define __CVC4__BV__SOLVER__TYPES_H 

#define BV_MINISAT
//#define BV_PICOSAT

#ifdef BV_MINISAT  /* BV_MINISAT if we are using the minisat solver for the theory of bitvectors*/
#include "theory/bv/bvminisat/core/Solver.h"
#include "theory/bv/bvminisat/core/SolverTypes.h"
#include "theory/bv/bvminisat/simp/SimpSolver.h"
#endif   /* BV_MINISAT */

#ifdef BV_PICOSAT  /* BV_PICOSAT */
#include "picosat/picosat.h"
#endif  /* BV_PICOSAT */

#include "expr/node.h"
#include <vector>
#include <list>
#include <iostream>
#include <math.h>
#include <ext/hash_map>
#include "context/cdlist.h"
#include "util/stats.h"


namespace CVC4 {
namespace theory {
namespace bv {

#ifdef BV_MINISAT /* BV_MINISAT */
/** 
 * MINISAT type-definitions
 * 
 * 
 */

typedef BVMinisat::Var SatVar; 
typedef BVMinisat::Lit SatLit; 
typedef BVMinisat::vec<SatLit> MinisatClause; // Minisat internal clause representation 

std::string toStringLit(SatLit lit); 

SatLit neg(const SatLit& lit);

struct SatLitHash {
  static size_t hash (const SatLit& lit) {
    return (size_t) toInt(lit);
  }
};

struct SatLitHashFunction {
  size_t operator()(SatLit lit) const {
    return (size_t) toInt(lit); 
  }
};

struct SatLitLess{
  static bool compare(const SatLit& x, const SatLit& y)
  {
    return toInt(x)<toInt(y);
  }
};

#endif /* BV_MINISAT */



#ifdef BV_PICOSAT /* BV_PICOSAT */
/** 
 * PICOSAT type-definitions
 * 
 * 
 */

typedef int SatVar; 
typedef int SatLit; 

std::string toStringLit(SatLit lit); 


SatLit neg(const SatLit& lit); 

struct SatLitHash {
  static size_t hash (const SatLit& lit) {
    return (size_t) lit;
  }
  
};

struct SatLitHashFunction {
  size_t operator()(SatLit lit) const {
    return (size_t) lit; 
  }
};

struct SatLitLess{
  static bool compare(const SatLit& x, const SatLit& y)
  {
    return x < y;
  }
};

#endif /* BV_PICOSAT */


/** 
 * Canonical Clause
 * 
 */
template <class T, class Hash = std::hash<T>, class Less = std::less<T> >
class CanonicalClause {
  std::vector<T> d_data;
  bool d_sorted;
public:
  CanonicalClause() :
    d_data(),
    d_sorted(false)
  {}
  
  void addLiteral(T lit);
  std::string toString(); 
  bool operator==(const CanonicalClause<T, Hash, Less>& other) const; 
  const T& operator[](const unsigned i) const {
    Assert (i <= d_data.size()); 
    return d_data[i];
  }
  
  unsigned size() const {
    return d_data.size(); 
  }

  bool isSorted() const {
    return d_sorted; 
  }

  void sort(); 
};


template <class T, class H, class L> 
void CanonicalClause<T, H, L>::addLiteral(T lit) {
  Assert (!d_sorted); 
  d_data.push_back(lit); 
}

template <class T, class H, class L>
void CanonicalClause<T, H, L>::sort() {
  std::sort (d_data.begin(), d_data.end() );
  d_sorted = true; 
}

template <class T, class H, class L> 
bool CanonicalClause<T, H, L> ::operator==(const CanonicalClause<T, H, L>& other) const{
  // make sure both clauses are indeed in canonical form
  Assert(d_sorted && other.isSorted() ); 
  
  if (d_data.size() != other.size()) {
    return false; 
  }
  for (unsigned i=0; i < other.size(); ++i) {
    if (d_data[i] != other[i]) {
      return false;
    }
  }
  return true; 
}

template <class T, class H, class L>
std::string CanonicalClause<T, H, L>::toString() {
  if (d_data.empty()) {
    return std::string("[]"); 
  }
  std::ostringstream os;
  os << "["; 
  for (unsigned i = 0; i < d_data.size(); i++) {
    os << toStringLit(d_data[i]) << (d_data.size() - 1 == i ? "" : ",") ;
  }
  os <<"] \n";
  return os.str(); 
}

template <class T, class HashFunc, class Less>
struct CanonicalClauseHash {
  size_t operator() (const CanonicalClause<T, HashFunc, Less> cc) const {
    // using a PJW hash
    size_t hash = 0; 

    for (unsigned i= 0; i < cc.size(); ++i) {
      hash  = (hash << 4) + HashFunc::hash(cc[i]);
      size_t g = hash & 0xf0000000;
      if (g!= 0) {
        hash = pow(hash, (g >> 24));
        hash = pow(hash, g); 
      }
    } 
    return hash; 
  }

    
}; 


// all the datastructures outside this file will use SatClause and SatClauseHash 
typedef CanonicalClause<SatLit, SatLitHash, SatLitLess> SatClause; 
typedef CanonicalClauseHash<SatLit, SatLitHash, SatLitLess> SatClauseHash; 



/** 
 * Base class for SatSolver
 * 
 */
class SatSolverInterface {
public:
  virtual ~SatSolverInterface() {};
  virtual void         addClause(const SatClause* cl) = 0;
  virtual bool         solve () = 0;
  virtual bool         solve(const context::CDList<SatLit> & assumps) = 0;
  virtual SatVar       newVar() = 0;
  virtual void         setUnremovable(SatLit) = 0;
  virtual SatClause*   getUnsatCore() = 0;
}; 


#ifdef BV_MINISAT /* BV_MINISAT */

/** 
 * Some helper functions that should be defined for each SAT solver supported
 * 
 * 
 * @return 
 */

SatLit mkLit(SatVar var);
SatVar mkVar(SatLit lit);
bool   polarity(SatLit lit); 

/** 
 * Wrapper class around the minsat solver
 * 
 */
class SatSolver : public SatSolverInterface {
  BVMinisat::SimpSolver d_solver;
  int d_result; 
public:
  SatSolver() :
    d_solver(),
    d_result(0),
    d_statistics()
  {
    d_statistics.init(&d_solver); 
  }
  ~SatSolver() {}

  void addClause(const SatClause* cl) {
    const SatClause& clause = *cl;
    BVMinisat::vec<SatLit> minisat_clause;
    for (unsigned i = 0; i < clause.size(); ++i ) {
      minisat_clause.push(clause[i]); 
    }
    d_solver.addClause(minisat_clause);
  }

  bool solve() {
    if (d_solver.solve()) {
      d_result = 1;
      return true; 
    }
    else {
      d_result = -1;
      return false;
    }
  }

  bool solve(const context::CDList<SatLit> & assumptions) {
    /// pass the assumed marker literals to the solver
    context::CDList<SatLit>::const_iterator it = assumptions.begin();
    BVMinisat::vec<SatLit> assump; 
    for(; it!= assumptions.end(); ++it) {
      SatLit lit = *it;
      assump.push(lit); 
    }

    if(d_solver.solve(assump)) {
      d_result = 1;
      return true; 
    }
    else {
      d_result = -1;
      return false;
    }
    
  }

  SatVar newVar() {
    return d_solver.newVar(); 
  }

  void setUnremovable(SatLit lit) {
    d_solver.setFrozen(BVMinisat::var(lit), true); 
  }

  SatClause* getUnsatCore() {
    SatClause* conflict = new SatClause(); 
    Assert (d_result < 0); 
    for (int i = 0; i < d_solver.conflict.size(); ++i) {
      conflict->addLiteral(d_solver.conflict[i]); 
    }
    conflict->sort();
    
    return conflict; 
  }

  class Statistics {
  public:
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
    ReferenceStat<int> d_statEliminatedVars;
    Statistics() :
      d_statStarts("theory::bv::bvminisat::starts"),
      d_statDecisions("theory::bv::bvminisat::decisions"),
      d_statRndDecisions("theory::bv::bvminisat::rnd_decisions"),
      d_statPropagations("theory::bv::bvminisat::propagations"),
      d_statConflicts("theory::bv::bvminisat::conflicts"),
      d_statClausesLiterals("theory::bv::bvminisat::clauses_literals"),
      d_statLearntsLiterals("theory::bv::bvminisat::learnts_literals"),
      d_statMaxLiterals("theory::bv::bvminisat::max_literals"),
      d_statTotLiterals("theory::bv::bvminisat::tot_literals"),
      d_statEliminatedVars("theory::bv::bvminisat::eliminated_vars")
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
    }
    ~Statistics() {
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
    }
    
    void init(BVMinisat::SimpSolver* minisat){
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
  };
  
  Statistics d_statistics;

  
}; 

#endif /* BV_MINISAT */






#ifdef BV_PICOSAT  /* BV_PICOSAT */

/** 
 * Some helper functions that should be defined for each SAT solver supported
 * 
 * 
 * @return 
 */

SatLit mkLit(SatVar var);
SatVar mkVar(SatLit lit);
bool   polarity(SatLit lit); 


/** 
 * Wrapper to create the impression of a SatSolver class for Picosat
 * which is written in C
 */

class SatSolver: public SatSolverInterface {
  int d_varCount;
  bool d_started;
public:
  SatSolver() :
    d_varCount(0),
    d_started(false)
  {
    picosat_init(); /// call constructor
    picosat_enable_trace_generation(); // required for unsat cores
  }
  
  ~SatSolver() {
    picosat_reset(); 
  }

  void   addClause(const SatClause* cl) {
    Assert (cl);
    const SatClause& clause = *cl; 
    for (unsigned i = 0; i < clause.size(); ++i ) {
      picosat_add(clause[i]); 
    }
    picosat_add(0); // ends clause
  }
  
  bool   solve () {
    if(d_started) {
      picosat_remove_learned(100);
    }
    int res = picosat_sat(-1); // no decision limit
    // 0 UNKNOWN, 10 SATISFIABLE and 20 UNSATISFIABLE
    d_started = true; 
    Assert (res == 10 || res == 20); 
    return res == 10; 
  }
  
  bool   solve(const context::CDList<SatLit> & assumps) {
    context::CDList<SatLit>::const_iterator it = assumps.begin();
    for (; it!= assumps.end(); ++it) {
      picosat_assume(*it); 
    }
    return solve (); 
  }
  
  SatVar newVar() { return ++d_varCount; }

  void   setUnremovable(SatLit lit) {}; 

  SatClause* getUnsatCore() {
    const int* failedAssumption = picosat_failed_assumptions();
    Assert(failedAssumption);

    SatClause* unsatCore = new SatClause();
    while (*failedAssumption != 0) {
      SatLit lit = *failedAssumption;
      unsatCore->addLiteral(neg(lit));
      ++failedAssumption; 
    }
    unsatCore->sort(); 
    return unsatCore; 
  }
}; 


#endif  /* BV_PICOSAT */




} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SOLVER__TYPES_H */

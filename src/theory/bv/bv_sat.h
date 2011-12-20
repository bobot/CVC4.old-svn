/*********************                                                        */
/*! \file bv_sat.h
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
 ** \brief Wrapper around the SAT solver used for bitblasting
 **
 ** Wrapper around the SAT solver used for bitblasting.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BV__SAT_H
#define __CVC4__BV__SAT_H


#include "expr/node.h"
#include <vector>
#include <list>
#include <iostream>
#include <math.h>
#include <ext/hash_map>
#include "context/cdo.h"
#include "context/cdset.h"
#include "context/cdlist.h"
#include "bv_solver_types.h"
#include "theory_bv_utils.h"
#include "util/stats.h"
#include "bitblast_strategies.h"

namespace CVC4 {
namespace theory {
namespace bv {


std::string toString (Bits* bits); 

/** 
  *
 * Responsible of communicating with the SAT solver. Also keeps track of the mapping
 * between ids, canonical clauses and the internal SAT solver clause representation. 
  *
 */

class ClauseManager {
  typedef __gnu_cxx::hash_set<SatClause, SatClauseHash> ClauseSet; 

  SatSolver* d_solver;
  bool       d_canAddClause; /// true if we can still add clauses (set to false after first call of solve)
  SatClause* d_conflict;     /// the marker literals that represent the unsat core corresponding to the most
                             /// recent solve call to the SatSolver
                             /// NULL if the result was SAT
  
  /** 
   * Asserts the clause in the sat solver. 
   * @param clause 
   */
  void       assertClause (SatClause* clause);  
public:
  ClauseManager(); 
  
  ~ClauseManager();
  
  bool solve();
  bool solve(const context::CDList<SatLit>&); 
  void resetSolver(); 

  void mkClause (const std::vector<SatLit>& lits); 
  void mkClause (SatLit lit1); 
  void mkClause (SatLit lit1, SatLit lit2);
  void mkClause (SatLit lit1, SatLit lit2, SatLit lit3);
  void mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4);
  void mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5);

  SatVar mkMarkerVar(); 
  SatVar newVar();
  SatClause* getConflict(); 

private:
  class Statistics {
  public:
    IntStat     d_numVariables, d_numTotalClauses;
    TimerStat   d_satSolveTimer;
    TimerStat   d_unsatCoreTimer; 
    AverageStat d_avgClauseSize;
    IntStat     d_numDuplicateClauses; 
    Statistics();
    ~Statistics(); 

  };

  Statistics d_statistics; 
  
}; 



/** 
 * 
 * BooleanExpr class to store intermediate clauses
 * 
  */

enum BoolOp {
  True,
  False,
  And,
  Or,
  Xor,
  Impl,
  Iff,
  Var,
  Not
};


class BoolExpr {
};

class BoolOpExpr: public BoolExpr {
  BoolOp d_op;
  std::vector<BoolExpr> d_children;

public:
  BoolOpExpr(BoolOp op, BoolExpr expr) :
    d_op(op)
  {
    d_children.push_back(expr); 
  }

  BoolOpExpr(BoolOp op, BoolExpr& expr1, BoolExpr& expr2) :
    d_op(op)
  {
    d_children.push_back(expr1);
    d_children.push_back(expr2); 
  }

  BoolExpr operator[](unsigned i) {
    Assert (i < d_children.size());
    return d_children[i]; 
  }
}; 

class BoolVar : public BoolExpr {
  SatLit d_lit;
public:
  BoolVar(SatLit lit) :
    d_lit(lit) {}

  SatLit getLit() {
    return d_lit;
  }
};


class BoolExprManager {
  __gnu_cxx::hash_set<BoolExpr> d_exprPool;
public:
  

}; 


/** 
 * 
 * The CnfConversion converts Nodes into CNF form
 * 
 * 
 * 
 */
class CnfConversion {
  typedef __gnu_cxx::hash_map<Node, SatLit>  ExprSatLitMap;  
  ClauseManager* d_clauseManager;
  ExprSatLitMap d_cnfCache; 

  SatLit cnfXor(SatLit lit1, SatLit lit2);
  SatLit cnfAnd(SatLit lit1, SatLit lit2);
  SatLit cnfOr(SatLit lit1, SatLit lit2);
  SatLit cnfImpl(SatLit lit1, SatLit lit2);
  SatLit cnfIff(SatLit lit1, SatLit lit2);

  bool   isTranslated(Node expr);
  SatLit getCnf(Node expr);
  void   cacheTranslation(Node expr, SatLit lit);
  SatLit translateNode(Node expr); 

public:
  CnfConversion():
    d_clauseManager(),
    d_cnfCache()
  {}
  
  ~CnfConversion() {
    delete d_clauseManager; 
  }
  
  void asserToSat(Node expr); 

}; 


/** 
 * The Bitblaster that manages the mapping between Nodes 
 * and their bitwise definition 
 * 
 */
class Bitblaster {
  
  typedef __gnu_cxx::hash_map <TNode, Bits*, TNodeHashFunction >              TermDefMap;
  typedef __gnu_cxx::hash_map <TNode, SatVar, TNodeHashFunction >             AtomMarkerVarMap;
  typedef __gnu_cxx::hash_map <SatVar, TNode>                                 MarkerVarAtomMap; 

  typedef Bits*  (*TermBBStrategy) (TNode, Bitblaster*); 
  typedef void   (*AtomBBStrategy) (TNode, SatVar, Bitblaster*); 


  
  TermDefMap               d_termCache;
  ClauseManager*           d_clauseManager;
  AtomMarkerVarMap         d_atomMarkerVar;
  MarkerVarAtomMap         d_markerVarAtom; 
  context::CDList<SatLit>  d_assertedAtoms; /**< context dependent list storing the atoms
                                              currently asserted by the DPLL SAT solver. */

  /// term helper methods
  Bits*         getBBTerm(TNode node);
  void          cacheTermDef(TNode node, Bits* def);


  /// atom helper methods
  bool              hasMarkerVar(TNode node); 
  SatVar            mkMarkerVar(TNode);

  /// function tables for the various bitblasting strategies indexed by node kind
  TermBBStrategy d_termBBStrategies[kind::LAST_KIND];
  AtomBBStrategy d_atomBBStrategies[kind::LAST_KIND]; 

  // helper methods to initialize function tables
  void initAtomBBStrategies();
  void initTermBBStrategies(); 

  /// these are public for the bitblasting strategies 
public:
  Bits*  bbTerm(TNode node);
  SatVar newVar();
  Bits*  freshBits(unsigned size);
  void   mkClause (const std::vector<SatLit>& lits); 
  void   mkClause (SatLit lit1); 
  void   mkClause (SatLit lit1, SatLit lit2);
  void   mkClause (SatLit lit1, SatLit lit2, SatLit lit3);
  void   mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4);
  void   mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5);
  
  // dummy literals that are always forced to be assigned to true and false respectively
  const SatLit d_trueLit;
  const SatLit d_falseLit; 
  
public:
  Bitblaster(context::Context* c) :
    d_termCache(),
    d_clauseManager(new ClauseManager()),
    d_atomMarkerVar(),
    d_markerVarAtom(),
    d_assertedAtoms(c),
    d_trueLit(mkLit(d_clauseManager->mkMarkerVar())),
    d_falseLit(mkLit(d_clauseManager->mkMarkerVar())),
    d_statistics()
  {
    d_clauseManager->mkClause(d_trueLit);
    d_clauseManager->mkClause(neg(d_falseLit));
    initAtomBBStrategies(); 
    initTermBBStrategies(); 
    
  }

  ~Bitblaster() {
    delete d_clauseManager;
    TermDefMap::iterator it = d_termCache.begin();
    for ( ; it!= d_termCache.end(); ++it) {
      delete (*it).second; 
    }
    
  }
  void assertToSat(TNode node);
  bool solve();
  void resetSolver();
  void bitblast(TNode node);
  void getConflict(std::vector<TNode>& conflict); 

private:
  void bbAtom(TNode node);
  
  class Statistics {
  public:
    IntStat  d_numTermClauses, d_numAtomClauses;
    TimerStat d_bitblastTimer;
    Statistics();
    ~Statistics(); 
  }; 
  
  Statistics d_statistics;

};



} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SAT_H */

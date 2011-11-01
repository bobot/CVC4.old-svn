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

#ifndef __CVC4__BV__SAT__THEORY_BV_H
#define __CVC4__BV__SAT__THEORY_BV_H


#include "theory/bv/bvminisat/core/Solver.h"
#include "theory/bv/bvminisat/core/SolverTypes.h"
#include "theory/bv/bvminisat/simp/SimpSolver.h"
#include "expr/node.h"
#include <vector>
#include <iostream>
#include <ext/hash_map>

namespace CVC4 {
namespace theory {
namespace bv {

// fixme
// class SatLit {}; 
// class SatClause {}; 


typedef ::BVMinisat::Lit SatLit; 
typedef ::BVMinisat::vec<SatLit> SatClause; 


class SatInterface {
public:
  virtual ~SatInterface () {};
  virtual void addClause(SatClause& clause) = 0;
};



class BVSolver : public SatInterface {
  // some maps between the atom and the clauses bitblasted
  ::BVMinisat::SimpSolver d_solver; 
public:
  BVSolver();
  void addClause(SatClause& clause);
  void solve();
  // TODO 
};

// TODO is there a more efficient representation? 

typedef std::vector<SatLit> Bits; 
typedef __gnu_cxx::hash_map<TNode, Bits, TNodeHashFunction > TermBitsHashMap;

typedef std::vector<SatClause> Clauses; 
typedef __gnu_cxx::hash_map<TNode, Clauses, TNodeHashFunction> AtomClausesHashMap;

class BitBlaster {
  TermBitsHashMap d_termCache;
  AtomClausesHashMap d_atomCache;
  BVSolver d_solver; 
  
  Clauses& bbAtom (TNode node); 
  Clauses& bbEq   (TNode node); 
  Clauses& bbNeq  (TNode node); 
  
  Bits& bbTerm    (TNode node);
  Bits& bbOr      (TNode node);
  Bits& bbAnd     (TNode node);
  Bits& bbPlus    (TNode node);
  Bits& bbMult    (TNode node);
  Bits& bbLShift  (TNode node);
  Bits& bbRShift  (TNode node);
  
  bool getBBTerm    (TNode node, Bits& bits);
  bool getBBFormula (TNode node, Clauses& clauses); 
public:
  BitBlaster() :
    d_termCache(),
    d_atomCache(),
    d_solver()
  {}
  
  void assertToSat(TNode node);
  void bitblast(TNode node);
  bool solve(); 
};


} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SAT__THEORY_BV_H */

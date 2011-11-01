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
#include <list>
#include <iostream>
#include <ext/hash_map>

namespace CVC4 {
namespace theory {
namespace bv {

typedef BVMinisat::Var SatVar; 
typedef BVMinisat::Lit SatLit; 
typedef BVMinisat::vec<SatLit> SatClause; 


class SatInterface {
public:
  virtual ~SatInterface () {};
  virtual void addClause(SatClause* clause) = 0;
};



class BVSolver : public SatInterface {
  BVMinisat::Solver d_solver; 
public:
  BVSolver();
  void   addClause(SatClause* clause);
  void   addClause(SatLit lit); 
  bool   solve();
  SatVar newVar(); 
};

// TODO is there a more efficient representation? 
typedef std::vector<SatLit> Bits; // FIXME bits not enough  
typedef __gnu_cxx::hash_map<TNode, Bits*, TNodeHashFunction > TermBitsHashMap;

typedef std::vector<SatClause*> Clauses; // FIXME: need to change depending on what info we need from minisat
typedef __gnu_cxx::hash_map<TNode, Clauses, TNodeHashFunction> AtomClausesHashMap;

class Bitblaster {
  context::Context* d_context; 
  TermBitsHashMap d_termCache;
  AtomClausesHashMap d_atomCache;
  BVSolver d_solver; 
  SatLit d_true;
  SatLit d_false; 

  void bbEq   (TNode node); 
  void bbNeq  (TNode node); 
  
  Bits* bbTerm    (TNode node);
  Bits* bbConcat  (TNode node);
  Bits* bbExtract (TNode node);
  Bits* bbConst   (TNode node);
  Bits* bbVar     (TNode node); 
  Bits* bbOr      (TNode node);
  Bits* bbAnd     (TNode node);
  Bits* bbPlus    (TNode node);
  Bits* bbMult    (TNode node);
  Bits* bbLShift  (TNode node);
  Bits* bbRShift  (TNode node);
  
  bool getBBTerm (TNode node, Bits* &bits);
  bool getBBAtom (TNode node, Clauses& clauses); 
public:
  Bitblaster(context::Context* c) :
    d_context(c), 
    d_termCache(),
    d_atomCache(),
    d_solver()
  {
    // forcing the literals d_true to be true and d_false to be false
    // used for constant bitblasting
    BVMinisat::Var trueVar = d_solver.newVar();
    d_true = BVMinisat::mkLit(trueVar);
    //d_solver.addClause(d_true);
    
    BVMinisat::Var falseVar = d_solver.newVar();
    d_false = BVMinisat::mkLit(falseVar);
    //d_solver.addClause(~d_false); 
  }
  ~Bitblaster() {
    AtomClausesHashMap::iterator it = d_atomCache.begin();
    for (; it!= d_atomCache.end(); ++it) {
      Clauses& cls = (*it).second;
      for (unsigned i = 0; i < cls.size(); i++) {
        delete cls[i]; 
      }
    }
    
  }
  void assertToSat(TNode node);
  void bbAtom (TNode node); 
  bool solve(); 
};


} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SAT__THEORY_BV_H */

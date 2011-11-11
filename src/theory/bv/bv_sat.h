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
#include "bv_solver_types.h"

namespace CVC4 {
namespace theory {
namespace bv {

class SatInterface {
public:
  virtual ~SatInterface () {};
  virtual void addClause(SatClause* clause) = 0;
  virtual bool solve() = 0; 
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


typedef std::vector<SatLit>    Bits; 
typedef int                    ClauseId; 
typedef std::vector<ClauseId>  ClauseIds; 

/** 
  *
 * Responsible of communicating with the SAT solver. Also keeps track of the mapping
 * between ids, canonical clauses and the internal SAT solver clause representation. 
 * Base class to be extended for each SatSolver added.
 *
 */
class ClauseManager {
public:
  virtual void assertClause(ClauseId id) = 0;
  virtual bool solve () = 0;
  
  virtual ClauseId mkClause (SatLit lit1, SatLit lit2) = 0;
  virtual ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3) = 0;
  virtual ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4) = 0;
  virtual ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5) = 0;
}; 


/** 
 * The ClauseManager for Minisat
 * 
 */
class MinisatClauseManager: public ClauseManager {
  static int idCount; 

  typedef __gnu_cxx::hash_map <ClauseId, SatClause*>     IdClauseMap;
  typedef __gnu_cxx::hash_map <SatClause, ClauseId, SatClauseHash>      ClauseIdMap; 

  IdClauseMap               d_idClauseMap;        /**< map from ClauseId to clauses */
  ClauseIdMap               d_clauseIdMap;        /**< map from clauses to ClauseId */
  context::CDO<int>         d_assertedClausesIndex; /**< context dependent index that points into the assertion stack.
                                                  Anything below it should be asserted in the current context */
  std::vector<ClauseId>     d_assertedClausesStack; /**< stack storing the ids of all the clauses currently asserted
                                                  in minisat. INVARIANT: should not contain any duplicates. */
  BVMinisat::Solver* d_solver; 

  void popClauses(); 
  void removeClause(ClauseId clause);
  inline SatClause* getClause(ClauseId id);
  inline ClauseId   getId (SatClause* clause);
  inline bool       inPool(SatClause* clause);  
public:
  MinisatClauseManager(context::Context* c) :
    d_idClauseMap(),
    d_clauseIdMap(),
    d_assertedClausesIndex(c),
    d_assertedClausesStack(),
    d_solver()
  {}
  
  ~MinisatClauseManager() {}
  
  void assertClause(ClauseId id);
  bool solve();
  
  ClauseId mkClause (const std::vector<SatLit > & lits); 
  ClauseId mkClause (const SatClause& lits);
  
  ClauseId mkClause (SatLit lit1, SatLit lit2);
  ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3);
  ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4);
  ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5);
  
}; 

/** 
 * Bit-level definition of each bitvector [sub]term
 * 
 * @param bits fresh SAT variables for each bit
 * @param clauses the clauses that define the term in relation to its subterms
 */
class BVTermDefinition {
  Bits*      d_bits;            /// the bits that define the term
  ClauseIds* d_defClauses;      /// the clauses that define the term in relation to its subterms
public:
  BVTermDefinition(Bits* bits, ClauseIds* clauses) :
    d_bits(bits),
    d_defClauses(clauses)
  {}
  const Bits* const bits() {
    return d_bits; 
  }
  const ClauseIds* const clauses() {
    return d_defClauses; 
  }
};

/** 
 * The Default Term BitBlasting strategies using the following pattern
 * 
 * @param res the fresh variables for the resulting bits
 * @param lhs the bit variables for the left-hand side 
 * @param rhs the bit variables for the right-hand side
 * @param mgr the clause manager (to be able to store the clause) 
 * 
 * @return 
 */

struct DefaultMultBB {
  static BVTermDefinition* bitblast(Bits* res, Bits* lhs, Bits* rhs, ClauseManager* mgr) {
    Assert(0);
    return NULL; 
  }
}; 

struct DefaultPlusBB {
  static BVTermDefinition* bitblast(Bits* res, Bits* lhs, Bits* rhs, ClauseManager* mgr) {
    Assert(0);
    return NULL; 
  }
}; 

struct DefaultLtBB {
  static BVTermDefinition* bitblast(Bits* res, Bits* lhs, Bits* rhs, ClauseManager* mgr) {
    Assert(0);
    return NULL; 
  }
}; 

struct DefaultAndBB {
  static BVTermDefinition* bitblast(Bits* res, Bits* lhs, Bits* rhs, ClauseManager* mgr) {
    Assert(0);
    return NULL;
  }
}; 

struct DefaultOrBB {
  static BVTermDefinition* bitblast(Bits* res, Bits* lhs, Bits* rhs, ClauseManager* mgr) {
    ClauseIds* defClauses = new ClauseIds();
    
    for (unsigned i = 0; i < res->size(); ++i) {
      defClauses->push_back( mgr->mkClause( res->operator[](i), ~lhs->operator[](i)) );
      defClauses->push_back( mgr->mkClause( res->operator[](i), ~rhs->operator[](i)) );
      defClauses->push_back( mgr->mkClause(~res->operator[](i),  lhs->operator[](i), rhs->operator[](i)) );
    }
    
    BVTermDefinition* def = new BVTermDefinition(res, defClauses); 
    return def; 
  }
}; 


// class Bitblaster {
// public:
//   Bitblaster(context::Context* c) {}
// }; 

template
<
  class BBPlus = DefaultPlusBB,
  class BBMult = DefaultMultBB,
  class BBAnd  = DefaultAndBB,
  class BBOr   = DefaultOrBB
  >
class Bitblaster {
  
  typedef __gnu_cxx::hash_map <TNode, BVTermDefinition*, TNodeHashFunction >  TermDefMap;
  typedef __gnu_cxx::hash_map <TNode, ClauseIds*, TNodeHashFunction >         AtomDefMap; 

  
  TermDefMap             d_termCache;
  AtomDefMap             d_atomCache; 
  context::CDSet<TNode, TNodeHashFunction>  d_assertedAtoms; // atoms that are currently asserted in the SatSolver

  ClauseManager*         d_clauseManager;
  
  inline BVTermDefinition*      getBBTerm (TNode node);
  inline Bits*                  getBits   (TNode node); 
  inline ClauseIds*             getBBAtom (TNode node);
  
  inline void   cacheAtomDef(TNode node, ClauseIds* def);
  inline void   cacheTermDef(TNode node, BVTermDefinition* def);

  Bits*         freshBits(unsigned size); 
  
  /// fixed strategy bitblasting

  ClauseIds*  bbEqual(TNode node);
  ClauseIds*  bbNeq  (TNode node);
  
  BVTermDefinition* bbVar     (TNode node);
  BVTermDefinition* bbConst   (TNode node);
  BVTermDefinition* bbExtract (TNode node);
  BVTermDefinition* bbConcat  (TNode node);
  BVTermDefinition* bbNot     (TNode node);
  
public:
  Bitblaster(context::Context* c) :
    d_termCache(),
    d_atomCache(),
    d_assertedAtoms(c),
    d_clauseManager(new MinisatClauseManager(c))
  {}
  
  void assertToSat(TNode node);
  bool solve();
  
private:

  ClauseIds* bbAtom(TNode node) {
    ClauseIds* def = getBBAtom(node);
    if (def) {
      return def; 
    }

    switch(node.getKind()) {
    case kind::EQUAL:
      def = bbEqual(node);
      cacheAtomDef(node, def);
      break;
    case kind::NOT:
      def = bbNeq(node);
      cacheAtomDef(node, def);
      break;
    default:
      // TODO: implement other predicates
      Unhandled(node.getKind()); 
    }

    return def; 
  }
  
  BVTermDefinition* bbTerm(TNode node) {
    BVTermDefinition* def;
    if (getBBTerm(node, def)) {
      return def; 
    }

    switch(node.getKind()) {
      
    case kind::VARIABLE:
      def = bbVar(node);
      cacheTermDef(node, def); 
      break;
      
    case kind::CONST_BITVECTOR:
      def = bbConst(node);
      cacheTermDef(node, def); 
      break;
      
    case kind::BITVECTOR_EXTRACT:
      def = bbExtract(node);
      cacheTermDef(node, def); 
      break;
      
    case kind::BITVECTOR_CONCAT:
      def = bbConcat(node);
      cacheTermDef(node, def); 
      break;
      
    case kind::BITVECTOR_NOT:
      def = bbNot(node);
      cacheTermDef(node, def); 
      break;
      
    case kind::BITVECTOR_OR:
    case kind::BITVECTOR_AND:
    case kind::BITVECTOR_PLUS:
    case kind::BITVECTOR_MULT:
      //      def =  bbBinaryOp(node.getKind(), node[0], node[1]);
      cacheTermDef(node, def); 
      break;
      
    default:
      Unhandled(node.getKind());
    }
    
    return def; 
  }

  // BVTermDefinition* bbBinaryOp(CVC4::kind nodeKind, TNode lhs, TNode rhs) {
  //   Bits*  resBits = freshBits(getSize(lhs));

  //   Bits* lhsBits = bbTerm(lhs)->bits();
  //   Bits* rhsBits = bbTerm(rhs)->bits();
    
  //   switch(nodeKind) {
      
  //   case kind::BITVECTOR_OR:
  //     return BBOr::bitblast(resBits, lhsBits, rhsBits);
      
  //   case kind::BITVECTOR_AND:
  //     return BBAnd::bitblast(resBits, lhsBits, rhsBits);
      
  //   case kind::BITVECTOR_PLUS:
  //     return BBPlus::bitblast(resBits, lhsBits, rhsBits);
      
  //   case kind::BITVECTOR_MULT:
  //     return BBMult::bitblast(resBits, lhsBits, rhsBits);

  //   }
  // }
  
};






} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SAT_H */

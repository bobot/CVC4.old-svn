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

namespace CVC4 {
namespace theory {
namespace bv {

class Test; 

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
  virtual bool solve (const context::CDList<SatLit>&) = 0;
  virtual bool solve () = 0; 
  virtual void resetSolver() = 0; 

  virtual SatLit mkLit(SatVar& var) = 0;
  virtual SatVar newVar() = 0; 
  
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
  friend class Test; 

  typedef __gnu_cxx::hash_map <ClauseId, SatClause*>     IdClauseMap;
  typedef __gnu_cxx::hash_map <SatClause, ClauseId, SatClauseHash>      ClauseIdMap; 

  IdClauseMap           d_idClauseMap;          /**< map from ClauseId to clauses */
  ClauseIdMap           d_clauseIdMap;          /**< map from clauses to ClauseId */
  BVMinisat::Solver* d_solver; 

  void popClauses(); 
  void removeClause(ClauseId clause);
  SatClause* getClause(ClauseId id);
  ClauseId   getId (SatClause* clause);
  bool       inPool(SatClause* clause);

  /// marker literals
  BVMinisat::vec<SatLit> d_assumptions; 
public:
  MinisatClauseManager(context::Context* c) :
    d_idClauseMap(),
    d_clauseIdMap(),
    d_solver(new BVMinisat::Solver() ),
    d_assumptions()
  {}
  
  ~MinisatClauseManager() {}
  
  void assertClause(ClauseId id);
  bool solve();
  bool solve(const context::CDList<SatLit>&); 
  void resetSolver(); 
  
  ClauseId mkClause (const std::vector<SatLit > & lits); 
  ClauseId mkClause (const SatClause& lits);
  
  ClauseId mkClause (SatLit lit1, SatLit lit2);
  ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3);
  ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4);
  ClauseId mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5);

  SatLit mkLit(SatVar& var);
  SatVar newVar();


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
  static BVTermDefinition* bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
    return NULL; 
  }
}; 

struct DefaultPlusBB {
  static BVTermDefinition* bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
    return NULL; 
  }
}; 

struct DefaultLtBB {
  static BVTermDefinition* bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
    return NULL; 
  }
}; 

struct DefaultAndBB {
  static BVTermDefinition* bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
    return NULL;
  }
}; 

struct DefaultOrBB {
  static BVTermDefinition* bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
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

/** 
 * The Bitblaster that manages the mapping between Nodes 
 * and their bitwise definition 
 * 
 */
template
<
  class BBPlus, 
  class BBMult, 
  class BBAnd,
  class BBOr
  >
class Bitblaster {
  // FIXME: testing stuff
  friend class Test;
  
  typedef __gnu_cxx::hash_map <TNode, BVTermDefinition*, TNodeHashFunction >  TermDefMap;
  typedef __gnu_cxx::hash_map <TNode, ClauseIds*, TNodeHashFunction >         AtomDefMap; 
  typedef __gnu_cxx::hash_map <TNode, SatLit, TNodeHashFunction >             AtomMarkerLitMap;
  typedef __gnu_cxx::hash_map <SatLit, TNode , SatLitHashFunction>            MarkerLitAtomMap; 
  
  TermDefMap             d_termCache;
  AtomDefMap             d_atomCache;
  
  //context::CDSet<TNode, TNodeHashFunction>  d_assertedAtoms; // atoms that are currently asserted in the SatSolver

  ClauseManager*         d_clauseManager;
  
  BVTermDefinition*      getBBTerm (TNode node);
  Bits*                  getBits   (TNode node); 
  ClauseIds*             getBBAtom (TNode node);
 
  void   cacheAtomDef(TNode node, ClauseIds* def);
  void   cacheTermDef(TNode node, BVTermDefinition* def);

  Bits*         freshBits(unsigned size); 
  
  /// fixed strategy bitblasting

  ClauseIds*  bbEqual(TNode node, SatLit marker);
  ClauseIds*  bbNeq  (TNode node, SatLit marker);
  
  BVTermDefinition* bbVar     (TNode node);
  BVTermDefinition* bbConst   (TNode node);
  BVTermDefinition* bbExtract (TNode node);
  BVTermDefinition* bbConcat  (TNode node);
  BVTermDefinition* bbNot     (TNode node);

  /// marker literal
  AtomMarkerLitMap d_atomMarkerLit;
  MarkerLitAtomMap d_markerLitAtom; 
  SatLit mkMarkerLit(TNode);

  // context::CDO<int>     d_assertedAtomsIndex; /**< context dependent index that points into the assertion
  //                                                  stack. Anything below it should be asserted in the
  //                                                  current context */
  context::CDList<SatLit> d_assertedAtoms; /**< stack storing the asserted atoms. */

public:
  Bitblaster(context::Context* c) :
    d_termCache(),
    d_atomCache(),
    d_assertedAtoms(c),
    //d_assertedAtomsIndex(c),
    d_clauseManager(new MinisatClauseManager(c))
  {}
  
  void assertToSat(TNode node);
  bool solve();
  void resetSolver();
  void bitblast(TNode node); 
private:

  ClauseIds* bbAtom(TNode node) {
    ClauseIds* def = getBBAtom(node);
    if (def) {
      return def; 
    }

    SatLit markerLit = mkMarkerLit(node);  
    
    switch(node.getKind()) {
    case kind::EQUAL:
      def = bbEqual(node, markerLit);
      cacheAtomDef(node, def);
      break;
    case kind::NOT:
      def = bbNeq(node, markerLit);
      cacheAtomDef(node, def);
      break;
    default:
      // TODO: implement other predicates
      Unhandled(node.getKind()); 
    }

    return def; 
  }
  
  BVTermDefinition* bbTerm(TNode node) {
    BVTermDefinition* def = getBBTerm(node);
    if (def) {
      return def; 
    }

    switch(node.getKind()) {
      
    case kind::VARIABLE:
      def = bbVar(node);
      break;
      
    case kind::CONST_BITVECTOR:
      def = bbConst(node);
      break;
      
    case kind::BITVECTOR_EXTRACT:
      def = bbExtract(node);
      break;
      
    case kind::BITVECTOR_CONCAT:
      def = bbConcat(node);
      break;
      
    case kind::BITVECTOR_NOT:
      def = bbNot(node);
      break;
      
    case kind::BITVECTOR_OR:
    case kind::BITVECTOR_AND:
    case kind::BITVECTOR_PLUS:
    case kind::BITVECTOR_MULT:
      def =  bbBinaryOp(node.getKind(), node[0], node[1]);
      break;
      
    default:
      Unhandled(node.getKind());
    }
    
    Assert (def != NULL);
    cacheTermDef(node, def); 

    return def; 
  }

  BVTermDefinition* bbBinaryOp(Kind nodeKind, TNode lhs, TNode rhs) {
    Bits*  resBits = freshBits(utils::getSize(lhs));

    const Bits* lhsBits = bbTerm(lhs)->bits();
    const Bits* rhsBits = bbTerm(rhs)->bits();
    
    switch(nodeKind) {
      
    case kind::BITVECTOR_OR:
      return BBOr::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      
    case kind::BITVECTOR_AND:
      return BBAnd::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      
    case kind::BITVECTOR_PLUS:
      return BBPlus::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      
    case kind::BITVECTOR_MULT:
      return BBMult::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
    default:
      Unhandled(nodeKind); 
    }
  }
};

/// Public methods

template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::bitblast(TNode node) {
  if (node.getKind() == kind::EQUAL || node.getKind() == kind::NOT) {
    bbAtom(node); 
  } else {
    bbTerm(node); 
  }
}

/** 
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * 
 * @param node the atom to be aserted
 * 
 * @return 
 */
template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::assertToSat(TNode node) {
  // ClauseIds* def = bbAtom(node);
  // for (unsigned i = 0; i < def->size(); ++i) {
  //   d_clauseManager->assertClause(def->operator[](i) ); 
  // }

  /// for marker literals everything should be asserted
  Assert (d_atomMarkerLit.find(node) != d_atomMarkerLit.end()); 
  SatLit markerLiteral = d_atomMarkerLit[node];
  d_assertedAtoms.push_back(markerLiteral);
}

/** 
 * Calls the solve method for the Sat Solver. 
 * 
 * 
 * @return true for sat, and false for unsat
 */
template <class Plus, class Mult, class And, class Or>  
bool Bitblaster<Plus, Mult, And, Or>::solve() {

  return d_clauseManager->solve(d_assertedAtoms); 
}

/** 
 * Resets the Sat solver 
 * 
 * 
 * @return 
 */
template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::resetSolver() {
  d_clauseManager->resetSolver(); 
}


/// Helper methods

template <class Plus, class Mult, class And, class Or>  
SatLit Bitblaster<Plus, Mult, And, Or>::mkMarkerLit(TNode atom) {
  Assert (d_atomMarkerLit.find(atom) == d_atomMarkerLit.end());

  SatVar var = d_clauseManager->newVar();
  SatLit lit = d_clauseManager->mkLit(var); 
  d_atomMarkerLit[atom] = lit;
  d_markerLitAtom[lit] = atom;
  return lit; 
}


template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::cacheAtomDef(TNode atom, ClauseIds* def) {
  Assert (d_atomCache.find(atom) == d_atomCache.end());
  d_atomCache[atom] = def;
}

template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::cacheTermDef(TNode term, BVTermDefinition* def) {
  Assert (d_termCache.find(term) == d_termCache.end());
  d_termCache[term] = def; 
}

template <class Plus, class Mult, class And, class Or>  
ClauseIds* Bitblaster<Plus, Mult, And, Or>::getBBAtom(TNode node) {
  AtomDefMap::iterator it = d_atomCache.find(node);
  if (it == d_atomCache.end()) {
    return NULL; 
  }
  return d_atomCache[node];
}


template <class Plus, class Mult, class And, class Or>  
BVTermDefinition* Bitblaster<Plus, Mult, And, Or>::getBBTerm(TNode node) {
  TermDefMap::iterator it = d_termCache.find(node);
  if (it == d_termCache.end()) {
    return NULL; 
  }
  return d_termCache[node];
}

template <class Plus, class Mult, class And, class Or>  
Bits* Bitblaster<Plus, Mult, And, Or>::freshBits(unsigned size) {
  Bits* newbits = new Bits(); 
  for (unsigned i= 0; i < size; ++i) {
    SatVar var = d_clauseManager->newVar();
    SatLit lit = d_clauseManager->mkLit(var); 
    newbits->push_back(lit); 
  }
  return newbits; 
}

  
/// Fixed  bitblasting strategies

template <class Plus, class Mult, class And, class Or>  
ClauseIds* Bitblaster<Plus, Mult, And, Or>::bbEqual(TNode node, SatLit markerLit) {
  Assert(node.getKind() == kind::EQUAL);
  const Bits* lhsBits = bbTerm(node[0])->bits();
  const Bits* rhsBits = bbTerm(node[1])->bits();

  Assert(lhsBits->size() == rhsBits->size());
  ClauseIds* eq = new ClauseIds(); 
  for (unsigned i = 0; i < lhsBits->size(); i++) {
    // adding the constraints lhs_i <=> rhs_i as lhs_i => rhs_i and rhs_i => lhs_i
    eq->push_back(d_clauseManager->mkClause(lhsBits->operator[](i), ~rhsBits->operator[](i), markerLit));
    eq->push_back(d_clauseManager->mkClause(~lhsBits->operator[](i), rhsBits->operator[](i), markerLit));
  }
  return eq; 
}

template <class Plus, class Mult, class And, class Or>  
ClauseIds* Bitblaster<Plus, Mult, And, Or>::bbNeq(TNode node, SatLit markerLit) {
  Assert (0); 
  // FIXME!!! WRONG!! 
  Assert(node.getKind() == kind::EQUAL);
  const Bits* lhsBits = bbTerm(node[0])->bits();
  const Bits* rhsBits = bbTerm(node[1])->bits();

  Assert(lhsBits->size() == rhsBits->size());
  ClauseIds* neq = new ClauseIds(); 
  for (unsigned i = 0; i < lhsBits->size(); i++) {
    // adding the constraints (lhs_i OR rhs_i) and (NOT lhs_i) OR (NOT rhs_i)
    neq->push_back(d_clauseManager->mkClause(~lhsBits->operator[](i), ~rhsBits->operator[](i), markerLit));
    neq->push_back(d_clauseManager->mkClause( lhsBits->operator[](i),  rhsBits->operator[](i), markerLit));
  }
  return neq; 
}

template <class Plus, class Mult, class And, class Or>  
BVTermDefinition* Bitblaster<Plus, Mult, And, Or>::bbConst(TNode node) {
  Assert(node.getKind() == kind::CONST_BITVECTOR);
  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    // TODO : finish!!
  }
  return NULL; 
}
  
template <class Plus, class Mult, class And, class Or>  
BVTermDefinition* Bitblaster<Plus, Mult, And, Or>::bbVar(TNode node) {
  Assert (node.getKind() == kind::VARIABLE);
  Bits* bits;
  bits = freshBits(utils::getSize(node));
  return new BVTermDefinition(bits, new ClauseIds());
}

template <class Plus, class Mult, class And, class Or>  
BVTermDefinition* Bitblaster<Plus, Mult, And, Or>::bbExtract(TNode node) {
  Assert (node.getKind() == kind::BITVECTOR_EXTRACT);
  const Bits* bits = bbTerm(node[0])->bits();
  unsigned high = utils::getExtractHigh(node);
  unsigned low  = utils::getExtractLow(node);

  // TODO: double check this!!
  Bits* extractbits = new Bits(); 
  for (unsigned i = bits->size() - 1 - high; i <= bits->size() -1 - low; ++i) {
    extractbits->push_back(bits->operator[](i)); 
  }
    
  return new BVTermDefinition(extractbits, new ClauseIds()); 
}

template <class Plus, class Mult, class And, class Or>  
BVTermDefinition* Bitblaster<Plus, Mult, And, Or>::bbConcat(TNode node) {
  Assert (node.getKind() == kind::BITVECTOR_CONCAT);
  const Bits* bv1 = bbTerm(node[0])->bits();
  const Bits* bv2 = bbTerm(node[1])->bits();
    
  Bits* bits = new Bits();
    
  for(unsigned i = 0; i < utils::getSize(node[0]); ++i) {
    bits->push_back(bv1->operator[](i));
  }
    
  for(unsigned i = 0; i < utils::getSize(node[1]); ++i) {
    bits->push_back(bv2->operator[](i)); 
  }
  return new BVTermDefinition(bits, new ClauseIds()); 
}

template <class Plus, class Mult, class And, class Or>  
BVTermDefinition* Bitblaster<Plus, Mult, And, Or>::bbNot(TNode node) {
  Assert(node.getKind() == kind::BITVECTOR_NOT);

  const Bits* bv = bbTerm(node[0])->bits();
  Bits* notbv = freshBits(utils::getSize(node[0])); 
    
  ClauseIds* bbnot = new ClauseIds(); 
  for (unsigned i = 0; i < bv->size(); i++) {
    // adding the constraints (lhs_i OR rhs_i) and (NOT lhs_i) OR (NOT rhs_i)
    bbnot->push_back(d_clauseManager->mkClause(~bv->operator[](i), ~notbv->operator[](i)));
    bbnot->push_back(d_clauseManager->mkClause( bv->operator[](i),  notbv->operator[](i)));
  }
  return new BVTermDefinition(notbv, bbnot);  
}
  


} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SAT_H */

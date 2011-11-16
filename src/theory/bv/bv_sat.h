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

typedef std::vector<SatLit>    Bits; 
typedef int                    ClauseId; 
typedef std::vector<ClauseId>  ClauseIds; 


/** 
  *
 * Responsible of communicating with the SAT solver. Also keeps track of the mapping
 * between ids, canonical clauses and the internal SAT solver clause representation. 
  *
 */

class ClauseManager {
  typedef __gnu_cxx::hash_set<SatClause, SatClauseHash> ClauseSet; 

  SatSolver* d_solver;
  ClauseSet  d_clausePool; 
  bool       d_canAddClause; /// true if we can still add clauses (set to false after first call of solve)
  SatClause* d_conflict;     /// the marker literals that represent the unsat core corresponding to the most
                             /// recent solve call to the SatSolver
                             /// NULL if the result was SAT
  
  bool       inPool (SatClause* clause);
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

  void mkClause (SatLit lit1); 
  void mkClause (SatLit lit1, SatLit lit2);
  void mkClause (SatLit lit1, SatLit lit2, SatLit lit3);
  void mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4);
  void mkClause (SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5);

  void mkMarkedClause (SatLit marker, SatLit lit1); 
  void mkMarkedClause (SatLit marker, SatLit lit1, SatLit lit2);
  void mkMarkedClause (SatLit marker, SatLit lit1, SatLit lit2, SatLit lit3);
  void mkMarkedClause (SatLit marker, SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4);
  void mkMarkedClause (SatLit marker, SatLit lit1, SatLit lit2, SatLit lit3, SatLit lit4, SatLit lit5);

  
  SatLit mkLit(SatVar var);
  SatVar newVar();
  SatClause* getConflict(); 

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
  static void bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
  }
}; 

struct DefaultPlusBB {
  static void bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
  }
}; 

struct DefaultLtBB {
  static void bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
  }
}; 

struct DefaultAndBB {
  static void bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
  }
}; 

struct DefaultOrBB {
  static void bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    for (unsigned i = 0; i < res->size(); ++i) {
      mgr->mkClause( res->operator[](i),     neg(lhs->operator[](i)) );
      mgr->mkClause( res->operator[](i),     neg(rhs->operator[](i)) );
      mgr->mkClause(neg(res->operator[](i)), lhs->operator[](i), rhs->operator[](i));
    }
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
  
  typedef __gnu_cxx::hash_map <TNode, Bits*, TNodeHashFunction >              TermDefMap;
  typedef __gnu_cxx::hash_map <TNode, SatLit, TNodeHashFunction >             AtomMarkerLitMap;
  typedef __gnu_cxx::hash_map <SatLit, TNode , SatLitHashFunction>            MarkerLitAtomMap; 
  
  TermDefMap               d_termCache;
  ClauseManager*           d_clauseManager;
  AtomMarkerLitMap         d_atomMarkerLit;
  MarkerLitAtomMap         d_markerLitAtom; 
  context::CDList<SatLit>  d_assertedAtoms; /**< context dependent list storing the atoms
                                              currently asserted by the DPLL SAT solver. */

  /// term helper methods
  Bits*         getBBTerm(TNode node);
  void          cacheTermDef(TNode node, Bits* def);
  Bits*         freshBits(unsigned size);

  /// atom helper methods
  bool              hasMarkerLiteral(TNode node); 
  SatLit            mkMarkerLit(TNode);

  
  /// fixed strategy bitblasting
  void  bbEqual(TNode node, SatLit marker);
  void  bbNeq  (TNode node, SatLit marker);

  // returns the definitional bits for the bitblasted term while adding the
  // definition clauses to the sat solver (note that term definitions will always be asserted in the solver)
  Bits* bbVar     (TNode node);
  Bits* bbConst   (TNode node);
  Bits* bbExtract (TNode node);
  Bits* bbConcat  (TNode node);
  Bits* bbNot     (TNode node);

public:
  Bitblaster(context::Context* c) :
    d_termCache(),
    d_clauseManager(new ClauseManager()),
    d_atomMarkerLit(),
    d_markerLitAtom(),
    d_assertedAtoms(c)
  {}

  ~Bitblaster() {
    // TODO !!
  }
  void assertToSat(TNode node);
  bool solve();
  void resetSolver();
  void bitblast(TNode node);
  void getConflict(std::vector<TNode>& conflict); 
private:
  /** 
   * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
   * NOTE: duplicate clauses are not detected because of marker literal
   * @param node the atom to be bitblasted
   * 
   * @return the ids of the clauses assigned to the atom (not really needed for bitblasting)
   */
  void bbAtom(TNode node) {
    
    if (hasMarkerLiteral(node)) {
      return; 
    }

    SatLit markerLit = mkMarkerLit(node);  
    
    switch(node.getKind()) {
    case kind::EQUAL:
      bbEqual(node, markerLit);
      break;
    case kind::NOT:
      bbNeq(node, markerLit);
      break;
    default:
      // TODO: implement other predicates
      Unhandled(node.getKind()); 
    }
    
    // store the atom marker literal mapping
    d_atomMarkerLit[node] = markerLit;
    d_markerLitAtom[markerLit] = node; 

  }
  
  Bits* bbTerm(TNode node) {
    Bits* def = getBBTerm(node);
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

  Bits* bbBinaryOp(Kind nodeKind, TNode lhs, TNode rhs) {
    Bits*  resBits = freshBits(utils::getSize(lhs));

    const Bits* lhsBits = bbTerm(lhs);
    const Bits* rhsBits = bbTerm(rhs);
    
    switch(nodeKind) {
      
    case kind::BITVECTOR_OR:
      BBOr::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      
    case kind::BITVECTOR_AND:
      BBAnd::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      
    case kind::BITVECTOR_PLUS:
      BBPlus::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      
    case kind::BITVECTOR_MULT:
      BBMult::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
    default:
      Unhandled(nodeKind); 
    }
    
    return resBits; 
  }
};

/// Public methods

/** 
 * Called from preregistration bitblasts the node
 * 
 * @param node 
 * 
 * @return 
 */
template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::bitblast(TNode node) {
  // FIXME: better checks
  if (node.getKind() == kind::EQUAL || node.getKind() == kind::NOT) {
    bbAtom(node); 
  } else {
    bbTerm(node); 
  }
}

/** 
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * by turning on the marker literal (i.e. setting it to false)
 * @param node the atom to be aserted
 * 
 */
template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::assertToSat(TNode node) {
  Assert (d_atomMarkerLit.find(node) != d_atomMarkerLit.end()); 
  SatLit markerLiteral = d_atomMarkerLit[node];
  d_assertedAtoms.push_back(markerLiteral);
}

/** 
 * Calls the solve method for the Sat Solver. 
 * passing it the marker literals to be asserted
 * 
 * @return true for sat, and false for unsat
 */
template <class Plus, class Mult, class And, class Or>  
bool Bitblaster<Plus, Mult, And, Or>::solve() {
  return d_clauseManager->solve(d_assertedAtoms); 
}

template <class Plus, class Mult, class And, class Or>
void Bitblaster<Plus, Mult, And, Or>::getConflict(std::vector<TNode>& conflict) {
  SatClause* conflictClause = d_clauseManager->getConflict();
  Assert(conflictClause); 
  
  for (unsigned i = 0; i < conflictClause->size(); i++) {
    SatLit lit = conflictClause->operator[](i);
    Assert (d_markerLitAtom.find(lit) != d_markerLitAtom.end());
    TNode atom = d_markerLitAtom[lit];
    conflict.push_back(atom); 
  }
}

/** 
 * Resets the Sat solver by creating a new instace of it (Minisat)
 * 
 * 
 */
template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::resetSolver() {
  d_clauseManager->resetSolver(); 
}


/// Helper methods


template <class Plus, class Mult, class And, class Or>  
bool Bitblaster<Plus, Mult, And, Or>::hasMarkerLiteral(TNode atom) {
  return d_atomMarkerLit.find(atom) != d_atomMarkerLit.end();
}


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
void Bitblaster<Plus, Mult, And, Or>::cacheTermDef(TNode term, Bits* def) {
  Assert (d_termCache.find(term) == d_termCache.end());
  d_termCache[term] = def; 
}

template <class Plus, class Mult, class And, class Or>  
Bits* Bitblaster<Plus, Mult, And, Or>::getBBTerm(TNode node) {
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

// FIXME: better to have marker literal at the beginning of the clause?

template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::bbEqual(TNode node, SatLit markerLit) {
  Assert(node.getKind() == kind::EQUAL);
  const Bits* lhsBits = bbTerm(node[0]);
  const Bits* rhsBits = bbTerm(node[1]);

  Assert(lhsBits->size() == rhsBits->size());

  for (unsigned i = 0; i < lhsBits->size(); i++) {
    // adding the constraints lhs_i <=> rhs_i as lhs_i => rhs_i and rhs_i => lhs_i
    d_clauseManager->mkClause(lhsBits->operator[](i), neg(rhsBits->operator[](i)), markerLit);
    d_clauseManager->mkClause(neg(lhsBits->operator[](i)), rhsBits->operator[](i), markerLit);
  }

}

template <class Plus, class Mult, class And, class Or>  
void Bitblaster<Plus, Mult, And, Or>::bbNeq(TNode node, SatLit markerLit) {
  Assert (0); 
  // FIXME!!! WRONG!! 
  Assert(node.getKind() == kind::EQUAL);
  const Bits* lhsBits = bbTerm(node[0]);
  const Bits* rhsBits = bbTerm(node[1]);

  Assert(lhsBits->size() == rhsBits->size());
  for (unsigned i = 0; i < lhsBits->size(); i++) {
    // adding the constraints (lhs_i OR rhs_i) and (NOT lhs_i) OR (NOT rhs_i)
    d_clauseManager->mkClause(neg(lhsBits->operator[](i)), neg(rhsBits->operator[](i)), markerLit);
    d_clauseManager->mkClause( lhsBits->operator[](i),  rhsBits->operator[](i), markerLit);
  }
}

template <class Plus, class Mult, class And, class Or>  
Bits* Bitblaster<Plus, Mult, And, Or>::bbConst(TNode node) {
  Assert(node.getKind() == kind::CONST_BITVECTOR);
  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    // TODO : finish!!
  }
  return NULL; 
}
  
template <class Plus, class Mult, class And, class Or>  
Bits* Bitblaster<Plus, Mult, And, Or>::bbVar(TNode node) {
  Assert (node.getKind() == kind::VARIABLE);
  Bits* bits;
  bits = freshBits(utils::getSize(node));
  return bits; 
}

template <class Plus, class Mult, class And, class Or>  
Bits* Bitblaster<Plus, Mult, And, Or>::bbExtract(TNode node) {
  Assert (node.getKind() == kind::BITVECTOR_EXTRACT);
  const Bits* bits = bbTerm(node[0]);
  unsigned high = utils::getExtractHigh(node);
  unsigned low  = utils::getExtractLow(node);

  // TODO: double check this!!
  Bits* extractbits = new Bits(); 
  for (unsigned i = bits->size() - 1 - high; i <= bits->size() -1 - low; ++i) {
    extractbits->push_back(bits->operator[](i)); 
  }
  Assert (extractbits->size() == high - low + 1);   
  return extractbits; 
}

template <class Plus, class Mult, class And, class Or>  
Bits* Bitblaster<Plus, Mult, And, Or>::bbConcat(TNode node) {
  Assert (node.getKind() == kind::BITVECTOR_CONCAT);
  const Bits* bv1 = bbTerm(node[0]);
  const Bits* bv2 = bbTerm(node[1]);
    
  Bits* bits = new Bits();
    
  for(unsigned i = 0; i < utils::getSize(node[0]); ++i) {
    bits->push_back(bv1->operator[](i));
  }
    
  for(unsigned i = 0; i < utils::getSize(node[1]); ++i) {
    bits->push_back(bv2->operator[](i)); 
  }
  Assert (bits->size() == bv1->size() + bv2->size()); 
  return bits; 
}

template <class Plus, class Mult, class And, class Or>  
Bits* Bitblaster<Plus, Mult, And, Or>::bbNot(TNode node) {
  Assert(node.getKind() == kind::BITVECTOR_NOT);

  const Bits* bv = bbTerm(node[0]);
  Bits* notbv = freshBits(utils::getSize(node[0])); 
    
  for (unsigned i = 0; i < bv->size(); i++) {
    // adding the constraints (lhs_i OR rhs_i) and (NOT lhs_i) OR (NOT rhs_i)
    d_clauseManager->mkClause(neg(bv->operator[](i)), neg(notbv->operator[](i)) );
    d_clauseManager->mkClause( bv->operator[](i),  notbv->operator[](i));
  }
  return notbv; 
}
  


} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SAT_H */

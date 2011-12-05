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

namespace CVC4 {
namespace theory {
namespace bv {

typedef std::vector<SatLit>    Bits; 
typedef int                    ClauseId; 
typedef std::vector<ClauseId>  ClauseIds; 

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
  //  ClauseSet  d_clausePool; 
  bool       d_canAddClause; /// true if we can still add clauses (set to false after first call of solve)
  SatClause* d_conflict;     /// the marker literals that represent the unsat core corresponding to the most
                             /// recent solve call to the SatSolver
                             /// NULL if the result was SAT
  
  //  bool       inPool (SatClause* clause);
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
    Assert(res && lhs && rhs && mgr);
    Assert (0); 
  }
}; 

struct DefaultLtBB {
  static void bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(0);
  }
}; 

struct DefaultAndBB {
  static void bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert(res && lhs && rhs && mgr);
    const Bits& c = *res;
    const Bits& a = *lhs;
    const Bits& b = *rhs;

    for (unsigned i = 0; i < c.size(); ++i) {
      mgr->mkClause(neg(c[i]), a[i]);
      mgr->mkClause(neg(c[i]), b[i]);
      mgr->mkClause(c[i], neg(a[i]), neg(b[i])); 
    }
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

struct DefaultXorBB {
  static void bitblast(Bits* res, const Bits* lhs, const Bits* rhs, ClauseManager* mgr) {
    Assert (res && lhs && rhs && mgr);
    const Bits& c = *res;
    const Bits& a = *lhs;
    const Bits& b = *rhs; 
    for (unsigned i = 0; i < res->size(); ++i) {
      mgr->mkClause(neg(c[i]), a[i], b[i]);
      mgr->mkClause(neg(c[i]), neg(a[i]), neg(b[i]));
      mgr->mkClause(c[i], neg(a[i]), b[i]);
      mgr->mkClause(c[i], a[i], neg(b[i])); 
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
  class BBOr,
  class BBXor
  >
class Bitblaster {
  
  typedef __gnu_cxx::hash_map <TNode, Bits*, TNodeHashFunction >              TermDefMap;
  typedef __gnu_cxx::hash_map <TNode, SatVar, TNodeHashFunction >             AtomMarkerVarMap;
  typedef __gnu_cxx::hash_map <SatVar, TNode>                                 MarkerVarAtomMap; 
  
  TermDefMap               d_termCache;
  ClauseManager*           d_clauseManager;
  AtomMarkerVarMap         d_atomMarkerVar;
  MarkerVarAtomMap         d_markerVarAtom; 
  context::CDList<SatLit>  d_assertedAtoms; /**< context dependent list storing the atoms
                                              currently asserted by the DPLL SAT solver. */

  // dummy literals that are always forced to be assigned to true and false respectively
  const SatLit d_trueLit;
  const SatLit d_falseLit; 
  /// term helper methods
  Bits*         getBBTerm(TNode node);
  void          cacheTermDef(TNode node, Bits* def);
  Bits*         freshBits(unsigned size);

  /// atom helper methods
  bool              hasMarkerVareral(TNode node); 
  SatVar            mkMarkerVar(TNode);


  
  /// fixed strategy bitblasting
  void  bbEqual(TNode node, SatVar marker);

  // returns the definitional bits for the bitblasted term while adding the
  // definition clauses to the sat solver (note that term definitions will always be asserted in the solver)
  Bits* bbVar        (TNode node);
  Bits* bbConst      (TNode node);
  Bits* bbExtract    (TNode node);
  Bits* bbConcat     (TNode node);
  Bits* bbNot        (TNode node);
  Bits* bbZeroExtend (TNode node); 
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
  }


public:

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
  /** 
   * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
   * NOTE: duplicate clauses are not detected because of marker literal
   * @param node the atom to be bitblasted
   * 
   */
  void bbAtom(TNode node) {

    /// strip the not
    if (node.getKind() == kind::NOT) {
      node = node[0];
    }
    
    if (hasMarkerVareral(node)) {
      return; 
    }

    SatVar markerVar = mkMarkerVar(node);
    switch(node.getKind()) {
    case kind::EQUAL:
      bbEqual(node, markerVar);
      break;
    default:
      // TODO: implement other predicates
      Unhandled(node.getKind()); 
    }
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
    case kind::BITVECTOR_ZERO_EXTEND:
      def = bbZeroExtend(node);
      break;
    case kind::BITVECTOR_OR:
    case kind::BITVECTOR_AND:
    case kind::BITVECTOR_PLUS:
    case kind::BITVECTOR_MULT:
    case kind::BITVECTOR_XOR:
      def =  bbBinaryOp(node);
      break;
    default:
      Unhandled(node.getKind());
    }
    
    Assert (def != NULL);
    cacheTermDef(node, def); 

    return def; 
  }

  Bits* bbBinaryOp(TNode node) {
    TNode lhs = node[0];
    TNode rhs = node[1];
    Kind nodeKind = node.getKind(); 
    
    Bits*  resBits = freshBits(utils::getSize(lhs));

    Debug("bitvector-bb") << "Bitblasting node " << node << "\n";
    Debug("bitvector-bb") << "       with bits " << toString(resBits) ; 

    const Bits* lhsBits = bbTerm(lhs);
    const Bits* rhsBits = bbTerm(rhs);
    
    switch(nodeKind) {
      
    case kind::BITVECTOR_OR:
      BBOr::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      break;
    case kind::BITVECTOR_AND:
      BBAnd::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      break;
    case kind::BITVECTOR_PLUS:
      BBPlus::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      break;
    case kind::BITVECTOR_MULT:
      BBMult::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      break;
    case kind::BITVECTOR_XOR:
      BBXor::bitblast(resBits, lhsBits, rhsBits, d_clauseManager);
      break;
    default:
      Debug("bb") << "sadasd"; 
      Unhandled(nodeKind); 
    }
    
    return resBits; 
  }

private:  
  class Statistics {
  public:
    IntStat  d_numTermClauses, d_numAtomClauses;
    TimerStat d_bitblastTimer;
    Statistics();
    ~Statistics(); 
  }; 
  
  Statistics d_statistics;


};

/// Public methods

/** 
 * Called from preregistration bitblasts the node
 * 
 * @param node 
 * 
 * @return 
 */
template <class Plus, class Mult, class And, class Or, class Xor>  
void Bitblaster<Plus, Mult, And, Or, Xor>::bitblast(TNode node) {
  // FIXME: better checks
  TimerStat::CodeTimer codeTimer(d_statistics.d_bitblastTimer);
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
template <class Plus, class Mult, class And, class Or, class Xor>  
void Bitblaster<Plus, Mult, And, Or, Xor>::assertToSat(TNode lit) {
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
template <class Plus, class Mult, class And, class Or, class Xor>  
bool Bitblaster<Plus, Mult, And, Or, Xor>::solve() {
  return d_clauseManager->solve(d_assertedAtoms); 
}

template <class Plus, class Mult, class And, class Or, class Xor>
void Bitblaster<Plus, Mult, And, Or, Xor>::getConflict(std::vector<TNode>& conflict) {
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
template <class Plus, class Mult, class And, class Or, class Xor>  
void Bitblaster<Plus, Mult, And, Or, Xor>::resetSolver() {
  d_clauseManager->resetSolver(); 
}


/// Helper methods


template <class Plus, class Mult, class And, class Or, class Xor>  
bool Bitblaster<Plus, Mult, And, Or, Xor>::hasMarkerVareral(TNode atom) {
  return d_atomMarkerVar.find(atom) != d_atomMarkerVar.end();
}


template <class Plus, class Mult, class And, class Or, class Xor>  
SatVar Bitblaster<Plus, Mult, And, Or, Xor>::mkMarkerVar(TNode atom) {
  Assert (d_atomMarkerVar.find(atom) == d_atomMarkerVar.end());
  SatVar var = d_clauseManager->mkMarkerVar(); 
  d_atomMarkerVar[atom] = var;
  d_markerVarAtom[var] = atom;
  return var; 
}


template <class Plus, class Mult, class And, class Or, class Xor>  
void Bitblaster<Plus, Mult, And, Or, Xor>::cacheTermDef(TNode term, Bits* def) {
  Assert (d_termCache.find(term) == d_termCache.end());
  d_termCache[term] = def; 
}

template <class Plus, class Mult, class And, class Or, class Xor>  
Bits* Bitblaster<Plus, Mult, And, Or, Xor>::getBBTerm(TNode node) {
  TermDefMap::iterator it = d_termCache.find(node);
  if (it == d_termCache.end()) {
    return NULL; 
  }
  return d_termCache[node];
}

template <class Plus, class Mult, class And, class Or, class Xor>  
Bits* Bitblaster<Plus, Mult, And, Or, Xor>::freshBits(unsigned size) {
  Bits* newbits = new Bits(); 
  for (unsigned i= 0; i < size; ++i) {
    SatVar var = d_clauseManager->newVar();
    SatLit lit = mkLit(var); 
    newbits->push_back(lit); 
  }
  return newbits; 
}

  

/// Fixed  bitblasting strategies


/** 
 * Will add the clauses expressing atom_lit = (node[0] = node[1])
 * 
 * @param node 
 * @param atom_lit 
 * 
 * @return 
 */
template <class Plus, class Mult, class And, class Or, class Xor>  
void Bitblaster<Plus, Mult, And, Or, Xor>::bbEqual(TNode node, SatVar atom_var) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Debug("bitvector-bb") << "      marker lit " << toStringLit(mkLit(atom_var)) << "\n"; 
  
  Assert(node.getKind() == kind::EQUAL);
  const Bits& lhs = *(bbTerm(node[0]));
  const Bits& rhs = *(bbTerm(node[1]));

  Assert(lhs.size() == rhs.size());

  SatLit atom_lit = mkLit(atom_var); 
  std::vector<SatLit> lits;
  /// constructing the clause x_1 /\ .. /\ x_n =
  lits.push_back(atom_lit);
  
  for (unsigned i = 0; i < lhs.size(); i++) {
    SatLit x = mkLit(d_clauseManager->newVar());
    
    /// Adding the clauses corresponding to:
    ///       x_i = (lhs_i = rhs_i)
    d_clauseManager->mkClause(neg(x), lhs[i], neg(rhs[i]));
    d_clauseManager->mkClause(neg(x), neg(lhs[i]), rhs[i]);
    d_clauseManager->mkClause(x, lhs[i], rhs[i]);
    d_clauseManager->mkClause(x, neg(lhs[i]), neg(rhs[i]));

    /// adding the clauses for atom_lit => x_1 /\ ... /\ x_n
    d_clauseManager->mkClause(neg(atom_lit), x); 
    lits.push_back(neg(x));
  }
  d_clauseManager->mkClause(lits); 
}


template <class Plus, class Mult, class And, class Or, class Xor>  
Bits* Bitblaster<Plus, Mult, And, Or, Xor>::bbConst(TNode node) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";

  Assert(node.getKind() == kind::CONST_BITVECTOR);
  Bits* bits = new Bits();
  for (int i = utils::getSize(node) - 1; i >= 0; --i) {
    Integer bit = node.getConst<BitVector>().extract(i, i).getValue();
    if(bit == Integer(0)){
      bits->push_back(d_falseLit);
    } else {
      Assert (bit == Integer(1));
      bits->push_back(d_trueLit); 
    }
  }
  return bits; 
}
  
template <class Plus, class Mult, class And, class Or, class Xor>  
Bits* Bitblaster<Plus, Mult, And, Or, Xor>::bbVar(TNode node) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert (node.getKind() == kind::VARIABLE);
  Bits* bits;
  bits = freshBits(utils::getSize(node));
  Debug("bitvector-bb") << " with bits       " << toString(bits); 
  return bits; 
}



template <class Plus, class Mult, class And, class Or, class Xor>  
Bits* Bitblaster<Plus, Mult, And, Or, Xor>::bbExtract(TNode node) {
  Debug("bitvector-bb") << "Bitblasting node " << node;
  
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

template <class Plus, class Mult, class And, class Or, class Xor>  
Bits* Bitblaster<Plus, Mult, And, Or, Xor>::bbConcat(TNode node) {
  Debug("bitvector-bb") << "Bitblasting node " << node << "\n";
  Assert (node.getKind() == kind::BITVECTOR_CONCAT);
  TNode first = node[0];
  TNode second = node[1]; 
  const Bits* bv1 = bbTerm(first);
  const Bits* bv2 = bbTerm(second);
    
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

template <class Plus, class Mult, class And, class Or, class Xor>  
Bits* Bitblaster<Plus, Mult, And, Or, Xor>::bbNot(TNode node) {
  Debug("bitvector-bb") << "Bitblasting node " << node << "\n";
  
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

template <class Plus, class Mult, class And, class Or, class Xor>  
Bits* Bitblaster<Plus, Mult, And, Or, Xor>::bbZeroExtend(TNode node) {
  Debug("bitvector-bb") << "Bitblasting node " << node  << "\n";
  Assert (node.getKind() == kind::BITVECTOR_ZERO_EXTEND);
  Bits* bits = bbTerm(node[0]); 
  unsigned amount = node.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount; 
  Bits* res_bits = new Bits();

  for (unsigned i = 0 ; i < amount ; ++i ) {
    res_bits->push_back(d_falseLit); 
  }
  for (unsigned i = 0; i < bits->size(); ++i ) {
    res_bits->push_back(bits->operator[](i)); 
  }
  Assert (res_bits->size() == amount + bits->size()); 
  return res_bits; 
}


template <class Plus, class Mult, class And, class Or, class Xor>  
Bitblaster<Plus, Mult, And, Or, Xor>::Statistics::Statistics() :
  d_numTermClauses("theory::bv::NumberOfTermSatClauses", 0),
  d_numAtomClauses("theory::bv::NumberOfAtomSatClauses", 0), 
  d_bitblastTimer("theory::bv::BitblastTimer")
{
  StatisticsRegistry::registerStat(&d_numTermClauses);
  StatisticsRegistry::registerStat(&d_numAtomClauses);
  StatisticsRegistry::registerStat(&d_bitblastTimer);
}


template <class Plus, class Mult, class And, class Or, class Xor>  
Bitblaster<Plus, Mult, And, Or, Xor>::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numTermClauses);
  StatisticsRegistry::unregisterStat(&d_numAtomClauses);
  StatisticsRegistry::unregisterStat(&d_bitblastTimer);
}


} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SAT_H */

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
#include "context/cdhashset.h"
#include "context/cdlist.h"

#include "theory_bv_utils.h"
#include "util/stats.h"
#include "bitblast_strategies.h"

#include "prop/sat_module.h"

namespace CVC4 {

// forward declarations
namespace prop {
class CnfStream;
class BVSatSolverInterface;
}


namespace theory {
namespace bv {


std::string toString (Bits& bits); 

/** 
 * The Bitblaster that manages the mapping between Nodes 
 * and their bitwise definition 
 * 
 */

typedef std::vector<Node> Bits; 

class Bitblaster {
  
  typedef __gnu_cxx::hash_map <Node, Bits, TNodeHashFunction >              TermDefMap;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction>                      AtomSet; 
  
  typedef void   (*TermBBStrategy) (TNode, Bits&, Bitblaster*); 
  typedef Node   (*AtomBBStrategy) (TNode, Bitblaster*); 

  // sat solver used for bitblasting and associated CnfStream
  prop::BVSatSolverInterface*        d_satSolver; 
  prop::CnfStream*                   d_cnfStream;

  // caches and mappings
  TermDefMap                   d_termCache;
  AtomSet                      d_bitblastedAtoms;
  
  context::CDList<prop::SatLiteral>  d_assertedAtoms; /**< context dependent list storing the atoms
                                                       currently asserted by the DPLL SAT solver. */

  /// helper methods
  bool          hasBBAtom(TNode node);    
  bool          hasBBTerm(TNode node); 
  void          getBBTerm(TNode node, Bits& bits);




  /// function tables for the various bitblasting strategies indexed by node kind
  TermBBStrategy d_termBBStrategies[kind::LAST_KIND];
  AtomBBStrategy d_atomBBStrategies[kind::LAST_KIND]; 

  // helper methods to initialize function tables
  void initAtomBBStrategies();
  void initTermBBStrategies(); 

  // returns a node that might be easier to bitblast
  Node bbOptimize(TNode node); 
  
  void bbAtom(TNode node);
  // division is bitblasted in terms of constraints
  // so it needs to use private bitblaster interface
  void bbUdiv(TNode node, Bits& bits);
  void bbUrem(TNode node, Bits& bits); 
public:
  void cacheTermDef(TNode node, Bits def); // public so we can cache remainder for division
  void bbTerm(TNode node, Bits&  bits);
  
public:
  Bitblaster(context::Context* c); 
  ~Bitblaster();
  void assertToSat(TNode node);
  bool solve();
  void bitblast(TNode node);
  void getConflict(std::vector<TNode>& conflict); 
  void dumpDimacs(const std::string& file); 
private:

  
  class Statistics {
  public:
    IntStat d_numTermClauses, d_numAtomClauses;
    IntStat d_numTerms, d_numAtoms; 
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

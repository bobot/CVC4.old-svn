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
#include "context/cdo.h"

namespace CVC4 {
namespace theory {
namespace bv {

#ifdef BV_MINISAT /* BV_MINISAT */

typedef BVMinisat::Var SatVar; 
typedef BVMinisat::Lit SatLit; 
typedef BVMinisat::vec<SatLit> MinisatClause; // Minisat internal clause representation 


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

#ifdef BV_PICOSAT  /* BV_PICOSAT */

//TODO: define SatVar, SatLit and Clause and SatLitHash, SatLitLess 

#endif  /* BV_PICOSAT */


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
}

template <class T, class H, class L> 
bool CanonicalClause<T, H, L> ::operator==(const CanonicalClause<T, H, L>& other) const{
  // make sure both clauses are indeed in canonical form

  Assert(d_sorted && other.isSorted() ); 
  
  if (d_data.size() != other.size()) {
    return false; 
  }
  for (unsigned i=0; i != other.size(); ++i) {
    if (d_data[i] != other[i]) {
      return false;
    }
  }
  return true; 
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


// all the datastructures will use SatClause and SatClauseHash 
typedef CanonicalClause<SatLit, SatLitHash, SatLitLess> SatClause; 
typedef CanonicalClauseHash<SatLit, SatLitHash, SatLitLess> SatClauseHash; 


} /* bv namespace */ 

} /* theory namespace */

} /* CVC4 namespace */

#endif /* __CVC4__BV__SOLVER__TYPES_H */

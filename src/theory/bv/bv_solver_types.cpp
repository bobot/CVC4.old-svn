/*********************                                                        */
/*! \file bv_sat.cpp
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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** 
 **/

#include "theory_bv_utils.h"
#include "bv_solver_types.h"

using namespace std;
using namespace CVC4::theory::bv::utils;
namespace CVC4 {
namespace theory {
namespace bv{



/// CanonicalClause


template <class T, class H, class L> 
void CanonicalClause<T, H, L>::addLiteral(T lit) {
  for (typename list<T>::iterator it = d_data.begin(); it!=d_data.end(); ++it) {
    T elem = *it; 
    if (L::compare(lit, elem)) {
      ++it; 
      d_data.insert(it, lit);
      return; 
    }
  }
}

template <class T, class H, class L> 
bool CanonicalClause<T, H, L> ::operator==(const CanonicalClause<T, H, L>& other) const{
  if (d_data.size() != other.d_data.size()) {
    return false; 
  }
  typename list<T>::const_iterator it1 = d_data.begin();
  typename list<T>::const_iterator it2 = other.d_data.begin();
  for (; it1 != d_data.end(); ++it1, ++it2) {
    if (*it1 != *it2) {
      return false;
    }
  }
  return true; 
}


} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace */

/*********************                                                        */
/*! \file triple.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: lianah
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Similar to std::pair<>, for triples and quadruple
 **
 ** Similar to std::pair<>, for triples and quadruple.  Once we move to c++0x, this
 ** can be removed in favor of (standard-provided) N-ary tuples.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__NTUPLE_H
#define __CVC4__NTUPLE_H

namespace CVC4 {

template <class T1, class T2, class T3>
class triple {
public:
  T1 first;
  T2 second;
  T3 third;
};

template <class T1, class T2, class T3>
inline triple<T1, T2, T3>
make_triple(const T1& t1, const T2& t2, const T3& t3) {
  return triple<T1, T2, T3>(t1, t2, t3);
}

template <class T1, class T2, class T3, class T4>
class quad {
public:
  T1 first;
  T2 second;
  T3 third;
  T4 fourth;
};

template <class T1, class T2, class T3, class T4>
inline quad<T1, T2, T3, T4>
make_quad(const T1& t1, const T2& t2, const T3& t3, const T4& t4) {
  return quad<T1, T2, T3, T4>(t1, t2, t3, t4);
}

}/* CVC4 namespace */

#endif /* __CVC4__NTUPLE_H */

/*********************                                                        */
/*! \file stacking_vector.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Backtrackable vector using an undo stack
 **
 ** Backtrackable vector using an undo stack rather than storing items in
 ** a CDVector<>.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__STACKING_VECTOR_H
#define __CVC4__CONTEXT__STACKING_VECTOR_H

#include <utility>
#include <vector>

#include "context/cdo.h"

namespace CVC4 {
namespace context {

template <class T>
class StackingVector : context::ContextNotifyObj {
  /** Our underlying map type. */
  typedef std::vector<T> VectorType;

  /** Our map of indices to their values. */
  VectorType d_map;

  /** Our undo stack for changes made to d_map. */
  std::vector<std::pair<size_t, T> > d_trace;

  /** Our current offset in the d_trace stack (context-dependent). */
  context::CDO<size_t> d_offset;

public:
  typedef typename VectorType::const_iterator const_iterator;

  StackingVector(context::Context* ctxt) :
    context::ContextNotifyObj(ctxt),
    d_offset(ctxt, 0) {
  }

  ~StackingVector() throw() { }

  /**
   * Return a value from the vector.  If n is not a key in
   * the map, this function returns a default-constructed T.
   */
  T operator[](size_t n) const {
    return n < d_map.size() ? d_map[n] : T();
  }
  //T& operator[](ArgType n) { return d_map[n]; }// not permitted--bypasses set() logic

  /**
   * Set the value in the key-value map for Node n to newValue.
   */
  void set(size_t n, const T& newValue);

  /**
   * Called by the Context when a pop occurs.  Cancels everything to the
   * current context level.  Overrides ContextNotifyObj::notify().
   */
  void notify();

};/* class StackingVector<> */

template <class T>
void StackingVector<T>::set(size_t n, const T& newValue) {
  Trace("sv") << "SV setting " << n << " : " << newValue << " @ " << d_trace.size() << std::endl;
  if(n >= d_map.size()) {
    d_map.resize(n + 1);
  }
  T& ref = d_map[n];
  d_trace.push_back(std::make_pair(n, T(ref)));
  d_offset = d_trace.size();
  ref = newValue;
}

template <class T>
void StackingVector<T>::notify() {
  Trace("sv") << "SV cancelling : " << d_offset << " < " << d_trace.size() << " ?" << std::endl;
  while(d_offset < d_trace.size()) {
    std::pair<size_t, T> p = d_trace.back();
    d_map[p.first] = p.second;
    d_trace.pop_back();
  }
  Trace("sv") << "SV cancelling finished." << std::endl;
}

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /*__CVC4__CONTEXT__STACKING_VECTOR_H */

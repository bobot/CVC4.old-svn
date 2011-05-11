/*********************                                                        */
/*! \file generalized_vector.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once

#include <vector>

namespace CVC4 {

/**
 * Simple encapsulation of a vector with that can have negative indices. Any range of indices must always contain
 * either -1 or 0. Valid ranges are for example [-5:-1], [-1:1], [0:100], but not [-5,-2] or [1:100]. The push_front
 * starts pushing at index -1, -2, ..., and push_back is the same as the standard vector, i.e. 0, 1, ...
 */
template<typename value_type, typename _Alloc = std::allocator<value_type> >
class gvector {

  typedef std::vector<value_type, _Alloc> vector_type;

  vector_type d_positive;
  vector_type d_negative;

public:

  typedef typename vector_type::reference reference;
  typedef typename vector_type::const_reference const_reference;

  size_t size() const {
    return d_positive.size() + d_negative.size();
  }

  size_t positive_size() const {
    return d_positive.size();
  }

  size_t negative_size() const {
    return d_negative.size();
  }

  void push_back(const value_type& x) {
    d_positive.push_back(x);
  }

  void pop_back() {
    d_positive.pop_back();
  }

  void push_front(const value_type& x) {
    d_negative.push_back(x);
  }

  void pop_front() {
    d_negative.pop_front();
  }

  reference operator[](ssize_t index) {
    if (index < 0) {
      return d_negative[-index-1];
    } else {
      return d_positive[index];
    }
  }

  const_reference operator[](ssize_t index) const {
    if (index < 0) {
      return d_negative[-index-1];
    } else {
      return d_positive[index];
    }
  }

  reference back() {
    return d_positive.back();
  }

  const_reference back() const {
    return d_positive.back();
  }

  reference front() {
    return d_negative.back();
  }

  const_reference front() const {
    return d_negative.back();
  }
};

} // Namespace CVC4

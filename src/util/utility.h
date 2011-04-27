/*********************                                                        */
/*! \file utility.h
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
 ** \brief Some standard STL-related utility functions for CVC4
 **
 ** Some standard STL-related utility functions for CVC4.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTILITY_H
#define __CVC4__UTILITY_H

#include <utility>
#include <functional>

namespace CVC4 {


/**
 * Like std::equal_to<>, but tests equality between the first element
 * of a pair and an element.
 */
template <class T, class U>
struct first_equal_to : std::binary_function<std::pair<T, U>, T, bool> {
  bool operator()(const std::pair<T, U>& pr, const T& x) const {
    return pr.first == x;
  }
};/* struct first_equal_to<T> */


/**
 * Like std::equal_to<>, but tests equality between the second element
 * of a pair and an element.
 */
template <class T, class U>
struct second_equal_to : std::binary_function<std::pair<T, U>, U, bool> {
  bool operator()(const std::pair<T, U>& pr, const U& x) const {
    return pr.second == x;
  }
};/* struct first_equal_to<T> */


}/* CVC4 namespace */

#endif /* __CVC4__UTILITY_H */

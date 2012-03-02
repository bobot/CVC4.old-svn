/*********************                                                        */
/*! \file ascription_type.h
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
 ** \brief A class representing a type ascription
 **
 ** A class representing a parameter for the type ascription operator.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__ASCRIPTION_TYPE_H
#define __CVC4__ASCRIPTION_TYPE_H

#include "expr/type.h"

namespace CVC4 {

/**
 * A class used to parameterize a type ascription.  For example,
 * "nil :: list<nat>" is an expression of kind APPLY_TYPE_ASCRIPTION.
 * The parameter is an ASCRIPTION_TYPE-kinded expression with an
 * AscriptionType payload.  (Essentially, all of this is a way to
 * coerce a Type into the expression tree.)
 */
class CVC4_PUBLIC AscriptionType {
  Type d_type;
public:
  AscriptionType(Type t) throw() : d_type(t) {}
  Type getType() const throw() { return d_type; }
  bool operator==(const AscriptionType& other) const throw() {
    return d_type == other.d_type;
  }
  bool operator!=(const AscriptionType& other) const throw() {
    return d_type != other.d_type;
  }
};/* class AscriptionType */

/**
 * A hash strategy for type ascription operators.
 */
struct CVC4_PUBLIC AscriptionTypeHashStrategy {
  static inline size_t hash(const AscriptionType& at) {
    return TypeHashFunction()(at.getType());
  }
};/* struct AscriptionTypeHashStrategy */

/** An output routine for AscriptionTypes */
inline std::ostream& operator<<(std::ostream& out, AscriptionType at) {
  out << at.getType();
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__ASCRIPTION_TYPE_H */

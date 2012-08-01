/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Enumerators for rationals and integers
 **
 ** Enumerators for rationals and integers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H

#include "util/integer.h"
#include "util/rational.h"
#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace arith {

class RationalEnumerator : public TypeEnumeratorBase<RationalEnumerator> {
  Rational d_rat;

public:

  RationalEnumerator(TypeNode type) throw(AssertionException) :
    TypeEnumeratorBase<RationalEnumerator>(type),
    d_rat(0) {
    Assert(type.getKind() == kind::TYPE_CONSTANT &&
           type.getConst<TypeConstant>() == REAL_TYPE);
  }

  Node operator*() throw() {
    return NodeManager::currentNM()->mkConst(d_rat);
  }

  RationalEnumerator& operator++() throw() {
    // sequence is 0, then diagonal with negatives interleaved
    // ( 0, 1/1, -1/1, 2/1, -2/1, 1/2, -1/2, 3/1, -3/1, 1/3, -1/3,
    // 4/1, -4/1, 3/2, -3/2, 2/3, -2/3, 1/4, -1/4, ...)
    if(d_rat == 0) {
      d_rat = 1;
    } else if(d_rat < 0) {
      d_rat = -d_rat;
      Integer num = d_rat.getNumerator();
      Integer den = d_rat.getDenominator();
      do {
        num -= 1;
        den += 1;
        if(num == 0) {
          num = den;
          den = 1;
        }
        d_rat = Rational(num, den);
      } while(d_rat.getNumerator() != num);
    } else {
      d_rat = -d_rat;
    }
    return *this;
  }

};/* class RationalEnumerator */

class IntegerEnumerator : public TypeEnumeratorBase<IntegerEnumerator> {
  Integer d_int;

public:

  IntegerEnumerator(TypeNode type) throw(AssertionException) :
    TypeEnumeratorBase<IntegerEnumerator>(type),
    d_int(0) {
    Assert(type.getKind() == kind::TYPE_CONSTANT &&
           type.getConst<TypeConstant>() == INTEGER_TYPE);
  }

  Node operator*() throw() {
    return NodeManager::currentNM()->mkConst(Rational(d_int));
  }

  IntegerEnumerator& operator++() throw() {
    // sequence is 0, 1, -1, 2, -2, 3, -3, ...
    if(d_int <= 0) {
      d_int = -d_int + 1;
    } else {
      d_int = -d_int;
    }
    return *this;
  }

};/* class IntegerEnumerator */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H */

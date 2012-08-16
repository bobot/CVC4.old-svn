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
 ** \brief An enumerator for Booleans
 **
 ** An enumerator for Booleans.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BOOLEANS__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__BOOLEANS__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace booleans {

class BooleanEnumerator : public TypeEnumeratorBase<BooleanEnumerator> {
  enum { FALSE, TRUE, DONE } d_value;

public:

  BooleanEnumerator(TypeNode type) :
    TypeEnumeratorBase(type),
    d_value(FALSE) {
    Assert(type.getKind() == kind::TYPE_CONSTANT &&
           type.getConst<TypeConstant>() == BOOLEAN_TYPE);
  }

  Node operator*() throw(NoMoreValuesException) {
    switch(d_value) {
    case FALSE:
      return NodeManager::currentNM()->mkConst(false);
    case TRUE:
      return NodeManager::currentNM()->mkConst(true);
    default:
      throw NoMoreValuesException(getType());
    }
  }

  BooleanEnumerator& operator++() throw() {
    // sequence is FALSE, TRUE
    if(d_value == FALSE) {
      d_value = TRUE;
    } else {
      d_value = DONE;
    }
    return *this;
  }

};/* class BooleanEnumerator */

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BOOLEANS__TYPE_ENUMERATOR_H */

/*********************                                                        */
/*! \file theory_quantifiers_type_rules.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of quantifiers
 **
 ** Theory of quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H
#define __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H

#include "util/matcher.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct QuantifierForallTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Debug("typecheck-q") << "type check for fa " << n << std::endl;
    Assert(n.getKind() == kind::FORALL && n.getNumChildren()>0 );
    if( check ){
      if( n[ n.getNumChildren() - 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of universal quantifier is not boolean");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierForallTypeRule */

struct QuantifierExistsTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Debug("typecheck-q") << "type check for ex " << n << std::endl;
    Assert(n.getKind() == kind::EXISTS && n.getNumChildren()>0 );
    if( check ){
      if( n[ n.getNumChildren() - 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of existential quantifier is not boolean");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierExistsTypeRule */

struct QuantifierCounterexampleTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Debug("typecheck-q") << "type check for ce " << n << std::endl;
    Assert(n.getKind() == kind::NO_COUNTEREXAMPLE && n.getNumChildren()==1 && 
      ( n[0].getKind()==kind::FORALL || ( n[0].getKind()==kind::NOT && n[0][0].getKind()==kind::EXISTS )) );
    if( check ){
      if( n[ 0 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of counterexample is not boolean");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierCounterexampleTypeRule */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H */

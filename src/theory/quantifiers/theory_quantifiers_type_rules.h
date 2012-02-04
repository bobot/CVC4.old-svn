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
      if( n[ 0 ].getType(check)!=nodeManager->boundVarListType() ){
        throw TypeCheckingExceptionPrivate(n, "first argument of universal quantifier is not bound var list");
      }
      if( n[ 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of universal quantifier is not boolean");
      }
      if( n.getNumChildren()==3 && n[2].getType(check)!=nodeManager->instPatternListType() ){
        throw TypeCheckingExceptionPrivate(n, "third argument of universal quantifier is not instantiation pattern list");
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
      if( n[ 0 ].getType(check)!=nodeManager->boundVarListType() ){
        throw TypeCheckingExceptionPrivate(n, "first argument of existential quantifier is not bound var list");
      }
      if( n[ 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of existential quantifier is not boolean");
      }
      if( n.getNumChildren()==3 && n[2].getType(check)!=nodeManager->instPatternListType() ){
        throw TypeCheckingExceptionPrivate(n, "third argument of existential quantifier is not instantiation pattern list");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierExistsTypeRule */

struct QuantifierNoCounterexampleTypeRule {
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
};/* struct QuantifierNoCounterexampleTypeRule */

struct QuantifierBoundVarListTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::BOUND_VAR_LIST );
    if( check ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( n[i].getKind()!=kind::VARIABLE ){
          throw TypeCheckingExceptionPrivate(n, "argument of bound var list is not variable");
        }
      }
    }
    return nodeManager->boundVarListType();
  }
};/* struct QuantifierBoundVarListTypeRule */

struct QuantifierInstPatternTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::INST_PATTERN );
    return nodeManager->instPatternType();
  }
};/* struct QuantifierInstPatternTypeRule */


struct QuantifierInstPatternListTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::INST_PATTERN_LIST );
    if( check ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( n[i].getKind()!=kind::INST_PATTERN ){
          throw TypeCheckingExceptionPrivate(n, "argument of inst pattern list is not inst pattern");
        }
      }
    }
    return nodeManager->instPatternListType();
  }
};/* struct QuantifierInstPatternListTypeRule */


struct QuantifierRewriteRuleRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::REWRITE_RULE );
    if( check ){
      if( n[ 0 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "guard of rewrite rule is not boolean");
      }
      if( n[1].getType(check)!=n[2].getType(check) ){
        throw TypeCheckingExceptionPrivate(n, "terms of rewrite rule are not equal");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierRewriteRuleRule */

struct QuantifierReductionRuleRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::REDUCTION_RULE );
    if( check ){
      if( n[ 0 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "guard of reduction rule is not boolean");
      }
      if( n[ 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "head of reduction rule is not boolean");
      }
      if( n[ 2 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of reduction rule is not boolean");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierReductionRuleRule */

struct QuantifierDeductionRuleRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::DEDUCTION_RULE );
    if( check ){
      if( n[ 0 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "guard of deduction rule is not boolean");
      }
      if( n[ 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "head of deduction rule is not boolean");
      }
      if( n[ 2 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of deduction rule is not boolean");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct QuantifierDeductionRuleRule */


}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_TYPE_RULES_H */

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_TYPE_RULES_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_TYPE_RULES_H

#include "node_manager.h"

namespace CVC4 {
namespace theory {
namespace rewriterules {

class RewriteRuleTypeRule {
public:

  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of rewriterules.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check)
    throw(TypeCheckingExceptionPrivate) {
    Debug("typecheck-r") << "type check for rr " << n << std::endl;
    Assert(n.getKind() == kind::REWRITE_RULE && n.getNumChildren()==3 );
    if( check ){
      if( n[ 0 ].getType(check)!=nodeManager->boundVarListType() ){
        throw TypeCheckingExceptionPrivate(n,
                     "first argument of rewrite rule is not bound var list");
      }
      if( n[ 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n,
                     "guard of rewrite rule is not an actual guard");
      }
      if( n[2].getType(check) !=
          TypeNode(nodeManager->mkTypeConst<TypeConstant>(RRHB_TYPE))){
        throw TypeCheckingExceptionPrivate(n,
                     "not a correct rewrite rule");
      }
    }
    return nodeManager->booleanType();
  }
};/* class RewriterulesTypeRule */


class RRRewriteTypeRule {
public:

  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::RR_REWRITE );
    if( check ){
      if( n[0].getType(check)!=n[1].getType(check) ){
        throw TypeCheckingExceptionPrivate(n,
                     "terms of rewrite rule are not equal");
      }
      if( n.getNumChildren() == 3 && n[2].getType(check)!=nodeManager->instPatternListType() ){
        throw TypeCheckingExceptionPrivate(n, "third argument of rewrite rule is not instantiation pattern list");
      }
    }
    return TypeNode(nodeManager->mkTypeConst<TypeConstant>(RRHB_TYPE));
  }
};/* struct QuantifierReductionRuleRule */

class RRRedDedTypeRule {
public:

  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::RR_REDUCTION ||
           n.getKind() == kind::RR_DEDUCTION );
    if( check ){
      if( n[ 0 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "head of reduction rule is not boolean");
      }
      if( n[ 1 ].getType(check)!=nodeManager->booleanType() ){
        throw TypeCheckingExceptionPrivate(n, "body of reduction rule is not boolean");
      }
      if( n.getNumChildren() == 3 && n[2].getType(check)!=nodeManager->instPatternListType() ){
        throw TypeCheckingExceptionPrivate(n, "third argument of rewrite rule is not instantiation pattern list");
      }
    }
    return TypeNode(nodeManager->mkTypeConst<TypeConstant>(RRHB_TYPE));
  }
};/* struct QuantifierReductionRuleRule */

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_TYPE_RULES_H */

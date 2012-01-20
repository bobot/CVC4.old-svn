/*********************                                                        */
/*! \file theory_definitions_type_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add brief comments here ]]
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DEFINITIONS__THEORY_DEFINITIONS_TYPE_RULES_H
#define __CVC4__THEORY__DEFINITIONS__THEORY_DEFINITIONS_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace definitions {

class DefinitionsTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate) {
    /* Kind should always be definition */
    Assert(n.getKind() == Kind::DEFINITION);

    /* Also guarenteed that it's arity 2 (from the kinds file) */
    Assert(n.getNumChildren() == 2);


    /* This works
     *    n[0].getType().getKind() == Kind::Boolean;
     *    n[0].getType() == nodeManager->booleanType();     // Because they are singletons
     * but isn't as good because of subtyping
     */

    if (n[0].getType().isBoolean()) {
      if (n[1].getType().isBoolean()) {
	/* Return type as the check is bottom up */
	return nodeManager->booleanType();

      } else {
	std::stringstream ss;
	ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
	   << "Right hand side of definition " << n
	   << " is not Boolean" << std::endl;
	throw TypeCheckingExceptionPrivate(n, ss.str());      
      }
      
    } else {
      std::stringstream ss;
      ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
	 << "Left hand side of definition " << n
	 << " is not Boolean" << std::endl;
      throw TypeCheckingExceptionPrivate(n, ss.str());      
    }

    Unreachable();
  }
};/* class DefinitionsTypeRule */

}/* CVC4::theory::definitions namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DEFINITIONS__THEORY_DEFINITIONS_TYPE_RULES_H */

/*********************                                                        */
/*! \file theory_builtin_type_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Type rules for the builtin theory
 **
 ** Type rules for the builtin theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H
#define __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "expr/expr.h"

#include <sstream>

namespace CVC4 {
namespace theory {
namespace builtin {

class ApplyTypeRule {
  public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate) {
    TNode f = n.getOperator();
    TypeNode fType = f.getType(check);
    if( !fType.isFunction() && n.getNumChildren() > 0 ) {
      throw TypeCheckingExceptionPrivate(n, "operator does not have function type");
    }
    if( check ) {
      if(fType.isFunction()) {
        if(n.getNumChildren() != fType.getNumChildren() - 1) {
          throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the function type");
        }
        TNode::iterator argument_it = n.begin();
        TNode::iterator argument_it_end = n.end();
        TypeNode::iterator argument_type_it = fType.begin();
        for(; argument_it != argument_it_end; ++argument_it, ++argument_type_it) {
          if((*argument_it).getType() != *argument_type_it) {
            std::stringstream ss;
            ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage));
            ss << "argument types do not match the function type:\n"
               << "argument:  " << *argument_it << "\n"
               << "has type:  " << (*argument_it).getType() << "\n"
               << "not equal: " << *argument_type_it;
            throw TypeCheckingExceptionPrivate(n, ss.str());
          }
        }
      } else {
        if( n.getNumChildren() > 0 ) {
          throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the function type");
        }
      }
    }
    return fType.isFunction() ? fType.getRangeType() : fType;
  }
};/* class ApplyTypeRule */


class EqualityTypeRule {
  public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) throw (TypeCheckingExceptionPrivate) {
    TypeNode booleanType = nodeManager->booleanType();

    if( check ) {
      TypeNode lhsType = n[0].getType(check);
      TypeNode rhsType = n[1].getType(check);

      if ( lhsType != rhsType ) {
        std::stringstream ss;
        ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage));
        ss << "Types do not match in equation ";
        ss << "[" << lhsType << "<>" << rhsType << "]";

        throw TypeCheckingExceptionPrivate(n, ss.str());
      }

      if ( lhsType == booleanType ) {
        throw TypeCheckingExceptionPrivate(n, "equality between two boolean terms (use IFF instead)");
      }
    }
    return booleanType;
  }
};/* class EqualityTypeRule */


class DistinctTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    if( check ) {
      TNode::iterator child_it = n.begin();
      TNode::iterator child_it_end = n.end();
      TypeNode firstType = (*child_it).getType(check);
      for (++child_it; child_it != child_it_end; ++child_it) {
        if ((*child_it).getType() != firstType) {
          throw TypeCheckingExceptionPrivate(n, "Not all arguments are of the same type");
        }
      }
    }
    return nodeManager->booleanType();
  }
};/* class DistinctTypeRule */


class TupleTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    std::vector<TypeNode> types;
    for(TNode::iterator child_it = n.begin(), child_it_end = n.end();
        child_it != child_it_end;
        ++child_it) {
      types.push_back((*child_it).getType(check));
    }
    return nodeManager->mkTupleType(types);
  }
};/* class TupleTypeRule */


}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_TYPE_RULES_H */

/*********************                                                        */
/*! \file type_checker.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A type checker
 **
 ** A type checker.
 **/

#include "cvc4_private.h"

// ordering dependence
#include "expr/node.h"

#ifndef __CVC4__EXPR__TYPE_CHECKER_H
#define __CVC4__EXPR__TYPE_CHECKER_H

namespace CVC4 {
namespace expr {

class TypeChecker {
public:

  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check = false)
    throw (TypeCheckingExceptionPrivate, AssertionException);

  static bool computeIsConst(NodeManager* nodeManager, TNode n)
    throw (AssertionException);

};/* class TypeChecker */

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__TYPE_CHECKER_H */

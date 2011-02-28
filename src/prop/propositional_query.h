/*********************                                                        */
/*! \file propositional_query.h
 **
 ** \brief PropositionalQuery is a way for parts of CVC4 to do quick purely
 ** propositional satisfiability or validity checks on a Node.
 ** These checks have no theory reasoning, and handle atoms as propositional
 ** variables.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROPOSITIONAL_QUERY_H
#define __CVC4__PROPOSITIONAL_QUERY_H

#include "expr/node.h"
#include "util/result.h"

namespace CVC4 {
namespace prop {

/**
 * PropositionalQuery is a way for parts of CVC4 to do quick purely
 * propositional satisfiability or validity checks on a Node.
 */
class PropositionalQuery {
public:

  /**
   * Returns whether a node q is propositionally satisfiable.
   *
   * @params q Node to be checked for satisfiability.
   * @params e A number representing the effort to use between 0 (minimum effort),
   *  and 1 (maximum effort).
   * @precondition q is a ground formula.
   * @precondition effort is between 0 and 1.
   */
  static Result isSatisfiable(TNode q);

  /**
   * Returns whether a node q is a propositional tautology.
   *
   * @params q Node to be checked for satisfiability.
   * @params e A number representing the effort to use between 0 (minimum effort),
   *  and 1 (maximum effort).
   * @precondition q is a ground formula.
   * @precondition effort is between 0 and 1.
   */
  static Result isTautology(TNode q);

};/* class PropositionalQuery */

}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PROPOSITIONAL_QUERY_H */

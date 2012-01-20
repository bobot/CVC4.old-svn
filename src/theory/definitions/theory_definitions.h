/*********************                                                        */
/*! \file theory_definitions.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is a basic implementation of the Theory of Uninterpreted Functions
 ** with Equality.
 **
 ** This is a basic implementation of the Theory of Uninterpreted Functions
 ** with Equality.  It is based on the Nelson-Oppen algorithm given in
 ** "Fast Decision Procedures Based on Congruence Closure"
 **  (http://portal.acm.org/ft_gateway.cfm?id=322198&type=pdf)
 ** This has been extended to work in a context-dependent way.
 ** This interacts heavily with the data-structures given in ecdata.h .
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DEFINITIONS__THEORY_DEFINITIONS_H
#define __CVC4__THEORY__DEFINITIONS__THEORY_DEFINITIONS_H

#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/theory.h"

#include "context/context.h"
#include "context/cdo.h"
#include "context/cdlist.h"
#include "theory/definitions/theory_definitions.h"

namespace CVC4 {
namespace theory {
namespace definitions {

class TheoryDefinitions : public Theory {

private:


public:

  /** Constructs a new instance of TheoryDefinitions w.r.t. the provided context.*/
  TheoryDefinitions(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation);

  /** Destructor for the TheoryDefinitions object. */
  ~TheoryDefinitions();

  /**
   * Registers a previously unseen [in this context] node n.
   * For TheoryDefinitions, this sets up and maintains invaraints about
   * equivalence class data-structures.
   *
   * Overloads a void registerTerm(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void registerTerm(TNode n);

  /**
   * Currently this does nothing.
   *
   * Overloads a void preRegisterTerm(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void preRegisterTerm(TNode n);

  /**
   * Checks whether the set of literals provided to the theory is consistent.
   *
   * If this is called at any effort level, it computes the congruence closure
   * of all of the positive literals in the context.
   *
   * If this is called at full effort it checks if any of the negative literals
   * are inconsistent with the congruence closure.
   *
   * Overloads  void check(Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void check(Effort level);

  void presolve() {
    // do nothing
  }

  /**
   * Propagates theory literals. Currently does nothing.
   *
   * Overloads void propagate(Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void propagate(Effort level) {}

  /**
   * Explains a previously reported conflict. Currently does nothing.
   *
   * Overloads void explain(TNode n, Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void explain(TNode n) {}

  /**
   * Get a theory value.
   *
   * Overloads Node getValue(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  Node getValue(TNode n) {
    Unimplemented("TheoryDefinitions doesn't support model generation");
  }

  std::string identify() const { return std::string("TheoryDefinitions"); }

private:

};/* class TheoryDefinitions */

}/* CVC4::theory::definitions namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DEFINITIONS__THEORY_DEFINITIONS_H */

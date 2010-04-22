/*********************                                                        */
/** theory_arith.h
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Arithmetic theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__THEORY_ARITH_H
#define __CVC4__THEORY__ARITH__THEORY_ARITH_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"

#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArith : public Theory {
private:
  context::CDList<Node> d_diseq;
  Tableau d_tableau;
public:
  TheoryArith(context::Context* c, OutputChannel& out) :
    Theory(c, out), d_diseq(c)
  {}
  Node canonize(TNode n);

  void preRegisterTerm(TNode n) { Unimplemented(); }
  void registerTerm(TNode n);
  void check(Effort e);
  void propagate(Effort e) { Unimplemented(); }
  void explain(TNode n, Effort e) { Unimplemented(); }

  static Node s_TRUE_NODE;
  static Node s_FALSE_NODE;
  static Rational s_ZERO;
  static Rational s_ONE;
  static Rational s_NEGATIVE_ONE;

private:
  void AssertLower(TNode n);
  void AssertUpper(TNode n);
  void update(TNode x_i, DeltaRational& v);
  void pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v);
  TNode updateInconsistentVars();


};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */

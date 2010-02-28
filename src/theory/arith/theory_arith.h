/*********************                                                        */
/** theory_arith.h
 ** Original author: mdeters
 ** Major contributors: none
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

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArith : public TheoryImpl<TheoryArith> {
public:
  TheoryArith(context::Context* c, OutputChannel& out) :
    TheoryImpl<TheoryArith>(c, out) {
  }

  void preRegisterTerm(TNode n) { Unimplemented("preRegisterTerm"); }
  void registerTerm(TNode n) { Unimplemented("registerTerm"); }
  void check(Effort e) { Unimplemented("check"); }
  void propagate(Effort e) { Unimplemented("propagate"); }
  void explain(TNode n, Effort e) { Unimplemented("explain"); }
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */

/*********************                                                        */
/*! \file theory_uf_instantiator.h
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
 ** \brief Theory uf instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_INSTANTIATOR_H
#define __CVC4__THEORY_UF_INSTANTIATOR_H

#include "theory/instantiation_engine.h"

namespace CVC4 {
namespace theory {
namespace uf {
namespace morgan {

class TheoryUfInstantiatior : public TheoryInstantiatior{
protected:
  /** reference to the theory that it looks at */
  Theory* d_th;
public:
  TheoryUfInstantiatior(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th);
  ~TheoryUfInstantiatior() {}

  bool doInstantiation( OutputChannel* out );
  Theory* getTheory() { return d_th; }
};/* class TheoryUfInstantiatior */

}
}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

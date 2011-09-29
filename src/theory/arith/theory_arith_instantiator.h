/*********************                                                        */
/*! \file instantiator_arith_instantiator.h
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
 ** \brief instantiator_arith_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATOR_ARITH_H
#define __CVC4__INSTANTIATOR_ARITH_H

#include "theory/instantiation_engine.h"

namespace CVC4 {
namespace theory {
namespace arith {

class InstantiatorTheoryArith : public Instantiator{
  friend class InstantiationEngine;
public:
  InstantiatorTheoryArith(context::Context* c, InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryArith() {}

  /** check function, assertion is asserted to theory */
  void check( Node assertion );
  /**  reset instantiation */
  void resetInstantiation();
  /** prepare instantiation method
    * post condition: set d_solved_ic and d_lemmas fields */
  bool doInstantiation( int effort );
};/* class Instantiatior */

}
}
}

#endif
/*********************                                                        */
/*! \file instantiator_quantifiers_instantiator.h
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
 ** \brief instantiator_quantifiers_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATOR_QUANTIFIERS_H
#define __CVC4__INSTANTIATOR_QUANTIFIERS_H

#include "theory/instantiation_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstantiatorTheoryQuantifiers : public Instantiator{
  friend class InstantiationEngine;
public:
  InstantiatorTheoryQuantifiers(context::Context* c, InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryQuantifiers() {}

  /** check function, assertion is asserted to theory */
  void check( Node assertion );
  /**  reset instantiation */
  void resetInstantiation();
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryQuantifiers"); }
private:
  /** process at effort */
  void process( Node f, int effort );
};/* class InstantiatiorTheoryArith  */

}
}
}

#endif
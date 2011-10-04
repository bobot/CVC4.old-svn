/*********************                                                        */
/*! \file instantiator_default.h
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
 ** \brief instantiator_default
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATOR_DEFAULT_H
#define __CVC4__INSTANTIATOR_DEFAULT_H

#include "theory/instantiation_engine.h"

namespace CVC4 {
namespace theory {

class InstantiatorDefault : public Instantiator{
  friend class InstantiationEngine;
public:
  InstantiatorDefault(context::Context* c, InstantiationEngine* ie, Theory* th);
  ~InstantiatorDefault() {}
  /** check function, assertion is asserted to theory */
  void check( Node assertion );
  /** process quantifier */
  void process( Node f, int effort );
  /** identify */
  std::string identify() const { return std::string("InstantiatorDefault"); }
};/* class Instantiatior */


}
}

#endif
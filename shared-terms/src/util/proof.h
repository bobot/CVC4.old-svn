/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PROOF_H
#define __CVC4__PROOF_H

#include <iostream>

namespace CVC4 {

class CVC4_PUBLIC Proof {
public:
  virtual void toStream(std::ostream& out) = 0;
};/* class Proof */

}/* CVC4 namespace */

#endif /* __CVC4__PROOF_H */
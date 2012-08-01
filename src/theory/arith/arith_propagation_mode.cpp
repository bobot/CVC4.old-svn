/*********************                                                        */
/*! \file arith_propagation_mode.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
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

#include "theory/arith/arith_propagation_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, ArithPropagationMode mode) {
  switch(mode) {
  case NO_PROP:
    out << "NO_PROP";
    break;
  case UNATE_PROP:
    out << "UNATE_PROP";
    break;
  case BOUND_INFERENCE_PROP:
    out << "BOUND_INFERENCE_PROP";
    break;
  case BOTH_PROP:
    out << "BOTH_PROP";
    break;
  default:
    out << "ArithPropagationMode!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */


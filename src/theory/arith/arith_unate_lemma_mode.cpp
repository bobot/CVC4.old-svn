/*********************                                                        */
/*! \file arith_unate_lemma_mode.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/arith_unate_lemma_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, ArithUnateLemmaMode mode) {
  switch(mode) {
  case NO_PRESOLVE_LEMMAS:
    out << "NO_PRESOLVE_LEMMAS";
    break;
  case INEQUALITY_PRESOLVE_LEMMAS:
    out << "INEQUALITY_PRESOLVE_LEMMAS";
    break;
  case EQUALITY_PRESOLVE_LEMMAS:
    out << "EQUALITY_PRESOLVE_LEMMAS";
    break;
  case ALL_PRESOLVE_LEMMAS:
    out << "ALL_PRESOLVE_LEMMAS";
    break;
  default:
    out << "ArithUnateLemmaMode!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */


/*********************                                                        */
/*! \file modes.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
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

#include <iostream>
#include "theory/quantifiers/modes.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, theory::quantifiers::InstWhenMode mode) {
  switch(mode) {
  case theory::quantifiers::INST_WHEN_PRE_FULL:
    out << "INST_WHEN_PRE_FULL";
    break;
  case theory::quantifiers::INST_WHEN_FULL:
    out << "INST_WHEN_FULL";
    break;
  case theory::quantifiers::INST_WHEN_FULL_LAST_CALL:
    out << "INST_WHEN_FULL_LAST_CALL";
    break;
  case theory::quantifiers::INST_WHEN_LAST_CALL:
    out << "INST_WHEN_LAST_CALL";
    break;
  default:
    out << "InstWhenMode!UNKNOWN";
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, theory::quantifiers::LiteralMatchMode mode) {
  switch(mode) {
  case theory::quantifiers::LITERAL_MATCH_NONE:
    out << "LITERAL_MATCH_NONE";
    break;
  case theory::quantifiers::LITERAL_MATCH_PREDICATE:
    out << "LITERAL_MATCH_PREDICATE";
    break;
  case theory::quantifiers::LITERAL_MATCH_EQUALITY:
    out << "LITERAL_MATCH_EQUALITY";
    break;
  default:
    out << "LiteralMatchMode!UNKNOWN";
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, theory::quantifiers::AxiomInstMode mode) {
  switch(mode) {
  case theory::quantifiers::AXIOM_INST_MODE_DEFAULT:
    out << "AXIOM_INST_MODE_DEFAULT";
    break;
  case theory::quantifiers::AXIOM_INST_MODE_TRUST:
    out << "AXIOM_INST_MODE_TRUST";
    break;
  case theory::quantifiers::AXIOM_INST_MODE_PRIORITY:
    out << "AXIOM_INST_MODE_PRIORITY";
    break;
  default:
    out << "AxiomInstMode!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */


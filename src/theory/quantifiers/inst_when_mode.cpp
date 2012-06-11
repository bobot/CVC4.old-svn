#include <iostream>
#include "theory/quantifiers/inst_when_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, theory::quantifiers::InstWhenMode mode) {
  switch(mode) {
  case INST_WHEN_PRE_FULL:
    out << "INST_WHEN_PRE_FULL";
    break;
  case INST_WHEN_FULL:
    out << "INST_WHEN_FULL";
    break;
  case INST_WHEN_FULL_LAST_CALL:
    out << "INST_WHEN_FULL_LAST_CALL";
    break;
  case INST_WHEN_LAST_CALL:
    out << "INST_WHEN_LAST_CALL";
    break;
  default:
    out << "InstWhenMode!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */


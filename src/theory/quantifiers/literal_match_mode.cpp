#include <iostream>
#include "theory/quantifiers/literal_match_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, theory::quantifiers::LiteralMatchMode mode) {
  switch(mode) {
  case LITERAL_MATCH_NONE:
    out << "LITERAL_MATCH_NONE";
    break;
  case LITERAL_MATCH_PREDICATE:
    out << "LITERAL_MATCH_PREDICATE";
    break;
  case LITERAL_MATCH_EQUALITY:
    out << "LITERAL_MATCH_EQUALITY";
    break;
  default:
    out << "LiteralMatchMode!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */

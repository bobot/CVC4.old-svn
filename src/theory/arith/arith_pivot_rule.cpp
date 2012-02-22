#include "theory/arith/arith_pivot_rule.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, ArithPivotRule rule) {
  switch(rule) {
  case MINIMUM:
    out << "MINIMUM";
    break;
  case BREAK_TIES:
    out << "BREAK_TIES";
    break;
  case MAXIMUM:
    out << "MAXIMUM";
    break;
  default:
    out << "ArithPivotRule!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */


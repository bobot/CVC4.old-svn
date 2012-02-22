#include "smt/simplification_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, SimplificationMode mode) {
  switch(mode) {
  case SIMPLIFICATION_MODE_INCREMENTAL:
    out << "SIMPLIFICATION_MODE_INCREMENTAL";
    break;
  case SIMPLIFICATION_MODE_BATCH:
    out << "SIMPLIFICATION_MODE_BATCH";
    break;
  case SIMPLIFICATION_MODE_NONE:
    out << "SIMPLIFICATION_MODE_NONE";
    break;
  default:
    out << "SimplificationMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}

}/* CVC4 namespace */

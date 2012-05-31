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


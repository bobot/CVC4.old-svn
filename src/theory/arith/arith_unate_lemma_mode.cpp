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


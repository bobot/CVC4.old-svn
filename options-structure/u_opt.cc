#include "u_opt.h"
#include "options_holder.h"

namespace CVC4 {
  template <>
  heuristic_t::type&
  Options::operator[](heuristic_t) {
    return d_holder->heuristic;
  }
}


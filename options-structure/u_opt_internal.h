#pragma once

#include "options.h"
#include "u_opt.h"

namespace CVC4 {
  template <>
  heuristic_t::type&
  Options::operator[](heuristic_t);
}


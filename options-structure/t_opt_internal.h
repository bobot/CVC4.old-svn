#pragma once

#include "options.h"
#include "t_opt.h"

namespace CVC4 {
  template <>
  verbose_t::type&
  Options::operator[](verbose_t);

  template <>
  stats_t::type&
  Options::operator[](stats_t);
}


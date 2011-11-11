#pragma once

#include "options.h"

#define T_OPT_OPTIONS \
  verbose_t::type verbose; \
  stats_t::type stats;

namespace CVC4 {
  struct verbose_t { typedef bool type; };
  extern verbose_t verbose;

  struct stats_t { typedef bool type; };
  extern stats_t stats;
}


#include "t_opt_internal.h"
#include "options_holder.h"

namespace CVC4 {
  template <>
  verbose_t::type&
  Options::operator[](verbose_t) {
    return d_holder->verbose;
  }

  template <>
  stats_t::type&
  Options::operator[](stats_t) {
    return d_holder->stats;
  }
}


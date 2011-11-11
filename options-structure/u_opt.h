#pragma once

#include <iostream>
#include "options.h"

#define U_OPT_OPTIONS \
  heuristic_t::type heuristic;

namespace CVC4 {
  enum Heuristic {
    FOO, BAR, BAZ
  };
  inline std::ostream& operator<<(std::ostream& out, const Heuristic& h) {
    switch(h) {
    case FOO: out << "FOO"; break;
    case BAR: out << "BAR"; break;
    case BAZ: out << "BAZ"; break;
    default: out << "ERROR!Heuristic";
    }
    return out;
  }

  struct heuristic_t { typedef Heuristic type; };
  extern heuristic_t heuristic;
}


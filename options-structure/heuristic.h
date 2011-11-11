#pragma once

#include <iostream>

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

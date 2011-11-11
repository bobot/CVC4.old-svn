#include "u.h"
#include "options.h"
#include "u_opt.h"
#include <iostream>

using namespace std;
using namespace CVC4;

void u() {
  cout << "heuristic is " << Options::current()[heuristic] << endl;
}

void uu() {
  Options::current()[heuristic] = BAZ;
}


#include <iostream>
#include "t_options.h"
#include "u.h"

using namespace CVC4;
using namespace std;

int main() {
  cout << "verbose is " << Options::current()[verbose] << std::endl;
  cout << "stats is " << Options::current()[stats] << std::endl;
  u();

  //Options::current().set(verbose, true);
  uu();

  cout << std::endl;

  cout << "verbose is " << Options::current()[verbose] << std::endl;
  cout << "stats is " << Options::current()[stats] << std::endl;
  u();

  return 0;
}

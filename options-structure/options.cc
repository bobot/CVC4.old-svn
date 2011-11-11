#include "options.h"
#include "options_holder.h"

namespace CVC4 {
  Options Options::d_current;

  Options::Options() {
    d_holder = new options_holder();
  }
}


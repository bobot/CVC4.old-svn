#include "cvc4_public.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROPAGATION_MODE_H
#define __CVC4__THEORY__ARITH__ARITH_PROPAGATION_MODE_H

#include <iostream>

namespace CVC4 {

typedef enum {
  NO_PROP,
  UNATE_PROP,
  BOUND_INFERENCE_PROP,
  BOTH_PROP
} ArithPropagationMode;

std::ostream& operator<<(std::ostream& out, ArithPropagationMode rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_PROPAGATION_MODE_H */

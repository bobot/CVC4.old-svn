#include "cvc4_public.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PIVOT_RULE_H
#define __CVC4__THEORY__ARITH__ARITH_PIVOT_RULE_H

#include <iostream>

namespace CVC4 {

typedef enum {
  MINIMUM,
  BREAK_TIES,
  MAXIMUM
} ArithPivotRule;

std::ostream& operator<<(std::ostream& out, ArithPivotRule rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_PIVOT_RULE_H */

#include "cvc4_public.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_UNATE_LEMMA_MODE_H
#define __CVC4__THEORY__ARITH__ARITH_UNATE_LEMMA_MODE_H

#include <iostream>

namespace CVC4 {

typedef enum {
  NO_PRESOLVE_LEMMAS,
  INEQUALITY_PRESOLVE_LEMMAS,
  EQUALITY_PRESOLVE_LEMMAS,
  ALL_PRESOLVE_LEMMAS
} ArithUnateLemmaMode;

std::ostream& operator<<(std::ostream& out, ArithUnateLemmaMode rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_UNATE_LEMMA_MODE_H */

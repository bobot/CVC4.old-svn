#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_WHEN_MODE_H
#define __CVC4__THEORY__QUANTIFIERS__INST_WHEN_MODE_H

#include <iostream>

namespace CVC4 {
namespace theory {
namespace quantifiers {

typedef enum {
  /** Apply instantiation round before full effort (possibly at standard effort) */
  INST_WHEN_PRE_FULL,
  /** Apply instantiation round at full effort or above  */
  INST_WHEN_FULL,
  /** Apply instantiation round at full effort half the time, and last call always */
  INST_WHEN_FULL_LAST_CALL,
  /** Apply instantiation round at last call only */
  INST_WHEN_LAST_CALL,
} InstWhenMode;

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::quantifiers::InstWhenMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_WHEN_MODE_H */

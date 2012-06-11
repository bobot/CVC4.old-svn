#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__LITERAL_MATCH_MODE_H
#define __CVC4__THEORY__QUANTIFIERS__LITERAL_MATCH_MODE_H

#include <iostream>

namespace CVC4 {
namespace theory {
namespace quantifiers {

typedef enum {
  /** Do not consider polarity of patterns */
  LITERAL_MATCH_NONE,
  /** Consider polarity of boolean predicates only */
  LITERAL_MATCH_PREDICATE,
  /** Consider polarity of boolean predicates, as well as equalities */
  LITERAL_MATCH_EQUALITY,
} LiteralMatchMode;

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::quantifiers::LiteralMatchMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__LITERAL_MATCH_MODE_H */

/*********************                                                       */
/*! \file rewrite_engine.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: bobot
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewrite Engine classes
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_RULES_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_RULES_H

#include "theory/rewriterules/theory_rewriterules.h"
#include "theory/rewriterules/theory_rewriterules_params.h"

namespace CVC4 {
namespace theory {
namespace rewriterules {
#ifdef FIXED_REWRITE_RULES
inline std::ostream& operator <<(std::ostream& stream, const RewriteRule& r) {
  r.toStream(stream);
  return stream;
}
#endif


}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_RULES_H */
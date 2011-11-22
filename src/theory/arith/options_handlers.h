/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Custom handlers and predicates for arithmetic options
 **
 ** Custom handlers and predicates for arithmetic options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__ARITH__OPTIONS_HANDLERS_H

namespace CVC4 {
namespace theory {
namespace arith {

inline ArithPivotRule stringToArithPivotRule(std::string option, std::string optarg) {
  if(optarg == "min") {
    return MINIMUM;
  } else if(optarg == "min-break-ties") {
    return BREAK_TIES;
  } else if(optarg == "max") {
    return MAXIMUM;
  } else if(optarg == "help") {
    printf("Pivot rules available:\n");
    printf("min\n");
    printf("min-break-ties\n");
    printf("max\n");
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --pivot-rule: `") +
                          optarg + "'.  Try --pivot-rule help.");
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__OPTIONS_HANDLERS_H */

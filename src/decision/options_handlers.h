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
 ** \brief Custom handlers and predicates for DecisionEngine options
 **
 ** Custom handlers and predicates for DecisionEngine options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__DECISION__OPTIONS_HANDLERS_H
#define __CVC4__DECISION__OPTIONS_HANDLERS_H

#include "decision/decision_mode.h"

namespace CVC4 {
namespace decision {

static const std::string decisionModeHelp = "\
Decision modes currently supported by the --decision option:\n\
\n\
internal (default)\n\
+ Use the internal decision hueristics of the SAT solver\n\
\n\
justification\n\
+ An ATGP-inspired justification heuristic\n\
";

inline DecisionMode stringToDecisionMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "internal") {
    return DECISION_STRATEGY_INTERNAL;
  } else if(optarg == "justification") {
    return DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "help") {
    puts(decisionModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --decision: `") +
                          optarg + "'.  Try --decision help.");
  }
}

inline void setDecisionModeSetByUser(std::string option, bool b) {
  options::decisionModeSetByUser.set(true);
}

}/* CVC4::decision namespace */
}/* CVC4 namespace */

#endif /* __CVC4__DECISION__OPTIONS_HANDLERS_H */

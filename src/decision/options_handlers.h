/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
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
#include "main/options.h"

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
\n\
justification-stoponly\n\
+ Use the justification heuristic only to stop early, not for decisions\n\
";
/** Under-development options, commenting out from help for the release */
/*
\n\
relevancy\n\
+ Under development may-relevancy\n\
\n\
relevancy-leaves\n\
+ May-relevancy, but decide only on leaves\n\
\n\
Developer modes:\n\
\n\
justification-rel\n\
+ Use the relevancy code to do the justification stuff\n\
+ (This should do exact same thing as justification)\n\
\n\
justification-must\n\
+ Start deciding on literals close to root instead of those\n\
+ near leaves (don't expect it to work well) [Unimplemented]\n\
";*/

inline DecisionMode stringToDecisionMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  options::decisionRelevancyLeaves.set(false);
  options::decisionMaxRelTimeAsPermille.set(1000);
  options::decisionComputeRelevancy.set(true);
  options::decisionMustRelevancy.set(false);
  options::decisionStopOnly.set(false);

  if(optarg == "internal") {
    return DECISION_STRATEGY_INTERNAL;
  } else if(optarg == "justification") {
    return DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "justification-stoponly") {
    options::decisionStopOnly.set(true);
    return DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "relevancy") {
    options::decisionRelevancyLeaves.set(false);
    return DECISION_STRATEGY_RELEVANCY;
  } else if(optarg == "relevancy-leaves") {
    options::decisionRelevancyLeaves.set(true);
    Trace("options") << "version is " << options::version() << std::endl;
    return DECISION_STRATEGY_RELEVANCY;
  } else if(optarg == "justification-rel") {
    // relevancyLeaves : irrelevant
    // maxRelTimeAsPermille : irrelevant
    options::decisionComputeRelevancy.set(false);
    options::decisionMustRelevancy.set(false);
    return DECISION_STRATEGY_RELEVANCY;
  } else if(optarg == "justification-must") {
    // relevancyLeaves : irrelevant
    // maxRelTimeAsPermille : irrelevant
    options::decisionComputeRelevancy.set(false);
    options::decisionMustRelevancy.set(true);
    return DECISION_STRATEGY_RELEVANCY;
  } else if(optarg == "help") {
    puts(decisionModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --decision: `") +
                          optarg + "'.  Try --decision help.");
  }
}

inline void checkDecisionBudget(std::string option, unsigned short budget, SmtEngine* smt) throw(OptionException) {
  if(budget == 0) {
    Warning() << "Decision budget is 0. Consider using internal decision heuristic and "
              << std::endl << " removing this option." << std::endl;
              
  }
}

}/* CVC4::decision namespace */
}/* CVC4 namespace */

#endif /* __CVC4__DECISION__OPTIONS_HANDLERS_H */

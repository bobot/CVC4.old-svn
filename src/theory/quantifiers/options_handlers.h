/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__OPTIONS_HANDLERS_H
#define __CVC4__THEORY__QUANTIFIERS__OPTIONS_HANDLERS_H

#include <string>

namespace CVC4 {
namespace theory {
namespace quantifiers {

static const std::string instWhenHelp = "\
Possible settings for --inst-when:\n\
+ pre-full\n\
+ full\n\
+ full-last-call\n\
+ last-call\n\
";

static const std::string literalMatchHelp = "\
Possible settings for --literal-matching:\n\
+ none\n\
+ predicate\n\
+ equality\n\
";

inline InstWhenMode stringToInstWhenMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg == "pre-full") {
    return INST_WHEN_PRE_FULL;
  } else if(optarg == "full") {
    return INST_WHEN_FULL;
  } else if(optarg == "full-last-call") {
    return INST_WHEN_FULL_LAST_CALL;
  } else if(optarg == "last-call") {
    return INST_WHEN_LAST_CALL;
  } else if(optarg == "help") {
    puts(instWhenHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --inst-when: `") +
                          optarg + "'.  Try --inst-when help.");
  }
}

inline LiteralMatchMode stringToLiteralMatchMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  if(optarg ==  "none") {
    return LITERAL_MATCH_NONE;
  } else if(optarg ==  "predicate") {
    return LITERAL_MATCH_PREDICATE;
  } else if(optarg ==  "equality") {
    return LITERAL_MATCH_EQUALITY;
  } else if(optarg ==  "help") {
    puts(literalMatchHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --literal-matching: `") +
                          optarg + "'.  Try --literal-matching help.");
  }
}

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__OPTIONS_HANDLERS_H */

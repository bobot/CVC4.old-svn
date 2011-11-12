#ifndef __CVC4__BASE_OPTIONS_HANDLERS_H
#define __CVC4__BASE_OPTIONS_HANDLERS_H

#include "options/options.h"

namespace CVC4 {

inline void showVersion(const Options& options) {
}

inline void showHelp(const Options& options) {
}

inline int increaseVerbosity(const Options& options) {
  return options[verbosity] + 1;
}

inline void decreaseVerbosity(const Options& options) {
  return options[verbosity] - 1;
}

inline void dumpMode(const Options& options, std::string optarg) {
#ifdef CVC4_DUMPING
  char* optargPtr = strdup(optarg.c_str());
  char* tokstr = optargPtr;
  char* toksave;
  while((optarg = strtok_r(tokstr, ",", &toksave)) != NULL) {
    tokstr = NULL;
    if(!strcmp(optarg, "benchmark")) {
    } else if(!strcmp(optarg, "declarations")) {
    } else if(!strcmp(optarg, "assertions")) {
    } else if(!strcmp(optarg, "learned")) {
    } else if(!strcmp(optarg, "clauses")) {
    } else if(!strcmp(optarg, "t-conflicts") ||
              !strcmp(optarg, "t-lemmas") ||
              !strcmp(optarg, "t-explanations")) {
      // These are "non-state-dumping" modes.  If state (SAT decisions,
      // propagations, etc.) is dumped, it will interfere with the validity
      // of these generated queries.
      if(Dump.isOn("state")) {
        throw OptionException(string("dump option `") + optarg +
                              "' conflicts with a previous, "
                              "state-dumping dump option.  You cannot "
                              "mix stateful and non-stateful dumping modes; "
                              "see --dump help.");
      } else {
        Dump.on("no-permit-state");
      }
    } else if(!strcmp(optarg, "state") ||
              !strcmp(optarg, "missed-t-conflicts") ||
              !strcmp(optarg, "t-propagations") ||
              !strcmp(optarg, "missed-t-propagations")) {
      // These are "state-dumping" modes.  If state (SAT decisions,
      // propagations, etc.) is not dumped, it will interfere with the
      // validity of these generated queries.
      if(Dump.isOn("no-permit-state")) {
        throw OptionException(string("dump option `") + optarg +
                              "' conflicts with a previous, "
                              "non-state-dumping dump option.  You cannot "
                              "mix stateful and non-stateful dumping modes; "
                              "see --dump help.");
      } else {
        Dump.on("state");
      }
    } else if(!strcmp(optarg, "help")) {
      puts(dumpHelp.c_str());
      exit(1);
    } else {
      throw OptionException(string("unknown option for --dump: `") +
                            optarg + "'.  Try --dump help.");
    }

    Dump.on(optarg);
    Dump.on("benchmark");
    if(strcmp(optarg, "benchmark")) {
      Dump.on("declarations");
    }
  }
  free(optargPtr);
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

inline void dumpToFile(const Options& options, std::string optarg) {
#ifdef CVC4_DUMPING
  if(optarg == "") {
    throw OptionException(string("Bad file name for --dump-to"));
  } else if(optarg == "-") {
    Dump.setStream(DumpC::dump_cout);
  } else {
    ostream* dumpTo = new ofstream(optarg, ofstream::out | ofstream::trunc);
    if(!*dumpTo) {
      throw OptionException(string("Cannot open dump-to file (maybe it exists): `") + optarg + "'");
    }
    Dump.setStream(*dumpTo);
  }
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

inline void setOutputLanguage(const Options& options, std::string optarg) throw(OptionException) {
  if(str == "cvc4" || str == "pl") {
    outputLanguage = language::output::LANG_CVC4;
    return;
  } else if(str == "smtlib" || str == "smt") {
    outputLanguage = language::output::LANG_SMTLIB;
    return;
  } else if(str == "smtlib2" || str == "smt2") {
    outputLanguage = language::output::LANG_SMTLIB_V2;
    return;
  } else if(str == "ast") {
    outputLanguage = language::output::LANG_AST;
    return;
  } else if(str == "auto") {
    outputLanguage = language::output::LANG_AUTO;
    return;
  }

  if(strcmp(str, "help")) {
    throw OptionException(string("unknown language for --output-lang: `") +
                          str + "'.  Try --output-lang help.");
  }

  languageHelp = true;
}

inline void setInputLanguage(const Options& options, std::string optarg) throw(OptionException) {
  if(str == "cvc4" || str == "pl" || str == "presentation") {
    inputLanguage = language::input::LANG_CVC4;
    return;
  } else if(str == "smtlib" || str == "smt") {
    inputLanguage = language::input::LANG_SMTLIB;
    return;
  } else if(str == "smtlib2" || str == "smt2") {
    inputLanguage = language::input::LANG_SMTLIB_V2;
    return;
  } else if(str == "auto") {
    inputLanguage = language::input::LANG_AUTO;
    return;
  }

  if(str == "help") {
    throw OptionException(string("unknown language for --lang: `") +
                          str + "'.  Try --lang help.");
  }

  languageHelp = true;
}

inline void showConfiguration(const Options& options) {
  fputs(Configuration::about().c_str(), stdout);
  printf("\n");
  printf("version    : %s\n", Configuration::getVersionString().c_str());
  if(Configuration::isSubversionBuild()) {
    printf("subversion : yes [%s r%u%s]\n",
           Configuration::getSubversionBranchName(),
           Configuration::getSubversionRevision(),
           Configuration::hasSubversionModifications() ?
             " (with modifications)" : "");
  } else {
    printf("subversion : %s\n", Configuration::isSubversionBuild() ? "yes" : "no");
  }
  printf("\n");
  printf("library    : %u.%u.%u\n",
         Configuration::getVersionMajor(),
         Configuration::getVersionMinor(),
         Configuration::getVersionRelease());
  printf("\n");
  printf("debug code : %s\n", Configuration::isDebugBuild() ? "yes" : "no");
  printf("statistics : %s\n", Configuration::isStatisticsBuild() ? "yes" : "no");
  printf("replay     : %s\n", Configuration::isReplayBuild() ? "yes" : "no");
  printf("tracing    : %s\n", Configuration::isTracingBuild() ? "yes" : "no");
  printf("dumping    : %s\n", Configuration::isDumpingBuild() ? "yes" : "no");
  printf("muzzled    : %s\n", Configuration::isMuzzledBuild() ? "yes" : "no");
  printf("assertions : %s\n", Configuration::isAssertionBuild() ? "yes" : "no");
  printf("proof      : %s\n", Configuration::isProofBuild() ? "yes" : "no");
  printf("coverage   : %s\n", Configuration::isCoverageBuild() ? "yes" : "no");
  printf("profiling  : %s\n", Configuration::isProfilingBuild() ? "yes" : "no");
  printf("competition: %s\n", Configuration::isCompetitionBuild() ? "yes" : "no");
  printf("\n");
  printf("cudd       : %s\n", Configuration::isBuiltWithCudd() ? "yes" : "no");
  printf("cln        : %s\n", Configuration::isBuiltWithCln() ? "yes" : "no");
  printf("gmp        : %s\n", Configuration::isBuiltWithGmp() ? "yes" : "no");
  printf("tls        : %s\n", Configuration::isBuiltWithTlsSupport() ? "yes" : "no");
  exit(0);
}

inline void preemptGetOpt(const Options& options) {
}

inline void addTraceTag(const Options& options, std::string optarg) {
  Trace.on(optarg);
}

inline void addDebugTag(const Options& options) {
  Debug.on(optarg);
  Trace.on(optarg);
}

inline InputLanguage stringToInputLanguage(const Options& options, std::string optarg) {
}

inline OutputLanguage stringToOutputLanguage(const Options& options, std::string optarg) {
}

inline SimplificationMode stringToOutputLanguage(const Options& options, std::string optarg) {
  if(optarg == "batch") {
    simplificationMode = SIMPLIFICATION_MODE_BATCH;
  } else if(optarg == "incremental") {
    simplificationMode = SIMPLIFICATION_MODE_INCREMENTAL;
  } else if(optarg == "none") {
    simplificationMode = SIMPLIFICATION_MODE_NONE;
  } else if(optarg == "help") {
    puts(simplificationHelp.c_str());
    exit(1);
  } else {
    throw OptionException(string("unknown option for --simplification: `") +
                          optarg + "'.  Try --simplification help.");
  }
}

inline void showDebugTags(const Options& options) {
  if(Configuration::isDebugBuild()) {
    printf("available tags:");
    unsigned ntags = Configuration::getNumDebugTags();
    char const* const* tags = Configuration::getDebugTags();
    for(unsigned i = 0; i < ntags; ++ i) {
      printf(" %s", tags[i]);
    }
    printf("\n");
  } else {
    throw OptionException("debug tags not available in non-debug build");
  }
  exit(0);
}

inline void showTraceTags(const Options& options) {
  if(Configuration::isTracingBuild()) {
    printf("available tags:");
    unsigned ntags = Configuration::getNumTraceTags();
    char const* const* tags = Configuration::getTraceTags();
    for (unsigned i = 0; i < ntags; ++ i) {
      printf(" %s", tags[i]);
    }
    printf("\n");
  } else {
    throw OptionException("trace tags not available in non-tracing build");
  }
  exit(0);
}

inline void setDefaultExprDepth(const Options& options) {
  int depth = atoi(optarg);

  Debug.getStream() << Expr::setdepth(depth);
  Trace.getStream() << Expr::setdepth(depth);
  Notice.getStream() << Expr::setdepth(depth);
  Chat.getStream() << Expr::setdepth(depth);
  Message.getStream() << Expr::setdepth(depth);
  Warning.getStream() << Expr::setdepth(depth);
}

inline void setPrintExprTypes(const Options& options) {
  Debug.getStream() << Expr::printtypes(true);
  Trace.getStream() << Expr::printtypes(true);
  Notice.getStream() << Expr::printtypes(true);
  Chat.getStream() << Expr::printtypes(true);
  Message.getStream() << Expr::printtypes(true);
  Warning.getStream() << Expr::printtypes(true);
}

inline double stringToRandomFreq(const Options& options, std::string optarg) {
  double d = atof(optarg.c_str());
  if(! (0.0 <= d && d <= 1.0)){
    throw OptionException(string("--random-freq: `") +
                          optarg + "' is not between 0.0 and 1.0.");
  }
}

inline ArithPivotRule stringToArithPivotRule(const Options& options, std::string optarg) {
  if(!strcmp(optarg, "min")) {
    return MINIMUM;
  } else if(!strcmp(optarg, "min-break-ties")) {
    return BREAK_TIES;
  } else if(!strcmp(optarg, "max")) {
    return MAXIMUM;
  } else if(!strcmp(optarg, "help")) {
    printf("Pivot rules available:\n");
    printf("min\n");
    printf("min-break-ties\n");
    printf("max\n");
    exit(1);
  } else {
    throw OptionException(string("unknown option for --pivot-rule: `") +
                          optarg + "'.  Try --pivot-rule help.");
  }
}

}/* CVC4 namespace */

//runHandlers

#endif /* __CVC4__BASE_OPTIONS_HANDLERS_H */


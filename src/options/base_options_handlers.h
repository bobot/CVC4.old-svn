#ifndef __CVC4__BASE_OPTIONS_HANDLERS_H
#define __CVC4__BASE_OPTIONS_HANDLERS_H

#include "options/options.h"
#include "options/base_options.h"

#include <iostream>
#include <string>

namespace CVC4 {

static const std::string dumpHelp = "\
Dump modes currently supported by the --dump option:\n\
\n\
benchmark\n\
+ Dump the benchmark structure (set-logic, push/pop, queries, etc.), but\n\
  does not include any declarations or assertions.  Implied by all following\n\
  modes.\n\
\n\
declarations\n\
+ Dump declarations.  Implied by all following modes.\n\
\n\
assertions\n\
+ Output the assertions after non-clausal simplification and static\n\
  learning phases, but before presolve-time T-lemmas arrive.  If\n\
  non-clausal simplification and static learning are off\n\
  (--simplification=none --no-static-learning), the output\n\
  will closely resemble the input (with term-level ITEs removed).\n\
\n\
learned\n\
+ Output the assertions after non-clausal simplification, static\n\
  learning, and presolve-time T-lemmas.  This should include all eager\n\
  T-lemmas (in the form provided by the theory, which my or may not be\n\
  clausal).  Also includes level-0 BCP done by Minisat.\n\
\n\
clauses\n\
+ Do all the preprocessing outlined above, and dump the CNF-converted\n\
  output\n\
\n\
state\n\
+ Dump all contextual assertions (e.g., SAT decisions, propagations..).\n\
  Implied by all \"stateful\" modes below and conflicts with all\n\
  non-stateful modes below.\n\
\n\
t-conflicts [non-stateful]\n\
+ Output correctness queries for all theory conflicts\n\
\n\
missed-t-conflicts [stateful]\n\
+ Output completeness queries for theory conflicts\n\
\n\
t-propagations [stateful]\n\
+ Output correctness queries for all theory propagations\n\
\n\
missed-t-propagations [stateful]\n\
+ Output completeness queries for theory propagations (LARGE and EXPENSIVE)\n\
\n\
t-lemmas [non-stateful]\n\
+ Output correctness queries for all theory lemmas\n\
\n\
t-explanations [non-stateful]\n\
+ Output correctness queries for all theory explanations\n\
\n\
Dump modes can be combined with multiple uses of --dump.  Generally you want\n\
one from the assertions category (either asertions, learned, or clauses), and\n\
perhaps one or more stateful or non-stateful modes for checking correctness\n\
and completeness of decision procedure implementations.  Stateful modes dump\n\
the contextual assertions made by the core solver (all decisions and propagations\n\
as assertions; that affects the validity of the resulting correctness and\n\
completeness queries, so of course stateful and non-stateful modes cannot\n\
be mixed in the same run.\n\
\n\
The --output-language option controls the language used for dumping, and\n\
this allows you to connect CVC4 to another solver implementation via a UNIX\n\
pipe to perform on-line checking.  The --dump-to option can be used to dump\n\
to a file.\n\
";

static const std::string simplificationHelp = "\
Simplification modes currently supported by the --simplification option:\n\
\n\
batch (default) \n\
+ save up all ASSERTions; run nonclausal simplification and clausal\n\
  (MiniSat) propagation for all of them only after reaching a querying command\n\
  (CHECKSAT or QUERY or predicate SUBTYPE declaration)\n\
\n\
incremental\n\
+ run nonclausal simplification and clausal propagation at each ASSERT\n\
  (and at CHECKSAT/QUERY/SUBTYPE)\n\
\n\
none\n\
+ do not perform nonclausal simplification\n\
";

inline void increaseVerbosity(Options& options, std::string option) {
  options.set(verbosity, options[verbosity] + 1);
}

inline void decreaseVerbosity(Options& options, std::string option) {
  options.set(verbosity, options[verbosity] - 1);
}

inline void dumpMode(Options& options, std::string option, std::string optarg) {
#ifdef CVC4_DUMPING
  char* optargPtr = strdup(optarg.c_str());
  char* tokstr = optargPtr;
  char* toksave;
  while((optargPtr = strtok_r(tokstr, ",", &toksave)) != NULL) {
    tokstr = NULL;
    if(!strcmp(optargPtr, "benchmark")) {
    } else if(!strcmp(optargPtr, "declarations")) {
    } else if(!strcmp(optargPtr, "assertions")) {
    } else if(!strcmp(optargPtr, "learned")) {
    } else if(!strcmp(optargPtr, "clauses")) {
    } else if(!strcmp(optargPtr, "t-conflicts") ||
              !strcmp(optargPtr, "t-lemmas") ||
              !strcmp(optargPtr, "t-explanations")) {
      // These are "non-state-dumping" modes.  If state (SAT decisions,
      // propagations, etc.) is dumped, it will interfere with the validity
      // of these generated queries.
      if(Dump.isOn("state")) {
        throw OptionException(std::string("dump option `") + optargPtr +
                              "' conflicts with a previous, "
                              "state-dumping dump option.  You cannot "
                              "mix stateful and non-stateful dumping modes; "
                              "see --dump help.");
      } else {
        Dump.on("no-permit-state");
      }
    } else if(!strcmp(optargPtr, "state") ||
              !strcmp(optargPtr, "missed-t-conflicts") ||
              !strcmp(optargPtr, "t-propagations") ||
              !strcmp(optargPtr, "missed-t-propagations")) {
      // These are "state-dumping" modes.  If state (SAT decisions,
      // propagations, etc.) is not dumped, it will interfere with the
      // validity of these generated queries.
      if(Dump.isOn("no-permit-state")) {
        throw OptionException(std::string("dump option `") + optargPtr +
                              "' conflicts with a previous, "
                              "non-state-dumping dump option.  You cannot "
                              "mix stateful and non-stateful dumping modes; "
                              "see --dump help.");
      } else {
        Dump.on("state");
      }
    } else if(!strcmp(optargPtr, "help")) {
      puts(dumpHelp.c_str());
      exit(1);
    } else {
      throw OptionException(std::string("unknown option for --dump: `") +
                            optargPtr + "'.  Try --dump help.");
    }

    Dump.on(optargPtr);
    Dump.on("benchmark");
    if(strcmp(optargPtr, "benchmark")) {
      Dump.on("declarations");
    }
  }
  free(optargPtr);
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

inline void dumpToFile(Options& options, std::string option, std::string optarg) {
#ifdef CVC4_DUMPING
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --dump-to"));
  } else if(optarg == "-") {
    Dump.setStream(DumpC::dump_cout);
  } else {
    std::ostream* dumpTo = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(!*dumpTo) {
      throw OptionException(std::string("Cannot open dump-to file (maybe it exists): `") + optarg + "'");
    }
    Dump.setStream(*dumpTo);
  }
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

inline OutputLanguage stringToOutputLanguage(Options& options, std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "cvc4" || optarg == "pl") {
    return language::output::LANG_CVC4;
  } else if(optarg == "smtlib" || optarg == "smt") {
    return language::output::LANG_SMTLIB;
  } else if(optarg == "smtlib2" || optarg == "smt2") {
    return language::output::LANG_SMTLIB_V2;
  } else if(optarg == "ast") {
    return language::output::LANG_AST;
  } else if(optarg == "auto") {
    return language::output::LANG_AUTO;
  }

  if(optarg != "help") {
    throw OptionException(std::string("unknown language for --output-lang: `") +
                          optarg + "'.  Try --output-lang help.");
  }

  options.set(languageHelp, true);
  return language::output::LANG_AUTO;
}

inline InputLanguage stringToInputLanguage(Options& options, std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "cvc4" || optarg == "pl" || optarg == "presentation") {
    return language::input::LANG_CVC4;
  } else if(optarg == "smtlib" || optarg == "smt") {
    return language::input::LANG_SMTLIB;
  } else if(optarg == "smtlib2" || optarg == "smt2") {
    return language::input::LANG_SMTLIB_V2;
  } else if(optarg == "auto") {
    return language::input::LANG_AUTO;
  }

  if(optarg != "help") {
    throw OptionException(std::string("unknown language for --lang: `") +
                          optarg + "'.  Try --lang help.");
  }

  options.set(languageHelp, true);
  return language::input::LANG_AUTO;
}

inline SimplificationMode stringToSimplificationMode(Options& options, std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "batch") {
    return SIMPLIFICATION_MODE_BATCH;
  } else if(optarg == "incremental") {
    return SIMPLIFICATION_MODE_INCREMENTAL;
  } else if(optarg == "none") {
    return SIMPLIFICATION_MODE_NONE;
  } else if(optarg == "help") {
    puts(simplificationHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --simplification: `") +
                          optarg + "'.  Try --simplification help.");
  }
}

inline void showConfiguration(Options& options, std::string option) {
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

inline void addTraceTag(Options& options, std::string option, std::string optarg) {
  Trace.on(optarg);
}

inline void addDebugTag(Options& options, std::string option, std::string optarg) {
  Debug.on(optarg);
  Trace.on(optarg);
}

inline SimplificationMode stringToSimplificationNode(Options& options, std::string option, std::string optarg) {
  if(optarg == "batch") {
    return SIMPLIFICATION_MODE_BATCH;
  } else if(optarg == "incremental") {
    return SIMPLIFICATION_MODE_INCREMENTAL;
  } else if(optarg == "none") {
    return SIMPLIFICATION_MODE_NONE;
  } else if(optarg == "help") {
    puts(simplificationHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --simplification: `") +
                          optarg + "'.  Try --simplification help.");
  }
}

inline void showDebugTags(Options& options, std::string option) {
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

inline void showTraceTags(Options& options, std::string option) {
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

inline void setDefaultExprDepth(Options& options, std::string option, std::string optarg) {
  int depth = atoi(optarg.c_str());

  Debug.getStream() << Expr::setdepth(depth);
  Trace.getStream() << Expr::setdepth(depth);
  Notice.getStream() << Expr::setdepth(depth);
  Chat.getStream() << Expr::setdepth(depth);
  Message.getStream() << Expr::setdepth(depth);
  Warning.getStream() << Expr::setdepth(depth);
}

inline void setPrintExprTypes(Options& options, std::string option) {
  Debug.getStream() << Expr::printtypes(true);
  Trace.getStream() << Expr::printtypes(true);
  Notice.getStream() << Expr::printtypes(true);
  Chat.getStream() << Expr::printtypes(true);
  Message.getStream() << Expr::printtypes(true);
  Warning.getStream() << Expr::printtypes(true);
}

inline void setInteractiveByUser(Options& options, std::string option, bool b) {
  options.set(interactiveSetByUser, true);
}

inline std::string checkReplayFilename(Options& options, std::string option, std::string optarg) {
#ifdef CVC4_REPLAY
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --replay"));
  } else {
    return optarg;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}

inline std::ostream* checkReplayLogFilename(Options& options, std::string option, std::string optarg) {
#ifdef CVC4_REPLAY 
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --replay-log"));
  } else if(optarg == "-") {
    return &std::cout;
  } else {
    std::ostream* replayLog = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(!*replayLog) {
      throw OptionException(std::string("Cannot open replay-log file: `") + optarg + "'");
    }
    return replayLog;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}

inline double stringToRandomFreq(Options& options, std::string option, std::string optarg) {
  double d = atof(optarg.c_str());
  if(! (0.0 <= d && d <= 1.0)){
    throw OptionException(std::string("--random-freq: `") +
                          optarg + "' is not between 0.0 and 1.0.");
  }
  return d;
}

inline ArithPivotRule stringToArithPivotRule(Options& options, std::string option, std::string optarg) {
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

}/* CVC4 namespace */

#endif /* __CVC4__BASE_OPTIONS_HANDLERS_H */


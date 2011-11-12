/*********************                                                        */
/*! \file options_template.cpp
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
 ** \brief Contains code for handling command-line options.
 **
 ** Contains code for handling command-line options
 **/

#include <cstdio>
#include <cstdlib>
#include <new>
#include <string>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#include <getopt.h>

#include "expr/expr.h"
#include "util/configuration.h"
#include "util/exception.h"
#include "util/language.h"
#include "options/options.h"
#include "options/theory_arith_options.h"
#include "options/theory_uf_options.h"
#include "options/prop_options.h"
#include "util/output.h"

#include "options/options_holder.h"

#include "cvc4autoconfig.h"

${option_handler_includes}

using namespace std;
using namespace CVC4;

namespace CVC4 {

CVC4_THREADLOCAL(const Options*) Options::s_current = NULL;

#ifdef CVC4_DEBUG
#  define USE_EARLY_TYPE_CHECKING_BY_DEFAULT true
#else /* CVC4_DEBUG */
#  define USE_EARLY_TYPE_CHECKING_BY_DEFAULT false
#endif /* CVC4_DEBUG */

#if defined(CVC4_MUZZLED) || defined(CVC4_COMPETITION_MODE)
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT false
#else /* CVC4_MUZZLED || CVC4_COMPETITION_MODE */
#  define DO_SEMANTIC_CHECKS_BY_DEFAULT true
#endif /* CVC4_MUZZLED || CVC4_COMPETITION_MODE */

Options::Options() :
  d_holder() {
}

OptionsHolder::OptionsHolder() : ${module_defaults}
{
}

static const string mostCommonOptionsDescription = "\
Most commonly-used CVC4 options:\n\
   --version | -V         identify this CVC4 binary\n\
   --help | -h            full command line reference\n\
   --lang | -L            force input language (default is `auto'; see --lang help)\n\
   --output-lang          force output language (default is `auto'; see --lang help)\n\
   --verbose | -v         increase verbosity (may be repeated)\n\
   --quiet | -q           decrease verbosity (may be repeated)\n\
   --stats                give statistics on exit\n\
   --parse-only           exit after parsing input\n\
   --preprocess-only      exit after preproc (useful with --stats or --dump)\n\
   --dump=MODE            dump preprocessed assertions, etc., see --dump=help\n\
   --dump-to=FILE         all dumping goes to FILE (instead of stdout)\n\
   --show-config          show CVC4 static configuration\n\
   --strict-parsing       be less tolerant of non-conforming inputs\n\
   --interactive          force interactive mode\n\
   --no-interactive       force non-interactive mode\n\
   --produce-models | -m  support the get-value command\n\
   --produce-assignments  support the get-assignment command\n\
   --proof                turn on proof generation\n\
   --incremental | -i     enable incremental solving\n\
   --tlimit=MS            enable time limiting (give milliseconds)\n\
   --tlimit-per=MS        enable time limiting per query (give milliseconds)\n\
   --rlimit=N             enable resource limiting\n\
   --rlimit-per=N         enable resource limiting per query\n\
";

static const string optionsDescription = mostCommonOptionsDescription + "\
\n\
Additional CVC4 options:\n\
   --mmap                 memory map file input\n\
   --segv-nospin          don't spin on segfault waiting for gdb\n\
   --lazy-type-checking   type check expressions only when necessary (default)\n\
   --eager-type-checking  type check expressions immediately on creation (debug builds only)\n\
   --no-type-checking     never type check expressions\n\
   --no-checking          disable ALL semantic checks, including type checks\n\
   --no-theory-registration disable theory reg (not safe for some theories)\n\
   --trace | -t           trace something (e.g. -t pushpop), can repeat\n\
   --debug | -d           debug something (e.g. -d arith), can repeat\n\
   --show-debug-tags      show all avalable tags for debugging\n\
   --show-trace-tags      show all avalable tags for tracing\n\
   --default-expr-depth=N print exprs to depth N (0 == default, -1 == no limit)\n\
   --print-expr-types     print types with variables when printing exprs\n\
   --lazy-definition-expansion expand define-funs/LAMBDAs lazily\n\
   --simplification=MODE  choose simplification mode, see --simplification=help\n\
   --no-static-learning   turn off static learning (e.g. diamond-breaking)\n\
   --replay=file          replay decisions from file\n\
   --replay-log=file      log decisions and propagations to file\n\
   --pivot-rule=RULE      change the pivot rule (see --pivot-rule help)\n\
   --pivot-threshold=N   sets the number of heuristic pivots per variable per simplex instance\n\
   --prop-row-length=N    sets the maximum row length to be used in propagation\n\
   --random-freq=P        sets the frequency of random decisions in the sat solver(P=0.0 by default)\n\
   --random-seed=S        sets the random seed for the sat solver\n\
   --disable-variable-removal enable permanent removal of variables in arithmetic (UNSAFE! experts only)\n\
   --disable-arithmetic-propagation turns on arithmetic propagation\n\
   --disable-symmetry-breaker turns off UF symmetry breaker (Deharbe et al., CADE 2011)\n\
";

#warning "Change CL options as --disable-variable-removal cannot do anything currently."

static const string languageDescription = "\
Languages currently supported as arguments to the -L / --lang option:\n\
  auto           attempt to automatically determine the input language\n\
  pl | cvc4      CVC4 presentation language\n\
  smt | smtlib   SMT-LIB format 1.2\n\
  smt2 | smtlib2 SMT-LIB format 2.0\n\
\n\
Languages currently supported as arguments to the --output-lang option:\n\
  auto           match the output language to the input language\n\
  pl | cvc4      CVC4 presentation language\n\
  smt | smtlib   SMT-LIB format 1.2\n\
  smt2 | smtlib2 SMT-LIB format 2.0\n\
  ast            internal format (simple syntax-tree language)\n\
";

static const string simplificationHelp = "\
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

static const string dumpHelp = "\
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

string Options::getDescription() const {
  return optionsDescription;
}

void Options::printUsage(const std::string msg, std::ostream& out) {
  out << msg << optionsDescription << endl << flush;
}

void Options::printShortUsage(const std::string msg, std::ostream& out) {
  out << msg << mostCommonOptionsDescription << endl
      << "For full usage, please use --help." << endl << flush;
}

void Options::printLanguageHelp(std::ostream& out) {
  out << languageDescription << flush;
}

/**
 * This is a table of long options.  By policy, each short option
 * should have an equivalent long option (but the reverse isn't the
 * case), so this table should thus contain all command-line options.
 *
 * Each option in this array has four elements:
 *
 * 1. the long option string
 * 2. argument behavior for the option:
 *    no_argument - no argument permitted
 *    required_argument - an argument is expected
 *    optional_argument - an argument is permitted but not required
 * 3. this is a pointer to an int which is set to the 4th entry of the
 *    array if the option is present; or NULL, in which case
 *    getopt_long() returns the 4th entry
 * 4. the return value for getopt_long() when this long option (or the
 *    value to set the 3rd entry to; see #3)
 *
 * If you add something here, you should add it in src/main/usage.h
 * also, to document it.
 *
 * If you add something that has a short option equivalent, you should
 * add it to the getopt_long() call in parseOptions().
 */
static struct option cmdlineOptions[] = {${module_long_options}
  { NULL, no_argument, NULL, '\0' }
};

static void preemptGetopt(int& argc, char**& argv, char* opt) {
  const size_t maxoptlen = 128;

  AlwaysAssert(opt != NULL && *opt != '\0');
  AlwaysAssert(strlen(opt) <= maxoptlen);

  ++argc;
  unsigned i = 0;
  while(argv[i] != NULL && argv[i][0] != '\0') {
    ++i;
  }

  if(argv[i] == NULL) {
    argv = (char**) realloc(argv, (i + 6) * sizeof(char*));
    for(unsigned j = i; j < i + 5; ++j) {
      argv[j] = (char*) malloc(sizeof(char) * maxoptlen);
      argv[j][0] = '\0';
    }
    argv[i + 5] = NULL;
  }

  strncpy(argv[i], opt, maxoptlen - 1);
  argv[i][maxoptlen - 1] = '\0'; // ensure NUL-termination even on overflow
}

/** Parse argc/argv and put the result into a CVC4::Options struct. */
int Options::parseOptions(int argc, char* argv[])
throw(OptionException) {
  const char *progName = argv[0];
  int c;

  // find the base name of the program
  const char *x = strrchr(progName, '/');
  if(x != NULL) {
    progName = x + 1;
  }
  d_holder->binary_name = string(progName);

  int extra_argc = 0;
  char **extra_argv = (char**) malloc(sizeof(char*));
  extra_argv[0] = NULL;

  int extra_optind = 0, main_optind = 0;

  for(;;) {
    if(extra_optind < extra_argc) {
      optreset = 1;
      optind = extra_optind;
      c = getopt_long(extra_argc, extra_argv,
                      ":${module_short_options}",
                      cmdlineOptions, NULL);
      if(extra_optind >= extra_argc) {
        unsigned i = 0;
        while(extra_argv[i] != NULL && extra_argv[i][0] != '\0') {
          extra_argv[i][0] = '\0';
          ++i;
        }
        extra_argc = extra_optind = 0;
      } else {
        extra_optind = optind;
      }
    }
    if(c == -1) {
      optreset = 1;
      optind = main_optind;
      c = getopt_long(argc, argv,
                      ":${module_short_options}",
                      cmdlineOptions, NULL);
      main_optind = optind;
      if(c == -1) {
        break;
      }
    }

    switch(c) {
${module_option_handlers}

    case ':':
      throw OptionException(string("option `") + argv[optind - 1] + "' missing its required argument");

    case '?':
    default:
      throw OptionException(string("can't understand option `") + argv[optind - 1] + "'");
    }
  }

  if(incrementalSolving && proof) {
    throw OptionException(string("The use of --incremental with --proof is not yet supported"));
  }

  return optind;
}

void Options::setOutputLanguage(const char* str) throw(OptionException) {
  if(!strcmp(str, "cvc4") || !strcmp(str, "pl")) {
    outputLanguage = language::output::LANG_CVC4;
    return;
  } else if(!strcmp(str, "smtlib") || !strcmp(str, "smt")) {
    outputLanguage = language::output::LANG_SMTLIB;
    return;
  } else if(!strcmp(str, "smtlib2") || !strcmp(str, "smt2")) {
    outputLanguage = language::output::LANG_SMTLIB_V2;
    return;
  } else if(!strcmp(str, "ast")) {
    outputLanguage = language::output::LANG_AST;
    return;
  } else if(!strcmp(str, "auto")) {
    outputLanguage = language::output::LANG_AUTO;
    return;
  }

  if(strcmp(str, "help")) {
    throw OptionException(string("unknown language for --output-lang: `") +
                          str + "'.  Try --output-lang help.");
  }

  languageHelp = true;
}

void Options::setInputLanguage(const char* str) throw(OptionException) {
  if(!strcmp(str, "cvc4") || !strcmp(str, "pl") || !strcmp(str, "presentation")) {
    inputLanguage = language::input::LANG_CVC4;
    return;
  } else if(!strcmp(str, "smtlib") || !strcmp(str, "smt")) {
    inputLanguage = language::input::LANG_SMTLIB;
    return;
  } else if(!strcmp(str, "smtlib2") || !strcmp(str, "smt2")) {
    inputLanguage = language::input::LANG_SMTLIB_V2;
    return;
  } else if(!strcmp(str, "auto")) {
    inputLanguage = language::input::LANG_AUTO;
    return;
  }

  if(strcmp(str, "help")) {
    throw OptionException(string("unknown language for --lang: `") +
                          str + "'.  Try --lang help.");
  }

  languageHelp = true;
}

std::ostream& operator<<(std::ostream& out, SimplificationMode mode) {
  switch(mode) {
  case SIMPLIFICATION_MODE_INCREMENTAL:
    out << "SIMPLIFICATION_MODE_INCREMENTAL";
    break;
  case SIMPLIFICATION_MODE_BATCH:
    out << "SIMPLIFICATION_MODE_BATCH";
    break;
  case SIMPLIFICATION_MODE_NONE:
    out << "SIMPLIFICATION_MODE_NONE";
    break;
  default:
    out << "SimplificationMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, ArithPivotRule rule) {
  switch(rule) {
  case MINIMUM:
    out << "MINIMUM";
    break;
  case BREAK_TIES:
    out << "BREAK_TIES";
    break;
  case MAXIMUM:
    out << "MAXIMUM";
    break;
  default:
    out << "ArithPivotRule!UNKNOWN";
  }

  return out;
}

#undef USE_EARLY_TYPE_CHECKING_BY_DEFAULT
#undef DO_SEMANTIC_CHECKS_BY_DEFAULT

}/* CVC4 namespace */

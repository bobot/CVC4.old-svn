/*********************                                                        */
/*! \file options.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): dejan, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
#include <vector>
#include <string>
#include <iostream>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#include <boost/program_options.hpp>

#include "expr/expr.h"
#include "util/configuration.h"
#include "util/exception.h"
#include "util/language.h"
#include "util/options.h"
#include "util/output.h"

#include "cvc4autoconfig.h"

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

using namespace std;
using namespace CVC4;
using namespace boost::program_options;

namespace CVC4 {

static const string languageDescription = "\
Languages currently supported as arguments to the -L / --lang option:\n\
  auto           attempt to automatically determine the input language\n\
  pl | cvc4      CVC4 presentation language\n\
  smt | smtlib   SMT-LIB format 1.2\n\
  smt2 | smtlib2 SMT-LIB format 2.0\n\
";

static const string ufDescription = "\
UF implementations available:\n\
  morgan   Morgan's UF solver (default)\n\
  tim      Tim's initial UF solver (predicates and models not supported)\n\
";

void Options::printUsage(const string& msg, ostream& out) const {
  out << msg << option_desc << endl << flush;
}

void Options::printLanguageHelp(std::ostream& out) {
  out << languageDescription << flush;
}

void Options::printUfHelp(std::ostream& out) {
  out << ufDescription << flush;
}

void Options::printConfiguration(std::ostream& out) {
  out << Configuration::about() << endl
      << "version    : " << Configuration::getVersionString() << endl
      << endl
      << "library    : " << Configuration::getVersionMajor() << '.'
                         << Configuration::getVersionMinor() << '.'
                         << Configuration::getVersionRelease() << endl
      << endl
      << "debug code : " << (Configuration::isDebugBuild() ? "yes" : "no") << endl
      << "tracing    : " << (Configuration::isTracingBuild() ? "yes" : "no") << endl
      << "muzzled    : " << (Configuration::isMuzzledBuild() ? "yes" : "no") << endl
      << "assertions : " << (Configuration::isAssertionBuild() ? "yes" : "no") << endl
      << "coverage   : " << (Configuration::isCoverageBuild() ? "yes" : "no") << endl
      << "profiling  : " << (Configuration::isProfilingBuild() ? "yes" : "no") << endl
      << "competition: " << (Configuration::isCompetitionBuild() ? "yes" : "no") << endl
      << flush;
}

Options::Options() :
  option_desc("CVC4 options"),
  option_desc_hidden("Hidden options"),
  binary_name(),
  statistics(false),
  in(&std::cin),
  out(&std::cout),
  err(&std::cerr),
  verbosity(0),
  inputLanguage(language::input::LANG_AUTO),
  uf_implementation(MORGAN),
  parseOnly(false),
  semanticChecks(DO_SEMANTIC_CHECKS_BY_DEFAULT),
  theoryRegistration(true),
  memoryMap(false),
  strictParsing(false),
  lazyDefinitionExpansion(false),
  interactive(false),
  interactiveSetByUser(false),
  segvNoSpin(false),
  produceModels(false),
  produceAssignments(false),
  typeChecking(DO_SEMANTIC_CHECKS_BY_DEFAULT),
  earlyTypeChecking(USE_EARLY_TYPE_CHECKING_BY_DEFAULT) {

  options_description debug("Debugging options");
  options_description parser("Parser/input options");
  options_description core("Core options");
  options_description checking("Checking options");
  options_description theories("Theory options");
  options_description output("Output options");

  option_desc_hidden.add_options()
    ( "about", "identify this CVC4 binary" )
    ( "input-file", value<string>()->default_value("-"), "input file to process (default is `-', meaning stdin)" );
  option_desc.add_options()// driver options
    ( "help,h", "this command line reference" )
    ( "version,V", "identify this CVC4 binary" )
    ( "show-config", "show CVC4 static configuration" )
    ( "interactive", "run interactively" )
    ( "no-interactive", "do not run interactively" )
    ( "verbose,v", "increase verbosity (repeatable)" )
    ( "quiet,q", "decrease verbosity (repeatable)" )
    ( "stats", "give statistics on exit" );
  debug.add_options()
    ( "debug,d", value< vector<string> >(), "debugging for something (e.g. --debug arith), implies -t" )
    ( "trace,t", value< vector<string> >(), "tracing for something (e.g. --trace pushpop)" )
    ( "segv-nospin", "don't spin on segfault waiting for gdb" );
  parser.add_options()
    ( "lang,L", value<string>()->default_value("auto"), "force input language (default is `auto'; see --lang help)" )
    ( "mmap", "memory map file input" )
    ( "parse-only" , "parse, don't execute any commands" )
    ( "strict-parsing", "fail on non-conformant inputs (SMT2 only)" );
  core.add_options()
    ( "produce-models", "support the get-value command" )
    ( "produce-assignments", "support the get-assignment command" )
    ( "lazy-definition-expansion", "expand define-fun lazily" );
    ( "no-theory-registration", "do not do theory registration (unsafe for some theories)" );
  checking.add_options()
    ( "no-checking", "disable ALL semantic checks, including type checks" )
    ( "no-type-checking", "never type check expressions" )
    ( "lazy-type-checking", "type check expressions only when necessary (default)" )
    ( "eager-type-checking", "type check expressions immediately on creation" );
  theories.add_options()
    ( "uf", value<string>()->default_value("morgan"), "select uninterpreted function theory implementation" );
  output.add_options()
    ( "default-expr-depth", value<int>(), "print exprs to depth N (0 == default, -1 == no limit)" )
    ( "print-expr-types", "print types with variables when printing exprs" );

  option_desc.add(debug);
  option_desc.add(parser);
  option_desc.add(core);
  option_desc.add(checking);
  option_desc.add(theories);
  option_desc.add(output);
}

/** Parse argc/argv and put the result into a CVC4::Options struct. */
string Options::parseOptions(int argc, char* argv[]) throw(OptionException) {
  // compose visible and hidden options
  options_description allOptions;
  allOptions.add(option_desc);
  allOptions.add(option_desc_hidden);

  // positional options
  positional_options_description p;
  p.add("input-file", -1);

  // find the base name of the program
  const char *progName = argv[0];
  const char *cp = strrchr(progName, '/');
  if(cp != NULL) {
    progName = cp + 1;
  }
  binary_name = string(progName);

  // parse the command-line options
  variables_map vm;
  try {
    store(command_line_parser(argc, argv).
          options(allOptions).positional(p).run(), vm);
  } catch(std::exception& e) {
    throw OptionException(e.what());// e.g. unrecognized option
  }
  notify(vm);

  help = vm.count("help") + vm.count("about");
  version = vm.count("version");
  showConfig = vm.count("show-config");
  verbosity = vm.count("verbose") - vm.count("quiet");
  string lang = vm["lang"].as<string>();
  if(lang == "cvc4" || lang == "pl") {
    inputLanguage = language::input::LANG_CVC4;
  } else if(lang == "smtlib" || lang == "smt") {
    inputLanguage = language::input::LANG_SMTLIB;
  } else if(lang == "smtlib2" || lang == "smt2") {
    inputLanguage = language::input::LANG_SMTLIB_V2;
  } else if(lang == "auto") {
    inputLanguage = language::input::LANG_AUTO;
  } else if(lang == "help") {
    languageHelp = true;
  } else {
    throw OptionException(string("unknown language for --lang: `") +
                          optarg + "'.  Try --lang help.");
  }

  if(vm.count("trace")) {
    vector<string> traces = vm["trace"].as< vector<string> >();
    for(vector<string>::const_iterator i = traces.begin(),
          iend = traces.end();
        i != iend;
        ++i) {
      Trace.on(*i);
    }
  }
  if(vm.count("debug")) {
    vector<string> debugs = vm["debug"].as< vector<string> >();
    for(vector<string>::const_iterator i = debugs.begin(),
          iend = debugs.end();
        i != iend;
        ++i) {
      Debug.on(*i);
      Trace.on(*i);
    }
  }

  statistics = vm.count("stats");
  segvNoSpin = vm.count("segv-nospin");
  parseOnly = vm.count("parse-only");

  memoryMap = vm.count("mmap");
  strictParsing = vm.count("strict-parsing");

  if(vm.count("default-expr-depth")) {
    int depth = vm["default-expr-depth"].as<int>();
    Debug.getStream() << Expr::setdepth(depth);
    Trace.getStream() << Expr::setdepth(depth);
    Notice.getStream() << Expr::setdepth(depth);
    Chat.getStream() << Expr::setdepth(depth);
    Message.getStream() << Expr::setdepth(depth);
    Warning.getStream() << Expr::setdepth(depth);
  }

  if(vm.count("print-expr-types")) {
    Debug.getStream() << Expr::printtypes(true);
    Trace.getStream() << Expr::printtypes(true);
    Notice.getStream() << Expr::printtypes(true);
    Chat.getStream() << Expr::printtypes(true);
    Message.getStream() << Expr::printtypes(true);
    Warning.getStream() << Expr::printtypes(true);
  }

  string ufTheory = vm["uf"].as<string>();
  if(ufTheory == "tim") {
    uf_implementation = TIM;
  } else if(ufTheory == "morgan") {
    uf_implementation = MORGAN;
  } else if(ufTheory == "help") {
    ufHelp = true;
  } else {
    throw OptionException(string("unknown option for --uf: `") +
                          optarg + "'.  Try --uf help.");
  }

  lazyDefinitionExpansion = vm.count("lazy-definition-expansion");

  if(vm.count("interactive") && vm.count("no-interactive")) {
    throw OptionException("can't specify both --interactive and --no-interactive");
  }
  if(vm.count("interactive")) {
    interactive = true;
    interactiveSetByUser = true;
  }
  if(vm.count("no-interactive")) {
    interactive = false;
    interactiveSetByUser = true;
  }

  produceModels = vm.count("produce-models");
  produceAssignments = vm.count("produce-assignments");
  if(vm.count("no-theory-registration")) {
    theoryRegistration = false;
  }
  if(vm.count("no-checking")) {
    semanticChecks = false;
    typeChecking = false;
    earlyTypeChecking = false;
  }
  if(vm.count("no-type-checking")) {
    typeChecking = false;
    earlyTypeChecking = false;
  }
  if((vm.count("no-checking") || vm.count("no-type-checking")) && vm.count("eager-type-checking")) {
    throw OptionException("can't specify --eager-type-checking with --no-checking or --no-type-checking");
  }
  if((vm.count("no-checking") || vm.count("no-type-checking")) && vm.count("lazy-type-checking")) {
    throw OptionException("can't specify --lazy-type-checking with --no-checking or --no-type-checking");
  }
  if(vm.count("lazy-type-checking") && vm.count("eager-type-checking")) {
    throw OptionException("can't specify both --lazy-type-checking and --eager-type-checking");
  }
  if(vm.count("lazy-type-checking")) {
    typeChecking = true;
    earlyTypeChecking = false;
  }
  if(vm.count("eager-type-checking")) {
    typeChecking = true;
    earlyTypeChecking = true;
  }

  return vm["input-file"].as<string>();
}

}/* CVC4 namespace */

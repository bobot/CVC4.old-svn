/*********************                                                        */
/*! \file main.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, cconway
 ** Minor contributors (to current version): barrett, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Main driver for CVC4 executable.
 **
 ** Main driver for CVC4 executable.
 **/

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstring>
#include <new>

#include "cvc4autoconfig.h"
#include "main.h"
#include "usage.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "expr/command.h"
#include "util/Assert.h"
#include "util/configuration.h"
#include "util/output.h"
#include "smt/options.h"
#include "util/result.h"
#include "util/stats.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

namespace CVC4 {
  namespace main {
    struct Options options;
  }/* CVC4::main namespace */
}/* CVC4 namespace */

int runCvc4(int argc, char* argv[]);
void doCommand(SmtEngine&, Command*);

/**
 * CVC4's main() routine is just an exception-safe wrapper around CVC4.
 * Please don't construct anything here.  Even if the constructor is
 * inside the try { }, an exception during destruction can cause
 * problems.  That's why main() wraps runCvc4() in the first place.
 * Put everything in runCvc4().
 */
int main(int argc, char* argv[]) {
  try {
    return runCvc4(argc, argv);
  } catch(OptionException& e) {
#ifdef CVC4_COMPETITION_MODE
    cout << "unknown" << endl;
#endif
    cerr << "CVC4 Error:" << endl << e << endl;
    printf(usage, options.binary_name.c_str());
    exit(1);
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    cout << "unknown" << endl;
#endif
    cerr << "CVC4 Error:" << endl << e << endl;
    exit(1);
  } catch(bad_alloc) {
#ifdef CVC4_COMPETITION_MODE
    cout << "unknown" << endl;
#endif
    cerr << "CVC4 ran out of memory." << endl;
    exit(1);
  } catch(...) {
#ifdef CVC4_COMPETITION_MODE
    cout << "unknown" << endl;
#endif
    cerr << "CVC4 threw an exception of unknown type." << endl;
    exit(1);
  }
}


int runCvc4(int argc, char* argv[]) {

  // Initialize the signal handlers
  cvc4_init();

  // Parse the options
  int firstArgIndex = parseOptions(argc, argv, &options);

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC4_COMPETITION_MODE
  cout << unitbuf;
#endif

  // We only accept one input file
  if(argc > firstArgIndex + 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin =
    firstArgIndex >= argc || !strcmp("-", argv[firstArgIndex]);

  // if we're reading from stdin, default to interactive mode
  if(!options.interactiveSetByUser) {
    options.interactive = inputFromStdin;
  }

  // Create the expression manager
  ExprManager exprMgr(options.earlyTypeChecking);

  // Create the SmtEngine
  SmtEngine smt(&exprMgr, &options);

  // Auto-detect input language by filename extension
  const char* filename = inputFromStdin ? "<stdin>" : argv[firstArgIndex];

  ReferenceStat< const char* > s_statFilename("filename", filename);
  StatisticsRegistry::registerStat(&s_statFilename);

  if(options.inputLanguage == language::input::LANG_AUTO) {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      options.inputLanguage = language::input::LANG_CVC4;
    } else {
      unsigned len = strlen(filename);
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        options.inputLanguage = language::input::LANG_SMTLIB_V2;
      } else if(len >= 4 && !strcmp(".smt", filename + len - 4)) {
        options.inputLanguage = language::input::LANG_SMTLIB;
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        options.inputLanguage = language::input::LANG_CVC4;
      }
    }
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    Debug.setStream(CVC4::null_os);
    Trace.setStream(CVC4::null_os);
    Notice.setStream(CVC4::null_os);
    Chat.setStream(CVC4::null_os);
    Message.setStream(CVC4::null_os);
    Warning.setStream(CVC4::null_os);
  } else {
    if(options.verbosity < 2) {
      Chat.setStream(CVC4::null_os);
    }
    if(options.verbosity < 1) {
      Notice.setStream(CVC4::null_os);
    }
    if(options.verbosity < 0) {
      Message.setStream(CVC4::null_os);
      Warning.setStream(CVC4::null_os);
    }

    OutputLanguage language = language::toOutputLanguage(options.inputLanguage);
    Debug.getStream() << Expr::setlanguage(language);
    Trace.getStream() << Expr::setlanguage(language);
    Notice.getStream() << Expr::setlanguage(language);
    Chat.getStream() << Expr::setlanguage(language);
    Message.getStream() << Expr::setlanguage(language);
    Warning.getStream() << Expr::setlanguage(language);
  }

  ParserBuilder parserBuilder =
      ParserBuilder(exprMgr, filename)
        .withInputLanguage(options.inputLanguage)
        .withMmap(options.memoryMap)
        .withChecks(options.semanticChecks &&
                    !Configuration::isMuzzledBuild() )
        .withStrictMode( options.strictParsing );

  if( inputFromStdin ) {
    parserBuilder.withStreamInput(cin);
  }

  Parser *parser = parserBuilder.build();

  // Parse and execute commands until we are done
  Command* cmd;
  if( options.interactive ) {
    // cout << "CVC4> " << flush;
  }
  while((cmd = parser->nextCommand())) {
    if( !options.parseOnly ) {
      doCommand(smt, cmd);
    }
    delete cmd;
  }

  string result = smt.getInfo(":status").getValue();
  int returnValue;

  if(result == "sat") {
    returnValue = 10;
  } else if(result == "unsat") {
    returnValue = 20;
  } else {
    returnValue = 0;
  }

#ifdef CVC4_COMPETITION_MODE
  // exit, don't return
  // (don't want destructors to run)
  exit(returnValue);
#endif

  // Remove the parser
  delete parser;

  ReferenceStat< Result > s_statSatResult("sat/unsat", result);
  StatisticsRegistry::registerStat(&s_statSatResult);

  if(options.statistics){
    StatisticsRegistry::flushStatistics(cerr);
  }

  StatisticsRegistry::unregisterStat(&s_statSatResult);
  StatisticsRegistry::unregisterStat(&s_statFilename);

  return returnValue;
}

void doCommand(SmtEngine& smt, Command* cmd) {
  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    for(CommandSequence::iterator subcmd = seq->begin();
        subcmd != seq->end();
        ++subcmd) {
      doCommand(smt, *subcmd);
    }
  } else {
    if(options.verbosity > 0) {
      cout << "Invoking: " << *cmd << endl;
    }

    if(options.verbosity >= 0) {
      cmd->invoke(&smt, cout);
    } else {
      cmd->invoke(&smt);
    }
  }
}

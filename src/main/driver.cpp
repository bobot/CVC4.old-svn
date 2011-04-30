#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <new>

#include <stdio.h>
#include <unistd.h>

#include "cvc4autoconfig.h"
#include "main/main.h"
#include "main/interactive_shell.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "expr/command.h"
#include "util/Assert.h"
#include "util/configuration.h"
#include "util/options.h"
#include "util/output.h"
#include "util/result.h"
#include "util/stats.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

//int runCvc4(int argc, char* argv[]);
void doCommand(SmtEngine&, Command*, Options&);
//void printUsage();

namespace CVC4 {
  namespace main {/* Global options variable */
    CVC4_THREADLOCAL(Options*) pOptions;

    /** Full argv[0] */
    const char *progPath;

    /** Just the basename component of argv[0] */
    const char *progName;

    /** A pointer to the StatisticsRegistry (the signal handlers need it) */
    CVC4_THREADLOCAL(CVC4::StatisticsRegistry*) pStatistics;
  }
}


// no more % chars in here without being escaped; it's used as a
// printf() format string
const string usageMessage = "\
usage: %s [options] [input-file]\n\
\n\
Without an input file, or with `-', CVC4 reads from standard input.\n\
\n\
CVC4 options:\n";

void printUsage(Options& options) {
  stringstream ss;
  ss << "usage: " << options.binary_name << " [options] [input-file]" << endl
      << endl
      << "Without an input file, or with `-', CVC4 reads from standard input." << endl
      << endl
      << "CVC4 options:" << endl;
  Options::printUsage( ss.str(), *options.out );
}

int runCvc4(int argc, char* argv[], Options& options) {

  // For the signal handlers' benefit
  pOptions = &options;

  // Initialize the signal handlers
  cvc4_init();

  progPath = argv[0];

  // Parse the options
  int firstArgIndex = options.parseOptions(argc, argv);

  progName = options.binary_name.c_str();

  if( options.help ) {
    printUsage(options);
    exit(1);
  } else if( options.languageHelp ) {
    Options::printLanguageHelp(*options.out);
    exit(1);
  } else if( options.version ) {
    *options.out << Configuration::about().c_str() << flush;
    exit(0);
  }

  segvNoSpin = options.segvNoSpin;

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC4_COMPETITION_MODE
  *options.out << unitbuf;
#endif

  // We only accept one input file
  if(argc > firstArgIndex + 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin =
    firstArgIndex >= argc || !strcmp("-", argv[firstArgIndex]);

  // if we're reading from stdin on a TTY, default to interactive mode
  if(!options.interactiveSetByUser) {
    options.interactive = inputFromStdin && isatty(fileno(stdin));
  }

  // Create the expression manager
  ExprManager exprMgr(options);

  // Create the SmtEngine
  SmtEngine smt(&exprMgr);

  // signal handlers need access
  pStatistics = smt.getStatisticsRegistry();

  // Auto-detect input language by filename extension
  const char* filename = inputFromStdin ? "<stdin>" : argv[firstArgIndex];

  ReferenceStat< const char* > s_statFilename("filename", filename);
  RegisterStatistic statFilenameReg(exprMgr, &s_statFilename);

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


  // Parse and execute commands until we are done
  Command* cmd;
  if( options.interactive ) {
    InteractiveShell shell(exprMgr,options);
    while((cmd = shell.readCommand())) {
      doCommand(smt,cmd, options);
      delete cmd;
    }
  } else {
    ParserBuilder parserBuilder =
      ParserBuilder(&exprMgr, filename, options);

    if( inputFromStdin ) {
      parserBuilder.withStreamInput(cin);
    }

    Parser *parser = parserBuilder.build();
    while((cmd = parser->nextCommand())) {
      doCommand(smt, cmd, options);
      delete cmd;
    }
    // Remove the parser
    delete parser;
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

  ReferenceStat< Result > s_statSatResult("sat/unsat", result);
  RegisterStatistic statSatResultReg(exprMgr, &s_statSatResult);

  if(options.statistics) {
    pStatistics->flushStatistics(*options.err);
  }

  return returnValue;
}

/** Executes a command. Deletes the command after execution. */
void doCommand(SmtEngine& smt, Command* cmd, Options& options) {
  if( options.parseOnly ) {
    return;
  }

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    for(CommandSequence::iterator subcmd = seq->begin();
        subcmd != seq->end();
        ++subcmd) {
      doCommand(smt, *subcmd, options);
    }
  } else {
    if(options.verbosity > 0) {
      *options.out << "Invoking: " << *cmd << endl;
    }

    if(options.verbosity >= 0) {
      cmd->invoke(&smt, *options.out);
    } else {
      cmd->invoke(&smt);
    }
  }
}

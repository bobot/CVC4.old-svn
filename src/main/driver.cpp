/*********************                                                        */
/*! \file driver.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): barrett, dejan, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011, 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Driver for (sequential) CVC4 executable
 **
 ** Driver for (sequential) CVC4 executable.
 **/

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
#include "options/options.h"
#include "main/options.h"
#include "smt/options.h"
#include "theory/uf/options.h"
#include "util/output.h"
#include "util/dump.h"
#include "util/result.h"
#include "util/stats.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

static bool doCommand(SmtEngine&, Command*, Options&);

namespace CVC4 {
  namespace main {
    /** Global options variable */
    CVC4_THREADLOCAL(Options*) pOptions;

    /** Full argv[0] */
    const char *progPath;

    /** Just the basename component of argv[0] */
    const char *progName;

    /** A pointer to the StatisticsRegistry (the signal handlers need it) */
    CVC4::StatisticsRegistry* pStatistics;
  }
}


void printUsage(Options& opts, bool full) {
  stringstream ss;
  ss << "usage: " << opts[options::binary_name] << " [options] [input-file]" << endl
      << endl
      << "Without an input file, or with `-', CVC4 reads from standard input." << endl
      << endl
      << "CVC4 options:" << endl;
  if(full) {
    Options::printUsage( ss.str(), *opts[options::out] );
  } else {
    Options::printShortUsage( ss.str(), *opts[options::out] );
  }
}

int runCvc4(int argc, char* argv[], Options& opts) {

  // For the signal handlers' benefit
  pOptions = &opts;

  // Initialize the signal handlers
  cvc4_init();

  progPath = argv[0];

  // Parse the options
  int firstArgIndex = opts.parseOptions(argc, argv);

  progName = opts[options::binary_name].c_str();

  if( opts[options::help] ) {
    printUsage(opts, true);
    exit(1);
  } else if( opts[options::languageHelp] ) {
    Options::printLanguageHelp(*opts[options::out]);
    exit(1);
  } else if( opts[options::version] ) {
    *opts[options::out] << Configuration::about().c_str() << flush;
    exit(0);
  }

  segvNoSpin = opts[options::segvNoSpin];

  // If in competition mode, set output stream option to flush immediately
#ifdef CVC4_COMPETITION_MODE
  *opts[options::out] << unitbuf;
#endif

  // We only accept one input file
  if(argc > firstArgIndex + 1) {
    throw Exception("Too many input files specified.");
  }

  // If no file supplied we will read from standard input
  const bool inputFromStdin =
    firstArgIndex >= argc || !strcmp("-", argv[firstArgIndex]);

  // if we're reading from stdin on a TTY, default to interactive mode
  if(!opts[options::interactiveSetByUser]) {
    opts.set(options::interactive, inputFromStdin && isatty(fileno(stdin)));
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    Debug.setStream(CVC4::null_os);
    Trace.setStream(CVC4::null_os);
    Notice.setStream(CVC4::null_os);
    Chat.setStream(CVC4::null_os);
    Message.setStream(CVC4::null_os);
    Warning.setStream(CVC4::null_os);
    Dump.setStream(CVC4::null_os);
  } else {
    if(opts[options::verbosity] < 2) {
      Chat.setStream(CVC4::null_os);
    }
    if(opts[options::verbosity] < 1) {
      Notice.setStream(CVC4::null_os);
    }
    if(opts[options::verbosity] < 0) {
      Message.setStream(CVC4::null_os);
      Warning.setStream(CVC4::null_os);
    }
  }

  // Create the expression manager
  ExprManager exprMgr(opts);

  // Create the SmtEngine
  SmtEngine smt(&exprMgr);

  // signal handlers need access
  pStatistics = smt.getStatisticsRegistry();

  // Auto-detect input language by filename extension
  const char* filename = inputFromStdin ? "<stdin>" : argv[firstArgIndex];

  ReferenceStat< const char* > s_statFilename("filename", filename);
  RegisterStatistic statFilenameReg(exprMgr, &s_statFilename);

  if(opts[options::inputLanguage] == language::input::LANG_AUTO) {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      opts.set(options::inputLanguage, language::input::LANG_CVC4);
    } else {
      unsigned len = strlen(filename);
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        opts.set(options::inputLanguage, language::input::LANG_SMTLIB_V2);
      } else if(len >= 4 && !strcmp(".smt", filename + len - 4)) {
        opts.set(options::inputLanguage, language::input::LANG_SMTLIB);
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        opts.set(options::inputLanguage, language::input::LANG_CVC4);
      }
    }
  }

  if(opts[options::outputLanguage] == language::output::LANG_AUTO) {
    opts.set(options::outputLanguage, language::toOutputLanguage(opts[options::inputLanguage]));
  }

  // Determine which messages to show based on smtcomp_mode and verbosity
  if(Configuration::isMuzzledBuild()) {
    Debug.setStream(CVC4::null_os);
    Trace.setStream(CVC4::null_os);
    Notice.setStream(CVC4::null_os);
    Chat.setStream(CVC4::null_os);
    Message.setStream(CVC4::null_os);
    Warning.setStream(CVC4::null_os);
    Dump.setStream(CVC4::null_os);
  } else {
    if(opts[options::verbosity] < 2) {
      Chat.setStream(CVC4::null_os);
    }
    if(opts[options::verbosity] < 1) {
      Notice.setStream(CVC4::null_os);
    }
    if(opts[options::verbosity] < 0) {
      Message.setStream(CVC4::null_os);
      Warning.setStream(CVC4::null_os);
    }

    Debug.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Trace.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Notice.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Chat.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Message.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Warning.getStream() << Expr::setlanguage(opts[options::outputLanguage]);
    Dump.getStream() << Expr::setlanguage(opts[options::outputLanguage])
                     << Expr::setdepth(-1)
                     << Expr::printtypes(false);
  }

  Parser* replayParser = NULL;
  if( opts[options::replayFilename] != "" ) {
    ParserBuilder replayParserBuilder(&exprMgr, opts[options::replayFilename], opts);

    if( opts[options::replayFilename] == "-") {
      if( inputFromStdin ) {
        throw OptionException("Replay file and input file can't both be stdin.");
      }
      replayParserBuilder.withStreamInput(cin);
    }
    replayParser = replayParserBuilder.build();
    opts.set(options::replayStream, new Parser::ExprStream(replayParser));
  }
  if( opts[options::replayLog] != NULL ) {
    *opts[options::replayLog] << Expr::setlanguage(opts[options::outputLanguage]) << Expr::setdepth(-1);
  }

  // Parse and execute commands until we are done
  Command* cmd;
  bool status = true;
  if( opts[options::interactive] ) {
    InteractiveShell shell(exprMgr, opts);
    Message() << Configuration::getPackageName()
              << " " << Configuration::getVersionString();
    if(Configuration::isSubversionBuild()) {
      Message() << " [" << Configuration::getSubversionId() << "]";
    }
    Message() << (Configuration::isDebugBuild() ? " DEBUG" : "")
              << " assertions:"
              << (Configuration::isAssertionBuild() ? "on" : "off")
              << endl;
    if(replayParser != NULL) {
      // have the replay parser use the declarations input interactively
      replayParser->useDeclarationsFrom(shell.getParser());
    }
    while((cmd = shell.readCommand())) {
      status = doCommand(smt,cmd, opts) && status;
      delete cmd;
    }
  } else {
    ParserBuilder parserBuilder(&exprMgr, filename, opts);

    if( inputFromStdin ) {
      parserBuilder.withLineBufferedStreamInput(cin);
    }

    Parser *parser = parserBuilder.build();
    if(replayParser != NULL) {
      // have the replay parser use the file's declarations
      replayParser->useDeclarationsFrom(parser);
    }
    while((cmd = parser->nextCommand())) {
      status = doCommand(smt, cmd, opts) && status;
      delete cmd;
    }
    // Remove the parser
    delete parser;
  }

  if( opts[options::replayStream] != NULL ) {
    // this deletes the expression parser too
    delete opts[options::replayStream];
    opts.set(options::replayStream, NULL);
  }

  int returnValue;
  string result = "unknown";
  if(status) {
    result = smt.getInfo("status").getValue();

    if(result == "sat") {
      returnValue = 10;
    } else if(result == "unsat") {
      returnValue = 20;
    } else {
      returnValue = 0;
    }
  } else {
    // there was some kind of error
    returnValue = 1;
  }

#ifdef CVC4_COMPETITION_MODE
  // exit, don't return
  // (don't want destructors to run)
  exit(returnValue);
#endif

  ReferenceStat< Result > s_statSatResult("sat/unsat", result);
  RegisterStatistic statSatResultReg(exprMgr, &s_statSatResult);

  if(opts[options::statistics]) {
    pStatistics->flushInformation(*opts[options::err]);
  }

  return returnValue;
}

/** Executes a command. Deletes the command after execution. */
static bool doCommand(SmtEngine& smt, Command* cmd, Options& opts) {
  if( opts[options::parseOnly] ) {
    return true;
  }

  // assume no error
  bool status = true;

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    for(CommandSequence::iterator subcmd = seq->begin();
        subcmd != seq->end();
        ++subcmd) {
      status = doCommand(smt, *subcmd, opts) && status;
    }
  } else {
    if(opts[options::verbosity] > 0) {
      *opts[options::out] << "Invoking: " << *cmd << endl;
    }

    if(opts[options::verbosity] >= 0) {
      cmd->invoke(&smt, *opts[options::out]);
    } else {
      cmd->invoke(&smt);
    }
    status = status && cmd->ok();
  }

  return status;
}

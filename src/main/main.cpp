/*********************                                                        */
/*! \file main.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
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
#include "util/options.h"
#include "util/result.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::main;

static Result lastResult;
static struct Options options;

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

uint64_t gmpAllocations, gmpReallocations, gmpFree;
inline void * allocate_function (size_t alloc_size ){
  gmpAllocations++;
  return malloc(alloc_size);

}
inline void* realloc_func_ptr(void *ptr, size_t oldSize, size_t newSize){
  gmpReallocations++;
  return realloc(ptr, newSize);
}
inline void free_function (void *ptr, size_t size ){
  gmpFree++;
  free(ptr);
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

  gmpAllocations = gmpReallocations = gmpFree = 0;
  mp_set_memory_functions (&allocate_function, &realloc_func_ptr, &free_function);

  // Create the expression manager
  ExprManager exprMgr;




  // Create the SmtEngine
  SmtEngine smt(&exprMgr, &options);

  // If no file supplied we read from standard input
  bool inputFromStdin = 
    firstArgIndex >= argc || !strcmp("-", argv[firstArgIndex]);

  // Auto-detect input language by filename extension
  const char* filename = inputFromStdin ? "<stdin>" : argv[firstArgIndex];

  if(options.lang == parser::LANG_AUTO) {
    if( inputFromStdin ) {
      // We can't do any fancy detection on stdin
      options.lang = parser::LANG_CVC4;
    } else {
      unsigned len = strlen(filename);
      if(len >= 5 && !strcmp(".smt2", filename + len - 5)) {
        options.lang = parser::LANG_SMTLIB_V2;
      } else if(len >= 4 && !strcmp(".smt", filename + len - 4)) {
        options.lang = parser::LANG_SMTLIB;
      } else if(( len >= 4 && !strcmp(".cvc", filename + len - 4) )
                || ( len >= 5 && !strcmp(".cvc4", filename + len - 5) )) {
        options.lang = parser::LANG_CVC4;
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
  }

  ParserBuilder parserBuilder =
      ParserBuilder(exprMgr, filename)
        .withInputLanguage(options.lang)
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
  while((cmd = parser->nextCommand())) {
    if( !options.parseOnly ) {
      doCommand(smt, cmd);
    }
    delete cmd;
  }

  // Get ready for tear-down
  exprMgr.prepareToBeDestroyed();

  // Remove the parser
  delete parser;

  cout << "==== begin gmp statistics ====" << endl;
  cout << "gmpAllocations " << gmpAllocations << endl;
  cout << "gmpReallocations " << gmpReallocations << endl;
  cout << "gmpFree " << gmpFree << endl;
  cout << "==== end gmp statistics ====" << endl;


  switch(lastResult.asSatisfiabilityResult().isSAT()) {

  case Result::SAT:
    return 10;

  case Result::UNSAT:
    return 20;

  default:
    return 0;

  }

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

    cmd->invoke(&smt);

    QueryCommand *qc = dynamic_cast<QueryCommand*>(cmd);
    if(qc != NULL) {
      lastResult = qc->getResult();
      if(options.verbosity >= 0) {
        cout << lastResult << endl;
      }
    } else {
      CheckSatCommand *csc = dynamic_cast<CheckSatCommand*>(cmd);
      if(csc != NULL) {
        lastResult = csc->getResult();
        if(options.verbosity >= 0) {
          cout << lastResult << endl;
        }
      }
    }
  }
}

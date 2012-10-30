/*********************                                                        */
/*! \file main.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): barrett, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Main driver for CVC4 executable
 **
 ** Main driver for CVC4 executable.
 **/

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>

#include <stdio.h>
#include <unistd.h>

#include "main/main.h"
#include "main/interactive_shell.h"
#include "main/command_executor.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "expr/expr_manager.h"
#include "smt/smt_engine.h"
#include "expr/command.h"
#include "util/configuration.h"
#include "main/options.h"
#include "theory/uf/options.h"
#include "util/output.h"
#include "util/result.h"
#include "util/statistics.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::main;

/**
 * CVC4's main() routine is just an exception-safe wrapper around CVC4.
 * Please don't construct anything here.  Even if the constructor is
 * inside the try { }, an exception during destruction can cause
 * problems.  That's why main() wraps runCvc4() in the first place.
 * Put everything in runCvc4().
 */
int main(int argc, char* argv[]) {
  Options opts;
  try {
    return runCvc4(argc, argv, opts);
  } catch(OptionException& e) {
#ifdef CVC4_COMPETITION_MODE
    *opts[options::out] << "unknown" << endl;
#endif
    cerr << "CVC4 Error:" << endl << e << endl << endl
         << "Please use --help to get help on command-line options."
         << endl;
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    *opts[options::out] << "unknown" << endl;
#endif
    *opts[options::err] << "CVC4 Error:" << endl << e << endl;
    if(opts[options::statistics] && pExecutor != NULL) {
      pExecutor->flushStatistics(*opts[options::err]);
    }
  }
  exit(1);
}

/*********************                                                        */
/*! \file main.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): barrett, dejan, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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

#include "main.h"
#include "util/stats.h"

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
  Options options;
  try {
    return runCvc4(argc, argv, options);
  } catch(OptionException& e) {
#ifdef CVC4_COMPETITION_MODE
    *options.out << "unknown" << endl;
#endif
    cerr << "CVC4 Error:" << endl << e << endl;
    printUsage(options);
    exit(1);
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    *options.out << "unknown" << endl;
#endif
    *options.err << "CVC4 Error:" << endl << e << endl;
    if(options.statistics && pStatistics != NULL) {
      pStatistics->flushInformation(*options.err);
    }
    exit(1);
  } catch(bad_alloc) {
#ifdef CVC4_COMPETITION_MODE
    *options.out << "unknown" << endl;
#endif
    *options.err << "CVC4 ran out of memory." << endl;
    if(options.statistics && pStatistics != NULL) {
      pStatistics->flushInformation(*options.err);
    }
    exit(1);
  } catch(...) {
#ifdef CVC4_COMPETITION_MODE
    *options.out << "unknown" << endl;
#endif
    *options.err << "CVC4 threw an exception of unknown type." << endl;
    exit(1);
  }
}

/*********************                                                        */
/*! \file Assert.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): acsys
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Assertion utility classes, functions, and exceptions.
 **
 ** Assertion utility classes, functions, and exceptions.  Implementation.
 **/

#include <new>
#include <cstdarg>
#include <cstdio>

#include "util/Assert.h"

using namespace std;

namespace CVC4 {

#ifdef CVC4_DEBUG
CVC4_PUBLIC CVC4_THREADLOCAL(const char*) s_debugLastException = NULL;
#endif /* CVC4_DEBUG */

void AssertionException::construct(const char* header, const char* extra,
                                   const char* function, const char* file,
                                   unsigned line, const char* fmt,
                                   va_list args) {
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 512;
  char* buf;

  for(;;) {
    buf = new char[n];

    int size;
    if(extra == NULL) {
      size = snprintf(buf, n, "%s\n%s\n%s:%d\n",
                      header, function, file, line);
    } else {
      size = snprintf(buf, n, "%s\n%s\n%s:%d:\n\n  %s\n",
                      header, function, file, line, extra);
    }

    if(size < n) {
      va_list args_copy;
      va_copy(args_copy, args);
      size += vsnprintf(buf + size, n - size, fmt, args_copy);
      va_end(args_copy);

      if(size < n) {
        break;
      }
    }

    if(size >= n) {
      // try again with a buffer that's large enough
      n = size + 1;
      delete [] buf;
    }
  }

  setMessage(string(buf));

#ifdef CVC4_DEBUG
  if(s_debugLastException == NULL) {
    // we leak buf[] but only in debug mode with assertions failing
    s_debugLastException = buf;
  }
#else /* CVC4_DEBUG */
  delete [] buf;
#endif /* CVC4_DEBUG */
}

void AssertionException::construct(const char* header, const char* extra,
                                   const char* function, const char* file,
                                   unsigned line) {
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 256;
  char* buf;

  for(;;) {
    buf = new char[n];

    int size;
    if(extra == NULL) {
      size = snprintf(buf, n, "%s.\n%s\n%s:%d\n",
                      header, function, file, line);
    } else {
      size = snprintf(buf, n, "%s.\n%s\n%s:%d:\n\n  %s\n",
                      header, function, file, line, extra);
    }

    if(size < n) {
      break;
    } else {
      // try again with a buffer that's large enough
      n = size + 1;
      delete [] buf;
    }
  }

  setMessage(string(buf));

#ifdef CVC4_DEBUG
  // we leak buf[] but only in debug mode with assertions failing
  if(s_debugLastException == NULL) {
    s_debugLastException = buf;
  }
#else /* CVC4_DEBUG */
  delete [] buf;
#endif /* CVC4_DEBUG */
}

#ifdef CVC4_DEBUG

/**
 * Special assertion failure handling in debug mode; in non-debug
 * builds, the exception is thrown from the macro.  We factor out this
 * additional logic so as not to bloat the code at every Assert()
 * expansion.
 *
 * Note this name is prefixed with "debug" because it is included in
 * debug builds only; in debug builds, it handles all assertion
 * failures (even those that exist in non-debug builds).
 */
void debugAssertionFailed(const AssertionException& thisException,
                          const char* propagatingException) {
  static CVC4_THREADLOCAL(bool) alreadyFired = false;

  if(EXPECT_TRUE( !std::uncaught_exception() ) || alreadyFired) {
    throw thisException;
  }

  alreadyFired = true;

  // propagatingException is the propagating exception, but can be
  // NULL if the propagating exception is not a CVC4::Exception.
  Warning() << "===========================================" << std::endl
            << "An assertion failed during stack unwinding:" << std::endl;
  if(propagatingException != NULL) {
    Warning() << "The propagating exception is:" << std::endl
              << propagatingException << std::endl
              << "===========================================" << std::endl;
    Warning() << "The newly-thrown exception is:" << std::endl;
  } else {
    Warning() << "The propagating exception is unknown." << std::endl;
  }
  Warning() << thisException << std::endl
            << "===========================================" << std::endl;

  terminate();
}

#endif /* CVC4_DEBUG */

}/* CVC4 namespace */

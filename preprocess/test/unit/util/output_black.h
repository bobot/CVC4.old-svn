/*********************                                                        */
/*! \file output_black.h
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
 ** \brief Black box testing of CVC4 output classes.
 **
 ** Black box testing of CVC4 output classes.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <sstream>

#include "util/output.h"

using namespace CVC4;
using namespace std;

class OutputBlack : public CxxTest::TestSuite {

  stringstream d_debugStream;
  stringstream d_traceStream;
  stringstream d_noticeStream;
  stringstream d_chatStream;
  stringstream d_messageStream;
  stringstream d_warningStream;

public:

  void setUp() {
    Debug.setStream(d_debugStream);
    Trace.setStream(d_traceStream);
    Notice.setStream(d_noticeStream);
    Chat.setStream(d_chatStream);
    Message.setStream(d_messageStream);
    Warning.setStream(d_warningStream);

    d_debugStream.str("");
    d_traceStream.str("");
    d_noticeStream.str("");
    d_chatStream.str("");
    d_messageStream.str("");
    d_warningStream.str("");
  }

  void tearDown() {
  }

  void testOutput() {
    Debug.on("foo");
    Debug("foo") << "testing1";
    Debug.off("foo");
    Debug("foo") << "testing2";
    Debug.on("foo");
    Debug("foo") << "testing3";

    Message() << "a message";
    Warning() << "bad warning!";
    Chat() << "chatty";
    Notice() << "note";

    Trace.on("foo");
    Trace("foo") << "tracing1";
    Trace.off("foo");
    Trace("foo") << "tracing2";
    Trace.on("foo");
    Trace("foo") << "tracing3";

#ifdef CVC4_MUZZLE

    TS_ASSERT( d_debugStream.str() == "" );
    TS_ASSERT( d_messageStream.str() == "" );
    TS_ASSERT( d_warningStream.str() == "" );
    TS_ASSERT( d_chatStream.str() == "" );
    TS_ASSERT( d_noticeStream.str() == "" );
    TS_ASSERT( d_traceStream.str() == "" );

#else /* CVC4_MUZZLE */

#  ifdef CVC4_DEBUG
    TS_ASSERT( d_debugStream.str() == "testing1testing3" );
#  else /* CVC4_DEBUG */
    TS_ASSERT( d_debugStream.str() == "" );
#  endif /* CVC4_DEBUG */

    TS_ASSERT( d_messageStream.str() == "a message" );
    TS_ASSERT( d_warningStream.str() == "bad warning!" );
    TS_ASSERT( d_chatStream.str() == "chatty" );
    TS_ASSERT( d_noticeStream.str() == "note" );

#  ifdef CVC4_TRACING
    TS_ASSERT( d_traceStream.str() == "tracing1tracing3" );
#  else /* CVC4_TRACING */
    TS_ASSERT( d_traceStream.str() == "" );
#  endif /* CVC4_TRACING */

#endif /* CVC4_MUZZLE */
  }

  void testPrintf() {

#ifdef CVC4_MUZZLE

    Debug.off("yo");
    Debug.printf("yo", "hello %s", "world");
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");
    Debug.printf(string("yo"), "hello %s", "world");
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");

    Debug.on("yo");
    Debug.printf("yo", "hello %s", "world");
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");
    Debug.printf(string("yo"), "hello %s", "world");
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");

    Trace.off("yo");
    Trace.printf("yo", "hello %s", "world");
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
    d_traceStream.str("");
    Trace.printf(string("yo"), "hello %s", "world");
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
    d_traceStream.str("");

    Trace.on("yo");
    Trace.printf("yo", "hello %s", "world");
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
    d_traceStream.str("");
    Trace.printf(string("yo"), "hello %s", "world");
    TS_ASSERT_EQUALS(d_traceStream.str(), string());

    Warning.printf("hello %s", "world");
    TS_ASSERT_EQUALS(d_warningStream.str(), string());

    Chat.printf("hello %s", "world");
    TS_ASSERT_EQUALS(d_chatStream.str(), string());

    Message.printf("hello %s", "world");
    TS_ASSERT_EQUALS(d_messageStream.str(), string());

    Notice.printf("hello %s", "world");
    TS_ASSERT_EQUALS(d_noticeStream.str(), string());

#else /* CVC4_MUZZLE */

    Debug.off("yo");
    Debug.printf("yo", "hello %s", "world");
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");
    Debug.printf(string("yo"), "hello %s", "world");
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");

    Debug.on("yo");
    Debug.printf("yo", "hello %s", "world");
#ifdef CVC4_DEBUG
    TS_ASSERT_EQUALS(d_debugStream.str(), string("hello world"));
#else /* CVC4_DEBUG */
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
#endif /* CVC4_DEBUG */
    d_debugStream.str("");
    Debug.printf(string("yo"), "hello %s", "world");
#ifdef CVC4_DEBUG
    TS_ASSERT_EQUALS(d_debugStream.str(), string("hello world"));
#else /* CVC4_DEBUG */
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
#endif /* CVC4_DEBUG */
    d_debugStream.str("");

    Trace.off("yo");
    Trace.printf("yo", "hello %s", "world");
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
    d_traceStream.str("");
    Trace.printf(string("yo"), "hello %s", "world");
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
    d_traceStream.str("");

    Trace.on("yo");
    Trace.printf("yo", "hello %s", "world");
#ifdef CVC4_TRACING
    TS_ASSERT_EQUALS(d_traceStream.str(), string("hello world"));
#else /* CVC4_TRACING */
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
#endif /* CVC4_TRACING */
    d_traceStream.str("");
    Trace.printf(string("yo"), "hello %s", "world");
#ifdef CVC4_TRACING
    TS_ASSERT_EQUALS(d_traceStream.str(), string("hello world"));
#else /* CVC4_TRACING */
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
#endif /* CVC4_TRACING */

    Warning.printf("hello %s", "world");
    TS_ASSERT_EQUALS(d_warningStream.str(), string("hello world"));

    Chat.printf("hello %s", "world");
    TS_ASSERT_EQUALS(d_chatStream.str(), string("hello world"));

    Message.printf("hello %s", "world");
    TS_ASSERT_EQUALS(d_messageStream.str(), string("hello world"));

    Notice.printf("hello %s", "world");
    TS_ASSERT_EQUALS(d_noticeStream.str(), string("hello world"));

#endif /* CVC4_MUZZLE */

  }

  static int expensiveFunction() {
    // this represents an expensive function that should NOT be called
    // when debugging/tracing is turned off
    TS_FAIL("a function was evaluated under Debug() or Trace() when it should not have been");
    return 0;
  }

  void testEvaluationOffWhenItsSupposedToBe() {
    Trace.on("foo");
#ifndef CVC4_TRACING
    TS_ASSERT( !( Trace.isOn("foo") ) );
    Trace("foo") << expensiveFunction() << endl;
#else /* CVC4_TRACING */
    TS_ASSERT( Trace.isOn("foo") );
#endif /* CVC4_TRACING */

    Debug.on("foo");
#ifndef CVC4_DEBUG
    TS_ASSERT( !( Debug.isOn("foo") ) );
    Debug("foo") << expensiveFunction() << endl;
#else /* CVC4_DEBUG */
    TS_ASSERT( Debug.isOn("foo") );
#endif /* CVC4_DEBUG */
  }

  void testSimplePrint() {

#ifdef CVC4_MUZZLE

    Debug.off("yo");
    Debug("yo", "foobar");
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");
    Debug.on("yo");
    Debug("yo", "baz foo");
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");

    Trace.off("yo");
    Trace("yo", "foobar");
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
    d_traceStream.str("");
    Trace.on("yo");
    Trace("yo", "baz foo");
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
    d_traceStream.str("");

    Warning("baz foo");
    TS_ASSERT_EQUALS(d_warningStream.str(), string());
    d_warningStream.str("");

    Chat("baz foo");
    TS_ASSERT_EQUALS(d_chatStream.str(), string());
    d_chatStream.str("");

    Message("baz foo");
    TS_ASSERT_EQUALS(d_messageStream.str(), string());
    d_messageStream.str("");

    Notice("baz foo");
    TS_ASSERT_EQUALS(d_noticeStream.str(), string());
    d_noticeStream.str("");

#else /* CVC4_MUZZLE */

    Debug.off("yo");
    Debug("yo") << "foobar";
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
    d_debugStream.str("");
    Debug.on("yo");
    Debug("yo") << "baz foo";
#  ifdef CVC4_DEBUG
    TS_ASSERT_EQUALS(d_debugStream.str(), string("baz foo"));
#  else /* CVC4_DEBUG */
    TS_ASSERT_EQUALS(d_debugStream.str(), string());
#  endif /* CVC4_DEBUG */
    d_debugStream.str("");

    Trace.off("yo");
    Trace("yo") << "foobar";
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
    d_traceStream.str("");
    Trace.on("yo");
    Trace("yo") << "baz foo";
#  ifdef CVC4_TRACING
    TS_ASSERT_EQUALS(d_traceStream.str(), string("baz foo"));
#  else /* CVC4_TRACING */
    TS_ASSERT_EQUALS(d_traceStream.str(), string());
#  endif /* CVC4_TRACING */
    d_traceStream.str("");

    Warning() << "baz foo";
    TS_ASSERT_EQUALS(d_warningStream.str(), string("baz foo"));
    d_warningStream.str("");

    Chat() << "baz foo";
    TS_ASSERT_EQUALS(d_chatStream.str(), string("baz foo"));
    d_chatStream.str("");

    Message() << "baz foo";
    TS_ASSERT_EQUALS(d_messageStream.str(), string("baz foo"));
    d_messageStream.str("");

    Notice() << "baz foo";
    TS_ASSERT_EQUALS(d_noticeStream.str(), string("baz foo"));
    d_noticeStream.str("");

#endif /* CVC4_MUZZLE */

  }
};

/*********************                                                        */
/** exception_black.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::Exception.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <sstream>

#include "util/exception.h"

using namespace CVC4;
using namespace std;

class ExceptionBlack : public CxxTest::TestSuite {
public:

  void setUp() {
  }

  void tearDown() {
  }

  // CVC4::Exception is a simple class, just test it all at once.
  void testExceptions() {
    Exception e1;
    Exception e2(string("foo!"));
    Exception e3("bar!");

    TS_ASSERT_EQUALS(e1.toString(), string("Unknown exception"));
    TS_ASSERT_EQUALS(e2.toString(), string("foo!"));
    TS_ASSERT_EQUALS(e3.toString(), string("bar!"));

    e1.setMessage("blah");
    e2.setMessage("another");
    e3.setMessage("three of 'em!");

    stringstream s1, s2, s3;
    s1 << e1;
    s2 << e2;
    s3 << e3;

    TS_ASSERT_EQUALS(s1.str(), string("blah"));
    TS_ASSERT_EQUALS(s2.str(), string("another"));
    TS_ASSERT_EQUALS(s3.str(), string("three of 'em!"));
  }
};

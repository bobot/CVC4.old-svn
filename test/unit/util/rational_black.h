/*********************                                                        */
/*! \file rational_black.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Rational.
 **
 ** Black box testing of CVC4::Rational.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "util/rational.h"

using namespace CVC4;
using namespace std;

const char* canReduce = "4547897890548754897897897897890789078907890/54878902347890234";

class RationalBlack : public CxxTest::TestSuite {
public:

  void testFromDecimal() {
    TS_ASSERT_EQUALS( Rational(0l,1l), Rational::fromDecimal("0") );
    TS_ASSERT_EQUALS( Rational(1l,1l), Rational::fromDecimal("1") );
    TS_ASSERT_EQUALS( Rational(-1l,1l), Rational::fromDecimal("-1") );
    TS_ASSERT_EQUALS( Rational(3l,2l), Rational::fromDecimal("1.5") );
    TS_ASSERT_EQUALS( Rational(-3l,2l), Rational::fromDecimal("-1.5") );
    TS_ASSERT_EQUALS( Rational(7l,10l), Rational::fromDecimal(".7") );
    TS_ASSERT_EQUALS( Rational(-7l,10l), Rational::fromDecimal("-.7") );
    TS_ASSERT_EQUALS( Rational(5l,1l), Rational::fromDecimal("5.") );
    TS_ASSERT_EQUALS( Rational(-5l,1l), Rational::fromDecimal("-5.") );
    TS_ASSERT_EQUALS( Rational(12345l,100ll), Rational::fromDecimal("123.45") );

    TS_ASSERT_THROWS( Rational::fromDecimal("1.2.3");, const std::invalid_argument& );
    TS_ASSERT_THROWS( Rational::fromDecimal("1.2/3");, const std::invalid_argument& );
    TS_ASSERT_THROWS( Rational::fromDecimal("Hello, world!");, const std::invalid_argument& );
  }

};

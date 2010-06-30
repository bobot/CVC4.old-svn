/*********************                                                        */
/*! \file integer_black.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): cconway, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Integer.
 **
 ** Black box testing of CVC4::Integer.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "util/integer.h"

using namespace CVC4;
using namespace std;

const char* largeVal = "4547897890548754897897897897890789078907890";

class IntegerBlack : public CxxTest::TestSuite {


public:

  void testConstructors() {
    Integer z0(1l);
    TS_ASSERT_EQUALS(z0.getLong(), 1);

    Integer z1(0l);
    TS_ASSERT_EQUALS(z1.getLong(), 0);

    Integer z2(-1l);
    TS_ASSERT_EQUALS(z2.getLong(), -1);

    Integer z3(0x890UL);
    TS_ASSERT_EQUALS(z3.getUnsignedLong(), 0x890UL);

    Integer z4;
    TS_ASSERT_EQUALS(z4.getLong(), 0);

    Integer z5("7896890");
    TS_ASSERT_EQUALS(z5.getUnsignedLong(), 7896890ul);

    Integer z6(z5);
    TS_ASSERT_EQUALS(z5.getUnsignedLong(), 7896890ul);
    TS_ASSERT_EQUALS(z6.getUnsignedLong(), 7896890ul);


    string bigValue("1536729");
    Integer z7(bigValue);
    TS_ASSERT_EQUALS(z7.getUnsignedLong(), 1536729ul);
  }

  void testCompareAgainstZero(){
    Integer z(0l);
    TS_ASSERT_THROWS_NOTHING(z == 0l;);
    TS_ASSERT_EQUALS(z,0l);
  }

  void testOperatorAssign(){
    Integer x(0l);
    Integer y(79l);
    Integer z(45789l);

    TS_ASSERT_EQUALS(x.getUnsignedLong(), 0ul);
    TS_ASSERT_EQUALS(y.getUnsignedLong(), 79ul);
    TS_ASSERT_EQUALS(z.getUnsignedLong(), 45789ul);

    x = y = z;

    TS_ASSERT_EQUALS(x.getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(y.getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(z.getUnsignedLong(), 45789ul);

    Integer a(2l);

    y = a;

    TS_ASSERT_EQUALS(a.getUnsignedLong(), 2ul);
    TS_ASSERT_EQUALS(y.getUnsignedLong(), 2ul);
    TS_ASSERT_EQUALS(x.getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(z.getUnsignedLong(), 45789ul);
  }

  void testOperatorEquals(){
    Integer a(0l);
    Integer b(79l);
    Integer c("79");
    Integer d;

    TS_ASSERT( (a==a));
    TS_ASSERT(!(a==b));
    TS_ASSERT(!(a==c));
    TS_ASSERT( (a==d));

    TS_ASSERT(!(b==a));
    TS_ASSERT( (b==b));
    TS_ASSERT( (b==c));
    TS_ASSERT(!(b==d));

    TS_ASSERT(!(c==a));
    TS_ASSERT( (c==b));
    TS_ASSERT( (c==c));
    TS_ASSERT(!(c==d));

    TS_ASSERT( (d==a));
    TS_ASSERT(!(d==b));
    TS_ASSERT(!(d==c));
    TS_ASSERT( (d==d));

  }

  void testOperatorNotEquals(){
    Integer a(0l);
    Integer b(79l);
    Integer c("79");
    Integer d;

    TS_ASSERT(!(a!=a));
    TS_ASSERT( (a!=b));
    TS_ASSERT( (a!=c));
    TS_ASSERT(!(a!=d));

    TS_ASSERT( (b!=a));
    TS_ASSERT(!(b!=b));
    TS_ASSERT(!(b!=c));
    TS_ASSERT( (b!=d));

    TS_ASSERT( (c!=a));
    TS_ASSERT(!(c!=b));
    TS_ASSERT(!(c!=c));
    TS_ASSERT( (c!=d));

    TS_ASSERT(!(d!=a));
    TS_ASSERT( (d!=b));
    TS_ASSERT( (d!=c));
    TS_ASSERT(!(d!=d));

  }

  void testOperatorSubtract(){
    Integer x(0l);
    Integer y(79l);
    Integer z(-34l);


    Integer act0 = x - x;
    Integer act1 = x - y;
    Integer act2 = x - z;
    Integer exp0(0l);
    Integer exp1(-79l);
    Integer exp2(34l);


    Integer act3 = y - x;
    Integer act4 = y - y;
    Integer act5 = y - z;
    Integer exp3(79l);
    Integer exp4(0l);
    Integer exp5(113l);


    Integer act6 = z - x;
    Integer act7 = z - y;
    Integer act8 = z - z;
    Integer exp6(-34l);
    Integer exp7(-113l);
    Integer exp8(0l);



    TS_ASSERT_EQUALS(act0, exp0);
    TS_ASSERT_EQUALS(act1, exp1);
    TS_ASSERT_EQUALS(act2, exp2);
    TS_ASSERT_EQUALS(act3, exp3);
    TS_ASSERT_EQUALS(act4, exp4);
    TS_ASSERT_EQUALS(act5, exp5);
    TS_ASSERT_EQUALS(act6, exp6);
    TS_ASSERT_EQUALS(act7, exp7);
    TS_ASSERT_EQUALS(act8, exp8);
  }
  void testOperatorAdd(){
    Integer x(0l);
    Integer y(79l);
    Integer z(-34l);


    Integer act0 = x + x;
    Integer act1 = x + y;
    Integer act2 = x + z;
    Integer exp0(0l);
    Integer exp1(79l);
    Integer exp2(-34l);


    Integer act3 = y + x;
    Integer act4 = y + y;
    Integer act5 = y + z;
    Integer exp3(79l);
    Integer exp4(158l);
    Integer exp5(45l);


    Integer act6 = z + x;
    Integer act7 = z + y;
    Integer act8 = z + z;
    Integer exp6(-34l);
    Integer exp7(45l);
    Integer exp8(-68l);



    TS_ASSERT_EQUALS(act0, exp0);
    TS_ASSERT_EQUALS(act1, exp1);
    TS_ASSERT_EQUALS(act2, exp2);
    TS_ASSERT_EQUALS(act3, exp3);
    TS_ASSERT_EQUALS(act4, exp4);
    TS_ASSERT_EQUALS(act5, exp5);
    TS_ASSERT_EQUALS(act6, exp6);
    TS_ASSERT_EQUALS(act7, exp7);
    TS_ASSERT_EQUALS(act8, exp8);
  }

  void testOperatorMult(){
    Integer x(0l);
    Integer y(79l);
    Integer z(-34l);


    Integer act0 = x * x;
    Integer act1 = x * y;
    Integer act2 = x * z;
    Integer exp0(0l);
    Integer exp1(0l);
    Integer exp2(0l);


    Integer act3 = y * x;
    Integer act4 = y * y;
    Integer act5 = y * z;
    Integer exp3(0l);
    Integer exp4(6241l);
    Integer exp5(-2686l);


    Integer act6 = z * x;
    Integer act7 = z * y;
    Integer act8 = z * z;
    Integer exp6(0l);
    Integer exp7(-2686l);
    Integer exp8(1156l);



    TS_ASSERT_EQUALS(act0, exp0);
    TS_ASSERT_EQUALS(act1, exp1);
    TS_ASSERT_EQUALS(act2, exp2);
    TS_ASSERT_EQUALS(act3, exp3);
    TS_ASSERT_EQUALS(act4, exp4);
    TS_ASSERT_EQUALS(act5, exp5);
    TS_ASSERT_EQUALS(act6, exp6);
    TS_ASSERT_EQUALS(act7, exp7);
    TS_ASSERT_EQUALS(act8, exp8);
  }


  void testToStringStuff(){
    stringstream ss;
    Integer large (largeVal);
    ss << large;
    string res = ss.str();

    TS_ASSERT_EQUALS(res, large.toString());
  }

  void testPow() {
    TS_ASSERT_EQUALS( Integer(1l), Integer(1l).pow(0) );
    TS_ASSERT_EQUALS( Integer(1l), Integer(5l).pow(0) );
    TS_ASSERT_EQUALS( Integer(1l), Integer(-1l).pow(0) );
    TS_ASSERT_EQUALS( Integer(0l), Integer(0l).pow(1) );
    TS_ASSERT_EQUALS( Integer(5l), Integer(5l).pow(1) );
    TS_ASSERT_EQUALS( Integer(-5l), Integer(-5l).pow(1) );
    TS_ASSERT_EQUALS( Integer(16l), Integer(2l).pow(4) );
    TS_ASSERT_EQUALS( Integer(16l), Integer(-2l).pow(4) );
    TS_ASSERT_EQUALS( Integer(1000l), Integer(10l).pow(3) );
    TS_ASSERT_EQUALS( Integer(-1000l), Integer(-10l).pow(3) );
  }
};

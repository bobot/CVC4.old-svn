/*********************                                                        */
/*! \file integer_white.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of CVC4::Integer.
 **
 ** White box testing of CVC4::Integer.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "util/integer.h"

using namespace CVC4;
using namespace std;

const char* largeVal = "4547897890548754897897897897890789078907890";

class IntegerWhite : public CxxTest::TestSuite {
public:

  void testHash(){
    Integer large (largeVal);
    Integer zero;
    Integer fits_in_2_bytes(55890);
    Integer fits_in_16_bytes("7890D789D33234027890D789D3323402", 16);


    TS_ASSERT_THROWS_NOTHING(zero.hash());
    TS_ASSERT_THROWS_NOTHING(fits_in_2_bytes.hash());
    TS_ASSERT_THROWS_NOTHING(fits_in_16_bytes.hash());
    TS_ASSERT_THROWS_NOTHING(large.hash());
  }
};

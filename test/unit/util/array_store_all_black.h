/*********************                                                        */
/*! \file array_store_all_black.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::ArrayStoreAll
 **
 ** Black box testing of CVC4::ArrayStoreAll.
 **/

#include <cxxtest/TestSuite.h>

#include "util/array_store_all.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/type.h"
#include "expr/expr.h"

using namespace CVC4;
using namespace std;

class ArrayStoreAllBlack : public CxxTest::TestSuite {

  ExprManager* d_em;
  ExprManagerScope* d_scope;

public:

  void setUp() {
    d_em = new ExprManager();
    d_scope = new ExprManagerScope(*d_em);
  }

  void tearDown() {
    delete d_scope;
    delete d_em;
  }

  void testStoreAll() {
    Type usort = d_em->mkSort("U");
    ArrayStoreAll(d_em->mkArrayType(d_em->integerType(), d_em->realType()), d_em->mkConst(Rational(9, 2)));
    ArrayStoreAll(d_em->mkArrayType(d_em->mkSort("U"), usort), d_em->mkVar(usort));
    ArrayStoreAll(d_em->mkArrayType(d_em->mkSort("U"), usort), d_em->mkConst(UninterpretedConstant(usort, 0)));
    ArrayStoreAll(d_em->mkArrayType(d_em->mkBitVectorType(8), d_em->realType()), d_em->mkConst(Rational(0)));
    ArrayStoreAll(d_em->mkArrayType(d_em->mkBitVectorType(8), d_em->integerType()), d_em->mkConst(Rational(0)));
  }

  void testTypeErrors() {
    // these two throw an AssertionException in assertions-enabled builds, and an IllegalArgumentException in production builds
    TS_ASSERT_THROWS_ANYTHING( ArrayStoreAll(d_em->integerType(), d_em->mkConst(UninterpretedConstant(d_em->mkSort("U"), 0))) );
    TS_ASSERT_THROWS_ANYTHING( ArrayStoreAll(d_em->integerType(), d_em->mkConst(Rational(9, 2))) );

    TS_ASSERT_THROWS( ArrayStoreAll(d_em->mkArrayType(d_em->integerType(), d_em->integerType()), d_em->mkConst(Rational(9, 2))), IllegalArgumentException );
    TS_ASSERT_THROWS( ArrayStoreAll(d_em->mkArrayType(d_em->integerType(), d_em->mkSort("U")), d_em->mkConst(Rational(9, 2))), IllegalArgumentException );
    TS_ASSERT_THROWS( ArrayStoreAll(d_em->mkArrayType(d_em->realType(), d_em->integerType()), d_em->mkConst(Rational(9, 2))), IllegalArgumentException );
  }

};/* class ArrayStoreAllBlack */

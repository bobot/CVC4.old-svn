/*********************                                                        */
/*! \file theory_black.h
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::theory
 **
 ** Black box testing of CVC4::theory
 **/

#include <cxxtest/TestSuite.h>

//Used in some of the tests
#include <vector>
#include <sstream>

#include "expr/expr_manager.h"
#include "expr/node_value.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::smt;

class TheoryBlack : public CxxTest::TestSuite {
private:

  ExprManager* d_em;
  SmtEngine* d_smt;
  NodeManager* d_nm;
  SmtScope* d_scope;

public:

  void setUp() {
    d_em = new ExprManager();
    d_smt = new SmtEngine(d_em);
    d_nm = NodeManager::fromExprManager(d_em);
    d_scope = new SmtScope(d_smt);
  }

  void tearDown() {
    delete d_em;
  }

  void testArrayConst() {
    TypeNode arrType = d_nm->mkArrayType(d_nm->integerType(), d_nm->integerType());
    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node storeAll = d_nm->mkConst(ArrayStoreAll(arrType.toType(), zero.toExpr()));
    TS_ASSERT(storeAll.isConst());

    Node arr = d_nm->mkNode(STORE, storeAll, zero, zero);
    TS_ASSERT(!arr.isConst());
    arr = Rewriter::rewrite(arr);
    TS_ASSERT(arr.isConst());
    arr = d_nm->mkNode(STORE, storeAll, zero, one);
    TS_ASSERT(arr.isConst());
    Node arr2 = d_nm->mkNode(STORE, arr, one, zero);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, one);
    TS_ASSERT(arr2.isConst());
    arr2 = d_nm->mkNode(STORE, arr, zero, one);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());

    arrType = d_nm->mkArrayType(d_nm->mkBitVectorType(1), d_nm->mkBitVectorType(1));
    zero = d_nm->mkConst(BitVector(1,unsigned(0)));
    one = d_nm->mkConst(BitVector(1,unsigned(1)));
    storeAll = d_nm->mkConst(ArrayStoreAll(arrType.toType(), zero.toExpr()));
    TS_ASSERT(storeAll.isConst());

    arr = d_nm->mkNode(STORE, storeAll, zero, zero);
    TS_ASSERT(!arr.isConst());
    arr = Rewriter::rewrite(arr);
    TS_ASSERT(arr.isConst());
    arr = d_nm->mkNode(STORE, storeAll, zero, one);
    TS_ASSERT(arr.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, zero);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, one);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());
    arr2 = d_nm->mkNode(STORE, arr, zero, one);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());

    arrType = d_nm->mkArrayType(d_nm->mkBitVectorType(2), d_nm->mkBitVectorType(2));
    zero = d_nm->mkConst(BitVector(2,unsigned(0)));
    one = d_nm->mkConst(BitVector(2,unsigned(1)));
    Node two = d_nm->mkConst(BitVector(2,unsigned(2)));
    Node three = d_nm->mkConst(BitVector(2,unsigned(3)));
    storeAll = d_nm->mkConst(ArrayStoreAll(arrType.toType(), one.toExpr()));
    TS_ASSERT(storeAll.isConst());

    arr = d_nm->mkNode(STORE, storeAll, zero, zero);
    TS_ASSERT(arr.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, zero);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());

    arr = d_nm->mkNode(STORE, storeAll, one, three);
    TS_ASSERT(arr.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, one);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2 == storeAll);

    arr2 = d_nm->mkNode(STORE, arr, zero, zero);
    TS_ASSERT(!arr2.isConst());
    TS_ASSERT(Rewriter::rewrite(arr2).isConst());
    arr2 = d_nm->mkNode(STORE, arr2, two, two);
    TS_ASSERT(!arr2.isConst());
    TS_ASSERT(Rewriter::rewrite(arr2).isConst());
    arr2 = d_nm->mkNode(STORE, arr2, three, one);
    TS_ASSERT(!arr2.isConst());
    TS_ASSERT(Rewriter::rewrite(arr2).isConst());
    arr2 = d_nm->mkNode(STORE, arr2, three, three);
    TS_ASSERT(!arr2.isConst());
    TS_ASSERT(Rewriter::rewrite(arr2).isConst());
    arr2 = d_nm->mkNode(STORE, arr2, two, zero);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());

  }

};

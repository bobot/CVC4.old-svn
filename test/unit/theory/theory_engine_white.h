/*********************                                                        */
/*! \file theory_engine_white.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of CVC4::theory::Theory.
 **
 ** White box testing of CVC4::theory::Theory.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <string>
#include <deque>

#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/theoryof_table.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/kind.h"
#include "context/context.h"
#include "util/rational.h"
#include "util/integer.h"
#include "util/Assert.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::expr;
using namespace CVC4::context;
using namespace CVC4::kind;

using namespace std;

class FakeOutputChannel : public OutputChannel {
  void conflict(TNode n, bool safe) throw(AssertionException) {
    Unimplemented();
  }
  void propagate(TNode n, bool safe) throw(AssertionException) {
    Unimplemented();
  }
  void lemma(TNode n, bool safe) throw(AssertionException) {
    Unimplemented();
  }
  void augmentingLemma(TNode n, bool safe) throw(AssertionException) {
    Unimplemented();
  }
  void explanation(TNode n, bool safe) throw(AssertionException) {
    Unimplemented();
  }
};/* class FakeOutputChannel */

class FakeTheory;

enum RewriteType {
  PRE,
  POST
};/* enum RewriteType */

struct RewriteItem {
  RewriteType d_type;
  FakeTheory* d_theory;
  Node d_node;
  bool d_topLevel;
};/* struct RewriteItem */

class FakeTheory : public Theory {
  std::string d_id;

  static std::deque<RewriteItem> s_expected;

public:
  FakeTheory(context::Context* ctxt, OutputChannel& out, std::string id) :
    Theory(ctxt, out),
    d_id(id) {
  }

  static void expect(RewriteType type, FakeTheory* thy,
                     TNode n, bool topLevel) throw() {
    RewriteItem item = { type, thy, n, topLevel };
    s_expected.push_back(item);
  }

  static bool nothingMoreExpected() throw() {
    return s_expected.empty();
  }

  RewriteResponse preRewrite(TNode n, bool topLevel) {
    if(s_expected.empty()) {
      cout << std::endl
           << "didn't expect anything more, but got" << std::endl
           << "     PRE  " << topLevel << " " << identify() << " " << n << std::endl;
    }
    TS_ASSERT(!s_expected.empty());

    RewriteItem expected = s_expected.front();
    s_expected.pop_front();

    if(expected.d_type != PRE ||
       expected.d_theory != this ||
       expected.d_node != n ||
       expected.d_topLevel != topLevel) {
      cout << std::endl
           << "HAVE PRE  " << topLevel << " " << identify() << " " << n << std::endl
           << "WANT " << (expected.d_type == PRE ? "PRE  " : "POST ") << expected.d_topLevel << " " << expected.d_theory->identify() << " " << expected.d_node << std::endl << std::endl;
    }

    TS_ASSERT_EQUALS(expected.d_type, PRE);
    TS_ASSERT_EQUALS(expected.d_theory, this);
    TS_ASSERT_EQUALS(expected.d_node, n);
    TS_ASSERT_EQUALS(expected.d_topLevel, topLevel);

    return RewriteComplete(n);
  }

  RewriteResponse postRewrite(TNode n, bool topLevel) {
    if(s_expected.empty()) {
      cout << std::endl
           << "didn't expect anything more, but got" << std::endl
           << "     POST " << topLevel << " " << identify() << " " << n << std::endl;
    }
    TS_ASSERT(!s_expected.empty());

    RewriteItem expected = s_expected.front();
    s_expected.pop_front();

    if(expected.d_type != POST ||
       expected.d_theory != this ||
       expected.d_node != n ||
       expected.d_topLevel != topLevel) {
      cout << std::endl
           << "HAVE POST " << topLevel << " " << identify() << " " << n << std::endl
           << "WANT " << (expected.d_type == PRE ? "PRE  " : "POST ") << expected.d_topLevel << " " << expected.d_theory->identify() << " " << expected.d_node << std::endl << std::endl;
    }

    TS_ASSERT_EQUALS(expected.d_type, POST);
    TS_ASSERT_EQUALS(expected.d_theory, this);
    TS_ASSERT_EQUALS(expected.d_node, n);
    TS_ASSERT_EQUALS(expected.d_topLevel, topLevel);

    return RewriteComplete(n);
  }

  std::string identify() const throw() {
    return "Fake" + d_id;
  }

  void preRegisterTerm(TNode) { Unimplemented(); }
  void registerTerm(TNode) { Unimplemented(); }
  void check(Theory::Effort) { Unimplemented(); }
  void propagate(Theory::Effort) { Unimplemented(); }
  void explain(TNode, Theory::Effort) { Unimplemented(); }
};/* class FakeTheory */

std::deque<RewriteItem> FakeTheory::s_expected;

/**
 * Test the TheoryEngine.
 */
class TheoryEngineWhite : public CxxTest::TestSuite {
  Context* d_ctxt;

  NodeManager* d_nm;
  NodeManagerScope* d_scope;
  FakeOutputChannel *d_nullChannel;
  FakeTheory *d_builtin, *d_bool, *d_uf, *d_arith, *d_arrays, *d_bv;
  TheoryEngine* d_theoryEngine;

public:

  void setUp() {
    d_ctxt = new Context;

    d_nm = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nm);

    d_nullChannel = new FakeOutputChannel;

    d_builtin = new FakeTheory(d_ctxt, *d_nullChannel, "Builtin");
    d_bool = new FakeTheory(d_ctxt, *d_nullChannel, "Bool");
    d_uf = new FakeTheory(d_ctxt, *d_nullChannel, "UF");
    d_arith = new FakeTheory(d_ctxt, *d_nullChannel, "Arith");
    d_arrays = new FakeTheory(d_ctxt, *d_nullChannel, "Arrays");
    d_bv = new FakeTheory(d_ctxt, *d_nullChannel, "BV");

    d_theoryEngine = new TheoryEngine(d_ctxt);

    // insert our fake versions into the theoryOf table
    d_theoryEngine->d_theoryOfTable.
      registerTheory(reinterpret_cast<theory::builtin::TheoryBuiltin*>(d_builtin));
    d_theoryEngine->d_theoryOfTable.
      registerTheory(reinterpret_cast<theory::booleans::TheoryBool*>(d_bool));
    d_theoryEngine->d_theoryOfTable.
      registerTheory(reinterpret_cast<theory::uf::TheoryUF*>(d_uf));
    d_theoryEngine->d_theoryOfTable.
      registerTheory(reinterpret_cast<theory::arith::TheoryArith*>(d_arith));
    d_theoryEngine->d_theoryOfTable.
      registerTheory(reinterpret_cast<theory::arrays::TheoryArrays*>(d_arrays));
    d_theoryEngine->d_theoryOfTable.
      registerTheory(reinterpret_cast<theory::bv::TheoryBV*>(d_bv));

    Debug.on("theory-rewrite");
  }

  void tearDown() {
    delete d_theoryEngine;

    delete d_bv;
    delete d_arrays;
    delete d_arith;
    delete d_uf;
    delete d_bool;
    delete d_builtin;

    delete d_nullChannel;

    delete d_scope;
    delete d_nm;

    delete d_ctxt;
  }

  void testRewriterSimple() {
    Node x = d_nm->mkVar("x", d_nm->integerType());
    Node y = d_nm->mkVar("y", d_nm->integerType());
    Node z = d_nm->mkVar("z", d_nm->integerType());

    // make the expression (PLUS x y (MULT z 0))
    Node zero = d_nm->mkConst(Rational("0"));
    Node zTimesZero = d_nm->mkNode(MULT, z, zero);
    Node n = d_nm->mkNode(PLUS, x, y, zTimesZero);

    Node nExpected = n;
    Node nOut;

    FakeTheory::expect(PRE, d_arith, n, true);
    FakeTheory::expect(PRE, d_arith, x, false);
    FakeTheory::expect(POST, d_arith, x, false);
    FakeTheory::expect(PRE, d_arith, y, false);
    FakeTheory::expect(POST, d_arith, y, false);
    FakeTheory::expect(PRE, d_arith, zTimesZero, false);
    FakeTheory::expect(PRE, d_arith, z, false);
    FakeTheory::expect(POST, d_arith, z, false);
    FakeTheory::expect(PRE, d_arith, zero, false);
    FakeTheory::expect(POST, d_arith, zero, false);
    FakeTheory::expect(POST, d_arith, zTimesZero, false);
    FakeTheory::expect(POST, d_arith, n, true);
    nOut = d_theoryEngine->rewrite(n);
    TS_ASSERT(FakeTheory::nothingMoreExpected());

    TS_ASSERT_EQUALS(nOut, nExpected);
  }

  void testRewriterComplicated() {
    Node x = d_nm->mkVar("x", d_nm->integerType());
    Node y = d_nm->mkVar("y", d_nm->realType());
    Node z1 = d_nm->mkVar("z1", d_nm->mkSort("U"));
    Node z2 = d_nm->mkVar("z2", d_nm->mkSort("U"));
    Node f = d_nm->mkVar("f", d_nm->mkFunctionType(d_nm->integerType(),
                                                   d_nm->integerType()));
    Node g = d_nm->mkVar("g", d_nm->mkFunctionType(d_nm->realType(),
                                                   d_nm->integerType()));
    Node one = d_nm->mkConst(Rational("1"));
    Node two = d_nm->mkConst(Rational("2"));

    Node f1 = d_nm->mkNode(APPLY_UF, f, one);
    Node f2 = d_nm->mkNode(APPLY_UF, f, two);
    Node fx = d_nm->mkNode(APPLY_UF, f, x);
    Node ffx = d_nm->mkNode(APPLY_UF, f, fx);
    Node gy = d_nm->mkNode(APPLY_UF, g, y);
    Node z1eqz2 = d_nm->mkNode(EQUAL, z1, z2);
    Node f1eqf2 = d_nm->mkNode(EQUAL, f1, f2);
    Node ffxeqgy = d_nm->mkNode(EQUAL,
                                ffx,
                                gy);
    Node and1 = d_nm->mkNode(AND, ffxeqgy, z1eqz2, ffx);
    Node ffxeqf1 = d_nm->mkNode(EQUAL, ffx, f1);
    Node or1 = d_nm->mkNode(OR, and1, ffxeqf1);
    // make the expression:
    // (IMPLIES (EQUAL (f 1) (f 2)) (OR (AND (EQUAL (f (f x)) (g y)) (EQUAL z1 z2) (f (f x)))) (EQUAL (f (f x)) (f 1)))
    Node n = d_nm->mkNode(IMPLIES, f1eqf2, or1);
    Node nExpected = n;
    Node nOut;

    // We WOULD expect that the commented-out calls were made, except
    // for the cache
    FakeTheory::expect(PRE, d_bool, n, true);
    FakeTheory::expect(PRE, d_uf, f1eqf2, true);
    FakeTheory::expect(PRE, d_uf, f1, false);
    FakeTheory::expect(PRE, d_builtin, f, true);
    FakeTheory::expect(POST, d_builtin, f, true);
    FakeTheory::expect(PRE, d_arith, one, true);
    FakeTheory::expect(POST, d_arith, one, true);
    FakeTheory::expect(POST, d_uf, f1, false);
    FakeTheory::expect(PRE, d_uf, f2, false);
    //FakeTheory::expect(PRE, d_builtin, f, true);
    //FakeTheory::expect(POST, d_builtin, f, true);
    FakeTheory::expect(PRE, d_arith, two, true);
    FakeTheory::expect(POST, d_arith, two, true);
    FakeTheory::expect(POST, d_uf, f2, false);
    FakeTheory::expect(POST, d_uf, f1eqf2, true);
    FakeTheory::expect(PRE, d_bool, or1, false);
    FakeTheory::expect(PRE, d_bool, and1, false);
    FakeTheory::expect(PRE, d_uf, ffxeqgy, true);
    FakeTheory::expect(PRE, d_uf, ffx, false);
    FakeTheory::expect(PRE, d_uf, fx, false);
    //FakeTheory::expect(PRE, d_builtin, f, true);
    //FakeTheory::expect(POST, d_builtin, f, true);
    FakeTheory::expect(PRE, d_arith, x, true);
    FakeTheory::expect(POST, d_arith, x, true);
    FakeTheory::expect(POST, d_uf, fx, false);
    FakeTheory::expect(POST, d_uf, ffx, false);
    FakeTheory::expect(PRE, d_uf, gy, false);
    FakeTheory::expect(PRE, d_builtin, g, true);
    FakeTheory::expect(POST, d_builtin, g, true);
    FakeTheory::expect(PRE, d_arith, y, true);
    FakeTheory::expect(POST, d_arith, y, true);
    FakeTheory::expect(POST, d_uf, gy, false);
    FakeTheory::expect(POST, d_uf, ffxeqgy, true);
    FakeTheory::expect(PRE, d_uf, z1eqz2, true);
    FakeTheory::expect(PRE, d_uf, z1, false);
    FakeTheory::expect(POST, d_uf, z1, false);
    FakeTheory::expect(PRE, d_uf, z2, false);
    FakeTheory::expect(POST, d_uf, z2, false);
    FakeTheory::expect(POST, d_uf, z1eqz2, true);
    // tricky one: ffx is in cache but for a non-topLevel !
    FakeTheory::expect(PRE, d_uf, ffx, true);
    //FakeTheory::expect(PRE, d_uf, fx, false);
    //FakeTheory::expect(POST, d_uf, fx, false);
    FakeTheory::expect(POST, d_uf, ffx, true);
    FakeTheory::expect(POST, d_bool, and1, false);
    FakeTheory::expect(PRE, d_uf, ffxeqf1, true);
    //FakeTheory::expect(PRE, d_uf, ffx, false);
    //FakeTheory::expect(POST, d_uf, ffx, false);
    //FakeTheory::expect(PRE, d_uf, f1, false);
    //FakeTheory::expect(POST, d_uf, f1, false);
    FakeTheory::expect(POST, d_uf, ffxeqf1, true);
    FakeTheory::expect(POST, d_bool, or1, false);
    FakeTheory::expect(POST, d_bool, n, true);
    nOut = d_theoryEngine->rewrite(n);
    TS_ASSERT(FakeTheory::nothingMoreExpected());

    TS_ASSERT_EQUALS(nOut, nExpected);
  }
};

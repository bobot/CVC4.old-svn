/*********************                                                        */
/*! \file attribute_white.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): cconway, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of Node attributes.
 **
 ** White box testing of Node attributes.
 **/

#include <cxxtest/TestSuite.h>

#include <string>

#include "context/context.h"
#include "expr/node_value.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/attribute.h"
#include "expr/node.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "util/Assert.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::expr;
using namespace CVC4::expr::attr;
using namespace std;

struct Test1;
struct Test2;
struct Test3;
struct Test4;
struct Test5;

typedef Attribute<Test1, std::string> TestStringAttr1;
typedef Attribute<Test2, std::string> TestStringAttr2;

// it would be nice to have CDAttribute<> for context-dependence
typedef CDAttribute<Test1, bool> TestCDFlag;

typedef Attribute<Test1, bool> TestFlag1;
typedef Attribute<Test2, bool> TestFlag2;
typedef Attribute<Test3, bool> TestFlag3;
typedef Attribute<Test4, bool> TestFlag4;
typedef Attribute<Test5, bool> TestFlag5;

typedef CDAttribute<Test1, bool> TestFlag1cd;
typedef CDAttribute<Test2, bool> TestFlag2cd;

class AttributeWhite : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;
  TypeNode* d_booleanType;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nm = new NodeManager(d_ctxt, NULL);
    d_scope = new NodeManagerScope(d_nm);

    d_booleanType = new TypeNode(d_nm->booleanType());
  }

  void tearDown() {
    delete d_booleanType;
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testAttributeIds() {
    // Test that IDs for (a subset of) attributes in the system are
    // unique and that the LastAttributeId (which would be the next ID
    // to assign) is greater than all attribute IDs.

    // We used to check ID assignments explicitly.  However, between
    // compilation modules, you don't get a strong guarantee
    // (initialization order is somewhat implementation-specific, and
    // anyway you'd have to change the tests anytime you add an
    // attribute).  So we back off, and just test that they're unique
    // and that the next ID to be assigned is strictly greater than
    // those that have already been assigned.

    unsigned lastId = attr::LastAttributeId<string, false>::s_id;
    TS_ASSERT_LESS_THAN(VarNameAttr::s_id, lastId);
    TS_ASSERT_LESS_THAN(TestStringAttr1::s_id, lastId);
    TS_ASSERT_LESS_THAN(TestStringAttr2::s_id, lastId);

    TS_ASSERT_DIFFERS(VarNameAttr::s_id, TestStringAttr1::s_id);
    TS_ASSERT_DIFFERS(VarNameAttr::s_id, TestStringAttr2::s_id);
    TS_ASSERT_DIFFERS(TestStringAttr1::s_id, TestStringAttr2::s_id);

    //lastId = attr::LastAttributeId<void*, false>::s_id;
    //TS_ASSERT_LESS_THAN(theory::uf::ECAttr::s_id, lastId);

    lastId = attr::LastAttributeId<bool, false>::s_id;
    TS_ASSERT_LESS_THAN(TestFlag1::s_id, lastId);
    TS_ASSERT_LESS_THAN(TestFlag2::s_id, lastId);
    TS_ASSERT_LESS_THAN(TestFlag3::s_id, lastId);
    TS_ASSERT_LESS_THAN(TestFlag4::s_id, lastId);
    TS_ASSERT_LESS_THAN(TestFlag5::s_id, lastId);
    TS_ASSERT_DIFFERS(TestFlag1::s_id, TestFlag2::s_id);
    TS_ASSERT_DIFFERS(TestFlag1::s_id, TestFlag3::s_id);
    TS_ASSERT_DIFFERS(TestFlag1::s_id, TestFlag4::s_id);
    TS_ASSERT_DIFFERS(TestFlag1::s_id, TestFlag5::s_id);
    TS_ASSERT_DIFFERS(TestFlag2::s_id, TestFlag3::s_id);
    TS_ASSERT_DIFFERS(TestFlag2::s_id, TestFlag4::s_id);
    TS_ASSERT_DIFFERS(TestFlag2::s_id, TestFlag5::s_id);
    TS_ASSERT_DIFFERS(TestFlag3::s_id, TestFlag4::s_id);
    TS_ASSERT_DIFFERS(TestFlag3::s_id, TestFlag5::s_id);
    TS_ASSERT_DIFFERS(TestFlag4::s_id, TestFlag5::s_id);

    lastId = attr::LastAttributeId<bool, true>::s_id;
    TS_ASSERT_LESS_THAN(theory::Asserted::s_id, lastId);
    TS_ASSERT_LESS_THAN(TestFlag1cd::s_id, lastId);
    TS_ASSERT_LESS_THAN(TestFlag2cd::s_id, lastId);
    TS_ASSERT_DIFFERS(theory::Asserted::s_id, TestFlag1cd::s_id);
    TS_ASSERT_DIFFERS(theory::Asserted::s_id, TestFlag2cd::s_id);
    TS_ASSERT_DIFFERS(TestFlag1cd::s_id, TestFlag2cd::s_id);
    cout << "A: " << theory::Asserted::s_id << endl;
    cout << "1: " << TestFlag1cd::s_id << endl;
    cout << "2: " << TestFlag2cd::s_id << endl;

    lastId = attr::LastAttributeId<Node, false>::s_id;
//    TS_ASSERT_LESS_THAN(theory::PreRewriteCache::s_id, lastId);
//    TS_ASSERT_LESS_THAN(theory::PostRewriteCache::s_id, lastId);
//    TS_ASSERT_LESS_THAN(theory::PreRewriteCacheTop::s_id, lastId);
//    TS_ASSERT_LESS_THAN(theory::PostRewriteCacheTop::s_id, lastId);
//    TS_ASSERT_DIFFERS(theory::PreRewriteCache::s_id, theory::PostRewriteCache::s_id);
//    TS_ASSERT_DIFFERS(theory::PreRewriteCache::s_id, theory::PreRewriteCacheTop::s_id);
//    TS_ASSERT_DIFFERS(theory::PreRewriteCache::s_id, theory::PostRewriteCacheTop::s_id);
//    TS_ASSERT_DIFFERS(theory::PostRewriteCache::s_id, theory::PreRewriteCacheTop::s_id);
//    TS_ASSERT_DIFFERS(theory::PostRewriteCache::s_id, theory::PostRewriteCacheTop::s_id);
//    TS_ASSERT_DIFFERS(theory::PreRewriteCacheTop::s_id, theory::PostRewriteCacheTop::s_id);

    lastId = attr::LastAttributeId<TypeNode, false>::s_id;
    TS_ASSERT_LESS_THAN(NodeManager::TypeAttr::s_id, lastId);

  }

  void testCDAttributes() {
    //Debug.on("cdboolattr");

    Node a = d_nm->mkVar(*d_booleanType);
    Node b = d_nm->mkVar(*d_booleanType);
    Node c = d_nm->mkVar(*d_booleanType);

    Debug("cdboolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

    d_ctxt->push(); // level 1

    // test that all boolean flags are FALSE to start
    Debug("cdboolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

    // test that they all HAVE the boolean attributes
    TS_ASSERT(a.hasAttribute(TestFlag1cd()));
    TS_ASSERT(b.hasAttribute(TestFlag1cd()));
    TS_ASSERT(c.hasAttribute(TestFlag1cd()));

    // test two-arg version of hasAttribute()
    bool bb = false;
    Debug("cdboolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(a.getAttribute(TestFlag1cd(), bb));
    TS_ASSERT(! bb);
    Debug("cdboolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(b.getAttribute(TestFlag1cd(), bb));
    TS_ASSERT(! bb);
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(c.getAttribute(TestFlag1cd(), bb));
    TS_ASSERT(! bb);

    // setting boolean flags
    Debug("cdboolattr") << "set flag 1 on a to T\n";
    a.setAttribute(TestFlag1cd(), true);
    Debug("cdboolattr") << "set flag 1 on b to F\n";
    b.setAttribute(TestFlag1cd(), false);
    Debug("cdboolattr") << "set flag 1 on c to F\n";
    c.setAttribute(TestFlag1cd(), false);

    Debug("cdboolattr") << "get flag 1 on a (should be T)\n";
    TS_ASSERT(a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

    d_ctxt->push(); // level 2

    Debug("cdboolattr") << "get flag 1 on a (should be T)\n";
    TS_ASSERT(a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

    Debug("cdboolattr") << "set flag 1 on a to F\n";
    a.setAttribute(TestFlag1cd(), false);
    Debug("cdboolattr") << "set flag 1 on b to T\n";
    b.setAttribute(TestFlag1cd(), true);

    Debug("cdboolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be T)\n";
    TS_ASSERT(b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

    d_ctxt->push(); // level 3

    Debug("cdboolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be T)\n";
    TS_ASSERT(b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

    Debug("cdboolattr") << "set flag 1 on c to T\n";
    c.setAttribute(TestFlag1cd(), true);

    Debug("cdboolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be T)\n";
    TS_ASSERT(b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be T)\n";
    TS_ASSERT(c.getAttribute(TestFlag1cd()));

    d_ctxt->pop(); // level 2

    Debug("cdboolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be T)\n";
    TS_ASSERT(b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

    d_ctxt->pop(); // level 1

    Debug("cdboolattr") << "get flag 1 on a (should be T)\n";
    TS_ASSERT(a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

    d_ctxt->pop(); // level 0

    Debug("cdboolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag1cd()));
    Debug("cdboolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1cd()));

#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS( d_ctxt->pop(), AssertionException );
#endif /* CVC4_ASSERTIONS */
  }

  void testAttributes() {
    //Debug.on("bootattr");

    Node a = d_nm->mkVar(*d_booleanType);
    Node b = d_nm->mkVar(*d_booleanType);
    Node c = d_nm->mkVar(*d_booleanType);
    Node unnamed = d_nm->mkVar(*d_booleanType);

    a.setAttribute(VarNameAttr(), "a");
    b.setAttribute(VarNameAttr(), "b");
    c.setAttribute(VarNameAttr(), "c");

    // test that all boolean flags are FALSE to start
    Debug("boolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag1()));
    Debug("boolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag1()));
    Debug("boolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1()));
    Debug("boolattr") << "get flag 1 on unnamed (should be F)\n";
    TS_ASSERT(! unnamed.getAttribute(TestFlag1()));

    Debug("boolattr") << "get flag 2 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag2()));
    Debug("boolattr") << "get flag 2 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag2()));
    Debug("boolattr") << "get flag 2 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag2()));
    Debug("boolattr") << "get flag 2 on unnamed (should be F)\n";
    TS_ASSERT(! unnamed.getAttribute(TestFlag2()));

    Debug("boolattr") << "get flag 3 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag3()));
    Debug("boolattr") << "get flag 3 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag3()));
    Debug("boolattr") << "get flag 3 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag3()));
    Debug("boolattr") << "get flag 3 on unnamed (should be F)\n";
    TS_ASSERT(! unnamed.getAttribute(TestFlag3()));

    Debug("boolattr") << "get flag 4 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag4()));
    Debug("boolattr") << "get flag 4 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag4()));
    Debug("boolattr") << "get flag 4 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag4()));
    Debug("boolattr") << "get flag 4 on unnamed (should be F)\n";
    TS_ASSERT(! unnamed.getAttribute(TestFlag4()));

    Debug("boolattr") << "get flag 5 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag5()));
    Debug("boolattr") << "get flag 5 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag5()));
    Debug("boolattr") << "get flag 5 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag5()));
    Debug("boolattr") << "get flag 5 on unnamed (should be F)\n";
    TS_ASSERT(! unnamed.getAttribute(TestFlag5()));

    // test that they all HAVE the boolean attributes
    TS_ASSERT(a.hasAttribute(TestFlag1()));
    TS_ASSERT(b.hasAttribute(TestFlag1()));
    TS_ASSERT(c.hasAttribute(TestFlag1()));
    TS_ASSERT(unnamed.hasAttribute(TestFlag1()));

    TS_ASSERT(a.hasAttribute(TestFlag2()));
    TS_ASSERT(b.hasAttribute(TestFlag2()));
    TS_ASSERT(c.hasAttribute(TestFlag2()));
    TS_ASSERT(unnamed.hasAttribute(TestFlag2()));

    TS_ASSERT(a.hasAttribute(TestFlag3()));
    TS_ASSERT(b.hasAttribute(TestFlag3()));
    TS_ASSERT(c.hasAttribute(TestFlag3()));
    TS_ASSERT(unnamed.hasAttribute(TestFlag3()));

    TS_ASSERT(a.hasAttribute(TestFlag4()));
    TS_ASSERT(b.hasAttribute(TestFlag4()));
    TS_ASSERT(c.hasAttribute(TestFlag4()));
    TS_ASSERT(unnamed.hasAttribute(TestFlag4()));

    TS_ASSERT(a.hasAttribute(TestFlag5()));
    TS_ASSERT(b.hasAttribute(TestFlag5()));
    TS_ASSERT(c.hasAttribute(TestFlag5()));
    TS_ASSERT(unnamed.hasAttribute(TestFlag5()));

    // test two-arg version of hasAttribute()
    bool bb;
    Debug("boolattr") << "get flag 1 on a (should be F)\n";
    TS_ASSERT(a.getAttribute(TestFlag1(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(b.getAttribute(TestFlag1(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(c.getAttribute(TestFlag1(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 1 on unnamed (should be F)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag1(), bb));
    TS_ASSERT(! bb);

    Debug("boolattr") << "get flag 2 on a (should be F)\n";
    TS_ASSERT(a.getAttribute(TestFlag2(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 2 on b (should be F)\n";
    TS_ASSERT(b.getAttribute(TestFlag2(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 2 on c (should be F)\n";
    TS_ASSERT(c.getAttribute(TestFlag2(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 2 on unnamed (should be F)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag2(), bb));
    TS_ASSERT(! bb);

    Debug("boolattr") << "get flag 3 on a (should be F)\n";
    TS_ASSERT(a.getAttribute(TestFlag3(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 3 on b (should be F)\n";
    TS_ASSERT(b.getAttribute(TestFlag3(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 3 on c (should be F)\n";
    TS_ASSERT(c.getAttribute(TestFlag3(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 3 on unnamed (should be F)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag3(), bb));
    TS_ASSERT(! bb);

    Debug("boolattr") << "get flag 4 on a (should be F)\n";
    TS_ASSERT(a.getAttribute(TestFlag4(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 4 on b (should be F)\n";
    TS_ASSERT(b.getAttribute(TestFlag4(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 4 on c (should be F)\n";
    TS_ASSERT(c.getAttribute(TestFlag4(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 4 on unnamed (should be F)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag4(), bb));
    TS_ASSERT(! bb);

    Debug("boolattr") << "get flag 5 on a (should be F)\n";
    TS_ASSERT(a.getAttribute(TestFlag5(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 5 on b (should be F)\n";
    TS_ASSERT(b.getAttribute(TestFlag5(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 5 on c (should be F)\n";
    TS_ASSERT(c.getAttribute(TestFlag5(), bb));
    TS_ASSERT(! bb);
    Debug("boolattr") << "get flag 5 on unnamed (should be F)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag5(), bb));
    TS_ASSERT(! bb);

    // setting boolean flags
    Debug("boolattr") << "set flag 1 on a to T\n";
    a.setAttribute(TestFlag1(), true);
    Debug("boolattr") << "set flag 1 on b to F\n";
    b.setAttribute(TestFlag1(), false);
    Debug("boolattr") << "set flag 1 on c to F\n";
    c.setAttribute(TestFlag1(), false);
    Debug("boolattr") << "set flag 1 on unnamed to T\n";
    unnamed.setAttribute(TestFlag1(), true);

    Debug("boolattr") << "set flag 2 on a to F\n";
    a.setAttribute(TestFlag2(), false);
    Debug("boolattr") << "set flag 2 on b to T\n";
    b.setAttribute(TestFlag2(), true);
    Debug("boolattr") << "set flag 2 on c to T\n";
    c.setAttribute(TestFlag2(), true);
    Debug("boolattr") << "set flag 2 on unnamed to F\n";
    unnamed.setAttribute(TestFlag2(), false);

    Debug("boolattr") << "set flag 3 on a to T\n";
    a.setAttribute(TestFlag3(), true);
    Debug("boolattr") << "set flag 3 on b to T\n";
    b.setAttribute(TestFlag3(), true);
    Debug("boolattr") << "set flag 3 on c to T\n";
    c.setAttribute(TestFlag3(), true);
    Debug("boolattr") << "set flag 3 on unnamed to T\n";
    unnamed.setAttribute(TestFlag3(), true);

    Debug("boolattr") << "set flag 4 on a to T\n";
    a.setAttribute(TestFlag4(), true);
    Debug("boolattr") << "set flag 4 on b to T\n";
    b.setAttribute(TestFlag4(), true);
    Debug("boolattr") << "set flag 4 on c to T\n";
    c.setAttribute(TestFlag4(), true);
    Debug("boolattr") << "set flag 4 on unnamed to T\n";
    unnamed.setAttribute(TestFlag4(), true);

    Debug("boolattr") << "set flag 5 on a to T\n";
    a.setAttribute(TestFlag5(), true);
    Debug("boolattr") << "set flag 5 on b to T\n";
    b.setAttribute(TestFlag5(), true);
    Debug("boolattr") << "set flag 5 on c to F\n";
    c.setAttribute(TestFlag5(), false);
    Debug("boolattr") << "set flag 5 on unnamed to T\n";
    unnamed.setAttribute(TestFlag5(), true);

    TS_ASSERT(a.getAttribute(VarNameAttr()) == "a");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(b.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(b.getAttribute(VarNameAttr()) == "b");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(c.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(c.getAttribute(VarNameAttr()) == "c");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) == "");

    TS_ASSERT(! unnamed.hasAttribute(VarNameAttr()));

    TS_ASSERT(! a.hasAttribute(TestStringAttr1()));
    TS_ASSERT(! b.hasAttribute(TestStringAttr1()));
    TS_ASSERT(! c.hasAttribute(TestStringAttr1()));
    TS_ASSERT(! unnamed.hasAttribute(TestStringAttr1()));

    TS_ASSERT(! a.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! b.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! c.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! unnamed.hasAttribute(TestStringAttr2()));

    Debug("boolattr") << "get flag 1 on a (should be T)\n";
    TS_ASSERT(a.getAttribute(TestFlag1()));
    Debug("boolattr") << "get flag 1 on b (should be F)\n";
    TS_ASSERT(! b.getAttribute(TestFlag1()));
    Debug("boolattr") << "get flag 1 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag1()));
    Debug("boolattr") << "get flag 1 on unnamed (should be T)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag1()));

    Debug("boolattr") << "get flag 2 on a (should be F)\n";
    TS_ASSERT(! a.getAttribute(TestFlag2()));
    Debug("boolattr") << "get flag 2 on b (should be T)\n";
    TS_ASSERT(b.getAttribute(TestFlag2()));
    Debug("boolattr") << "get flag 2 on c (should be T)\n";
    TS_ASSERT(c.getAttribute(TestFlag2()));
    Debug("boolattr") << "get flag 2 on unnamed (should be F)\n";
    TS_ASSERT(! unnamed.getAttribute(TestFlag2()));

    Debug("boolattr") << "get flag 3 on a (should be T)\n";
    TS_ASSERT(a.getAttribute(TestFlag3()));
    Debug("boolattr") << "get flag 3 on b (should be T)\n";
    TS_ASSERT(b.getAttribute(TestFlag3()));
    Debug("boolattr") << "get flag 3 on c (should be T)\n";
    TS_ASSERT(c.getAttribute(TestFlag3()));
    Debug("boolattr") << "get flag 3 on unnamed (should be T)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag3()));

    Debug("boolattr") << "get flag 4 on a (should be T)\n";
    TS_ASSERT(a.getAttribute(TestFlag4()));
    Debug("boolattr") << "get flag 4 on b (should be T)\n";
    TS_ASSERT(b.getAttribute(TestFlag4()));
    Debug("boolattr") << "get flag 4 on c (should be T)\n";
    TS_ASSERT(c.getAttribute(TestFlag4()));
    Debug("boolattr") << "get flag 4 on unnamed (should be T)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag4()));

    Debug("boolattr") << "get flag 5 on a (should be T)\n";
    TS_ASSERT(a.getAttribute(TestFlag5()));
    Debug("boolattr") << "get flag 5 on b (should be T)\n";
    TS_ASSERT(b.getAttribute(TestFlag5()));
    Debug("boolattr") << "get flag 5 on c (should be F)\n";
    TS_ASSERT(! c.getAttribute(TestFlag5()));
    Debug("boolattr") << "get flag 5 on unnamed (should be T)\n";
    TS_ASSERT(unnamed.getAttribute(TestFlag5()));

    a.setAttribute(TestStringAttr1(), "foo");
    b.setAttribute(TestStringAttr1(), "bar");
    c.setAttribute(TestStringAttr1(), "baz");

    TS_ASSERT(a.getAttribute(VarNameAttr()) == "a");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(b.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(b.getAttribute(VarNameAttr()) == "b");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(c.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(c.getAttribute(VarNameAttr()) == "c");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) == "");

    TS_ASSERT(! unnamed.hasAttribute(VarNameAttr()));

    TS_ASSERT(a.hasAttribute(TestStringAttr1()));
    TS_ASSERT(b.hasAttribute(TestStringAttr1()));
    TS_ASSERT(c.hasAttribute(TestStringAttr1()));
    TS_ASSERT(! unnamed.hasAttribute(TestStringAttr1()));

    TS_ASSERT(! a.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! b.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! c.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! unnamed.hasAttribute(TestStringAttr2()));

    a.setAttribute(VarNameAttr(), "b");
    b.setAttribute(VarNameAttr(), "c");
    c.setAttribute(VarNameAttr(), "a");

    TS_ASSERT(c.getAttribute(VarNameAttr()) == "a");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(a.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(a.getAttribute(VarNameAttr()) == "b");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(b.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(b.getAttribute(VarNameAttr()) == "c");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) == "");

    TS_ASSERT(! unnamed.hasAttribute(VarNameAttr()));
  }
};

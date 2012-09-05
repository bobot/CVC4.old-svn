/*********************                                                        */
/*! \file attribute_black.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: taking
 ** Minor contributors (to current version): cconway, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Attribute.
 **
 ** Black box testing of CVC4::Attribute.
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
#include "expr/attribute.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;

class AttributeBlack : public CxxTest::TestSuite {
private:

  Context* d_ctxt;
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nodeManager = new NodeManager(d_ctxt, NULL);
    d_scope = new NodeManagerScope(d_nodeManager);
  }

  void tearDown() {
    delete d_scope;
    delete d_nodeManager;
    delete d_ctxt;
  }

  class MyData {
  public:
    static int count;
    MyData()  { count ++; }
    ~MyData() { count --; }
  };

  struct MyDataAttributeId {};

  struct MyDataCleanupFunction {
    static void cleanup(MyData* myData){
      delete myData;
    }
  };

  typedef expr::Attribute<MyDataAttributeId, MyData*, MyDataCleanupFunction> MyDataAttribute;

  void testDeallocation() {
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem(booleanType));
    MyData* data;
    MyData* data1;
    MyDataAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data));
    node->setAttribute(attr, new MyData());
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT(MyData::count == 1);
    delete node;
  }

  struct PrimitiveIntAttributeId {};
  struct CDPrimitiveIntAttributeId {};

  typedef expr::Attribute<PrimitiveIntAttributeId,uint64_t> PrimitiveIntAttribute;
  typedef expr::CDAttribute<CDPrimitiveIntAttributeId,uint64_t> CDPrimitiveIntAttribute;
  void testInts(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem(booleanType));
    const uint64_t val = 63489;
    uint64_t data0 = 0;
    uint64_t data1 = 0;

    PrimitiveIntAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    uint64_t data2 = 0;
    uint64_t data3 = 0;
    CDPrimitiveIntAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
  }

  struct TNodeAttributeId {};
  struct CDTNodeAttributeId {};

  typedef expr::Attribute<TNodeAttributeId, TNode> TNodeAttribute;
  typedef expr::CDAttribute<CDTNodeAttributeId, TNode> CDTNodeAttribute;
  void testTNodes(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem(booleanType));

    Node val(d_nodeManager->mkSkolem(booleanType));
    TNode data0;
    TNode data1;

    TNodeAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    TNode data2;
    TNode data3;
    CDTNodeAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
  }

  class Foo {
    int blah;
  public:
    Foo(int b) : blah(b) {}
  };

  struct PtrAttributeId {};
  struct CDPtrAttributeId {};

  typedef expr::Attribute<PtrAttributeId, Foo*> PtrAttribute;
  typedef expr::CDAttribute<CDPtrAttributeId, Foo*> CDPtrAttribute;
  void testPtrs(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem(booleanType));

    Foo* val = new Foo(63489);
    Foo* data0 = NULL;
    Foo* data1 = NULL;

    PtrAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    Foo* data2 = NULL;
    Foo* data3 = NULL;
    CDPtrAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
    delete val;
  }


  struct ConstPtrAttributeId {};
  struct CDConstPtrAttributeId {};

  typedef expr::Attribute<ConstPtrAttributeId, const Foo*> ConstPtrAttribute;
  typedef expr::CDAttribute<CDConstPtrAttributeId, const Foo*> CDConstPtrAttribute;
  void testConstPtrs(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem(booleanType));

    const Foo* val = new Foo(63489);
    const Foo* data0 = NULL;
    const Foo* data1 = NULL;

    ConstPtrAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    const Foo* data2 = NULL;
    const Foo* data3 = NULL;
    CDConstPtrAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
    delete val;
  }

  struct StringAttributeId {};
  struct CDStringAttributeId {};

  typedef expr::Attribute<StringAttributeId, std::string> StringAttribute;
  typedef expr::CDAttribute<CDStringAttributeId, std::string> CDStringAttribute;
  void testStrings(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem(booleanType));

    std::string val("63489");
    std::string data0;
    std::string data1;

    StringAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    std::string data2;
    std::string data3;
    CDStringAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
  }

  struct BoolAttributeId {};
  struct CDBoolAttributeId {};

  typedef expr::Attribute<BoolAttributeId, bool> BoolAttribute;
  typedef expr::CDAttribute<CDBoolAttributeId, bool> CDBoolAttribute;
  void testBools(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem(booleanType));

    bool val = true;
    bool data0 = false;
    bool data1 = false;

    BoolAttribute attr;
    TS_ASSERT(node->getAttribute(attr, data0));
    TS_ASSERT_EQUALS(false, data0);
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    bool data2 = false;
    bool data3 = false;
    CDBoolAttribute cdattr;
    TS_ASSERT(node->getAttribute(cdattr, data2));
    TS_ASSERT_EQUALS(false, data2);
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
  }

};

int AttributeBlack::MyData::count = 0;
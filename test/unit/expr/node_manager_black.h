/*********************                                                        */
/** node_manager_black.h
 ** Original author: 
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** White box testing of CVC4::NodeManager.
 **/

#include <cxxtest/TestSuite.h>

#include <string>
#include <vector>

#include "expr/node_manager.h"
#include "context/context.h"

#include "util/rational.h"
#include "util/integer.h"

using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::context;

class NodeManagerBlack : public CxxTest::TestSuite {

  Context* d_context;
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_context = new Context;
    d_nodeManager = new NodeManager(d_context);
    d_scope = new NodeManagerScope(d_nodeManager);
  }

  void tearDown() {
    delete d_scope;
    delete d_nodeManager;
    delete d_context;
  }

  void testMkNodeNot() {
    Node x = d_nodeManager->mkVar("x",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(NOT, x);
    TS_ASSERT_EQUALS( n.getNumChildren(), 1u );
    TS_ASSERT_EQUALS( n.getKind(), NOT);
    TS_ASSERT_EQUALS( n[0], x);
  }

  void testMkNodeBinary() {
    Node x = d_nodeManager->mkVar("x",d_nodeManager->booleanType());
    Node y = d_nodeManager->mkVar("y",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(IMPLIES, x, y);
    TS_ASSERT_EQUALS( n.getNumChildren(), 2u );
    TS_ASSERT_EQUALS( n.getKind(), IMPLIES);
    TS_ASSERT_EQUALS( n[0], x);
    TS_ASSERT_EQUALS( n[1], y);
  }

  void testMkNodeThreeChildren() {
    Node x = d_nodeManager->mkVar("x",d_nodeManager->booleanType());
    Node y = d_nodeManager->mkVar("y",d_nodeManager->booleanType());
    Node z = d_nodeManager->mkVar("z",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x, y, z);
    TS_ASSERT_EQUALS( n.getNumChildren(), 3u );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    TS_ASSERT_EQUALS( n[0], x);
    TS_ASSERT_EQUALS( n[1], y);
    TS_ASSERT_EQUALS( n[2], z);
  }

  void testMkNodeFourChildren() {
    Node x1 = d_nodeManager->mkVar("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkVar("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkVar("x3",d_nodeManager->booleanType());
    Node x4 = d_nodeManager->mkVar("x4",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x1, x2, x3, x4);
    TS_ASSERT_EQUALS( n.getNumChildren(), 4u );
    TS_ASSERT_EQUALS( n.getKind(), AND );
    TS_ASSERT_EQUALS( n[0], x1 );
    TS_ASSERT_EQUALS( n[1], x2 );
    TS_ASSERT_EQUALS( n[2], x3 );
    TS_ASSERT_EQUALS( n[3], x4 );
  }

  void testMkNodeFiveChildren() {
    Node x1 = d_nodeManager->mkVar("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkVar("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkVar("x3",d_nodeManager->booleanType());
    Node x4 = d_nodeManager->mkVar("x4",d_nodeManager->booleanType());
    Node x5 = d_nodeManager->mkVar("x5",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x1, x2, x3, x4, x5);
    TS_ASSERT_EQUALS( n.getNumChildren(), 5u );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    TS_ASSERT_EQUALS( n[0], x1);
    TS_ASSERT_EQUALS( n[1], x2);
    TS_ASSERT_EQUALS( n[2], x3);
    TS_ASSERT_EQUALS( n[3], x4);
    TS_ASSERT_EQUALS( n[4], x5);
  }

  void testMkNodeVectorOfNodeChildren() {
    Node x1 = d_nodeManager->mkVar("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkVar("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkVar("x3",d_nodeManager->booleanType());
    std::vector<Node> args;
    args.push_back(x1);
    args.push_back(x2);
    args.push_back(x3);
    Node n = d_nodeManager->mkNode(AND, args);
    TS_ASSERT_EQUALS( n.getNumChildren(), args.size() );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    for( unsigned i = 0; i < args.size(); ++i ) {
      TS_ASSERT_EQUALS( n[i], args[i]);
    }
  }

  void testMkNodeVectorOfTNodeChildren() {
    Node x1 = d_nodeManager->mkVar("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkVar("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkVar("x3",d_nodeManager->booleanType());
    std::vector<TNode> args;
    args.push_back(x1);
    args.push_back(x2);
    args.push_back(x3);
    Node n = d_nodeManager->mkNode(AND, args);
    TS_ASSERT_EQUALS( n.getNumChildren(), args.size() );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    for( unsigned i = 0; i < args.size(); ++i ) {
      TS_ASSERT_EQUALS( n[i], args[i]);
    }
  }

  void testMkVarWithNoName() {
    Type booleanType = d_nodeManager->booleanType();
    Node x = d_nodeManager->mkVar(booleanType);
    TS_ASSERT_EQUALS(x.getKind(),VARIABLE);
    TS_ASSERT_EQUALS(x.getNumChildren(),0u);
    TS_ASSERT_EQUALS(x.getType(),booleanType);
  }

  void testMkVarWithName() {
    Type booleanType = d_nodeManager->booleanType();
    Node x = d_nodeManager->mkVar("x", booleanType);
    TS_ASSERT_EQUALS(x.getKind(),VARIABLE);
    TS_ASSERT_EQUALS(x.getNumChildren(),0u);
    TS_ASSERT_EQUALS(x.getAttribute(VarNameAttr()),"x");
    TS_ASSERT_EQUALS(x.getType(),booleanType);
  }

  void testMkConstBool() {
    Node tt = d_nodeManager->mkConst(true);
    TS_ASSERT_EQUALS(tt.getConst<bool>(),true);
    Node ff = d_nodeManager->mkConst(false);
    TS_ASSERT_EQUALS(ff.getConst<bool>(),false);
  }


  void testMkConstInt() {
    Integer i = "3";
    Node n = d_nodeManager->mkConst(i);
    TS_ASSERT_EQUALS(n.getConst<Integer>(),i);
  }

  void testMkConstRat() {
    Rational r = "3/2";
    Node n = d_nodeManager->mkConst(r);
    TS_ASSERT_EQUALS(n.getConst<Rational>(),r);
  }

  void testHasOperator() {
    TS_ASSERT( NodeManager::hasOperator(AND) );
    TS_ASSERT( NodeManager::hasOperator(OR) );
    TS_ASSERT( NodeManager::hasOperator(NOT) );
    TS_ASSERT( NodeManager::hasOperator(APPLY_UF) );
    TS_ASSERT( !NodeManager::hasOperator(VARIABLE) );
  }

  void testBooleanType() {
    Type t = d_nodeManager->booleanType();
    Type t2 = d_nodeManager->booleanType();
    Type t3 = d_nodeManager->mkSort("T");
    TS_ASSERT( t.isBoolean() );
    TS_ASSERT( !t.isFunction() );
    TS_ASSERT( !t.isKind() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( !t.isPredicate() );
    TS_ASSERT( !t.isSort() );
    TS_ASSERT_EQUALS(t, t2);
    TS_ASSERT( t != t3 );

    BooleanType bt = t;
    TS_ASSERT_EQUALS( bt, t);
  }

  void testKindType() {
    Type t = d_nodeManager->kindType();
    Type t2 = d_nodeManager->kindType();
    Type t3 = d_nodeManager->mkSort("T");

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( !t.isFunction() );
    TS_ASSERT( t.isKind() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( !t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS(t, t2);
    TS_ASSERT( t != t3);

    KindType kt = t;
    TS_ASSERT_EQUALS( kt, t );
    // TODO: Is there a way to get the type of otherType (it should == t)?
  }

  void testMkFunctionTypeBoolToBool() {
    Type booleanType = d_nodeManager->booleanType();
    Type t = d_nodeManager->mkFunctionType(booleanType,booleanType);
    Type t2 = d_nodeManager->mkFunctionType(booleanType,booleanType);

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( t.isFunction() );
    TS_ASSERT( !t.isKind() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS( t, t2 );

    FunctionType ft = t;
    TS_ASSERT_EQUALS( ft, t );
    TS_ASSERT_EQUALS(ft.getArgTypes().size(), 1u);
    TS_ASSERT_EQUALS(ft.getArgTypes()[0], booleanType);
    TS_ASSERT_EQUALS(ft.getRangeType(), booleanType);

  }

  void testMkFunctionTypeVectorOfArgsWithReturnType() {
    Type a = d_nodeManager->mkSort();
    Type b = d_nodeManager->mkSort();
    Type c = d_nodeManager->mkSort();

    std::vector<Type> argTypes;
    argTypes.push_back(a);
    argTypes.push_back(b);

    Type t = d_nodeManager->mkFunctionType(argTypes,c);
    Type t2 = d_nodeManager->mkFunctionType(argTypes,c);

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( t.isFunction() );
    TS_ASSERT( !t.isKind() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( !t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS( t, t2 );

    FunctionType ft = t;
    TS_ASSERT_EQUALS( ft, t );
    TS_ASSERT_EQUALS(ft.getArgTypes().size(), argTypes.size());
    TS_ASSERT_EQUALS(ft.getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft.getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft.getRangeType(), c);

  }

  void testMkFunctionTypeVectorOfArguments() {
    Type a = d_nodeManager->mkSort();
    Type b = d_nodeManager->mkSort();
    Type c = d_nodeManager->mkSort();

    std::vector<Type> types;
    types.push_back(a);
    types.push_back(b);
    types.push_back(c);

    Type t = d_nodeManager->mkFunctionType(types);
    Type t2 = d_nodeManager->mkFunctionType(types);

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( t.isFunction() );
    TS_ASSERT( !t.isKind() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( !t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS( t, t2 );

    FunctionType ft = t;
    TS_ASSERT_EQUALS( ft, t );
    TS_ASSERT_EQUALS(ft.getArgTypes().size(), types.size()-1);
    TS_ASSERT_EQUALS(ft.getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft.getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft.getRangeType(), c);
  }

  void testMkPredicateType() {
    Type a = d_nodeManager->mkSort("a");
    Type b = d_nodeManager->mkSort("b");
    Type c = d_nodeManager->mkSort("c");
    Type booleanType = d_nodeManager->booleanType();

    std::vector<Type> argTypes;
    argTypes.push_back(a);
    argTypes.push_back(b);
    argTypes.push_back(c);

    Type t = d_nodeManager->mkPredicateType(argTypes);
    Type t2 = d_nodeManager->mkPredicateType(argTypes);

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( t.isFunction() );
    TS_ASSERT( !t.isKind() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS( t, t2 );

    FunctionType ft = t;
    TS_ASSERT_EQUALS( ft, t );
    TS_ASSERT_EQUALS(ft.getArgTypes().size(), argTypes.size());
    TS_ASSERT_EQUALS(ft.getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft.getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft.getArgTypes()[2], c);
    TS_ASSERT_EQUALS(ft.getRangeType(), booleanType);

  }
};

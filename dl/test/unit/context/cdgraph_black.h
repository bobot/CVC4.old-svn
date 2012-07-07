/*********************                                                        */
/*! \file cdgraph_black.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black-box tests pertaining to the CDGraph<> class
 **
 ** Black-box tests pertaining to the CDGraph<> class.
 **/

#include <cxxtest/TestSuite.h>

#include <string>
#include <iostream>

#include "context/context.h"
#include "context/cdgraph.h"

using namespace std;
using namespace CVC4::context;

class CDGraphBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

public:

  void setUp() {
    d_context = new Context();
  }

  void tearDown() {
    delete d_context;
  }

  void testCDGraphSimple() {
    CDGraph<string, string> g;
    VertexId foo_id = g.addVertex("foo");
    const Vertex& foo = getVertex(foo_id);
    TS_ASSERT_EQUALS("foo", getVertexAnnotation(foo_id));
    TS_ASSERT(foo.noEdges());
    TS_ASSERT(foo.getIncomingEdges().empty());
    TS_ASSERT(foo.getOutgoingEdges().empty());

    d_context->push();
    g.addEdge(foo_id, foo_id);
    TS_ASSERT_EQUALS("foo", getVertexAnnotation(foo_id));
    TS_ASSERT(!foo.noEdges());
    TS_ASSERT(foo.getIncomingEdges().size() == 1);
    TS_ASSERT(foo.getIncomingEdges()[0] == foo_id);
    TS_ASSERT(foo.getOutgoingEdges()[0] == foo_id);
    d_context->pop();

    TS_ASSERT_EQUALS("foo", getVertexAnnotation(foo_id));
    TS_ASSERT(foo.noEdges());
    TS_ASSERT(foo.getIncomingEdges().empty());
    TS_ASSERT(foo.getOutgoingEdges().empty());
  }

};/* class CDGraphBlack */

/*********************                                                        */
/*! \file stacking_map_black.h
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
 ** \brief Black box testing of CVC4::theory::uf::morgan::StackingMap
 **
 ** Black box testing of CVC4::theory::uf::morgan::StackingMap.
 **/

#include <cxxtest/TestSuite.h>

#include "context/context.h"
#include "expr/node.h"
#include "theory/uf/morgan/stacking_map.h"

using namespace CVC4;
using namespace CVC4::theory::uf::morgan;
using namespace CVC4::context;

using namespace std;

/**
 * Test the StackingMap.
 */
class StackingMapBlack : public CxxTest::TestSuite {
  Context* d_ctxt;
  StackingMap<TNode, TNode, TNodeHashFunction>* d_mapPtr;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  Node a, b, c, d, e, f, g;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nm = new NodeManager(d_ctxt, NULL);
    d_scope = new NodeManagerScope(d_nm);
    d_mapPtr = new StackingMap<TNode, TNode, TNodeHashFunction>(d_ctxt);

    a = d_nm->mkVar("a", d_nm->realType());
    b = d_nm->mkVar("b", d_nm->realType());
    c = d_nm->mkVar("c", d_nm->realType());
    d = d_nm->mkVar("d", d_nm->realType());
    e = d_nm->mkVar("e", d_nm->realType());
    f = d_nm->mkVar("f", d_nm->realType());
    g = d_nm->mkVar("g", d_nm->realType());
  }

  void tearDown() {
    g = Node::null();
    f = Node::null();
    e = Node::null();
    d = Node::null();
    c = Node::null();
    b = Node::null();
    a = Node::null();

    delete d_mapPtr;
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testSimpleContextual() {
    StackingMap<TNode, TNode, TNodeHashFunction>& d_map = *d_mapPtr;

    TS_ASSERT(d_map[a].isNull());
    TS_ASSERT(d_map[b].isNull());
    TS_ASSERT(d_map[c].isNull());
    TS_ASSERT(d_map[d].isNull());
    TS_ASSERT(d_map[e].isNull());
    TS_ASSERT(d_map[f].isNull());
    TS_ASSERT(d_map[g].isNull());

    d_map.set(a, b);

    TS_ASSERT(d_map[a] == b);
    TS_ASSERT(d_map[b].isNull());
    TS_ASSERT(d_map[c].isNull());
    TS_ASSERT(d_map[d].isNull());
    TS_ASSERT(d_map[e].isNull());
    TS_ASSERT(d_map[f].isNull());
    TS_ASSERT(d_map[g].isNull());

    d_ctxt->push();
    {
      TS_ASSERT(d_map[a] == b);
      TS_ASSERT(d_map[b].isNull());
      TS_ASSERT(d_map[c].isNull());
      TS_ASSERT(d_map[d].isNull());
      TS_ASSERT(d_map[e].isNull());
      TS_ASSERT(d_map[f].isNull());
      TS_ASSERT(d_map[g].isNull());

      d_map.set(c, d);
      d_map.set(f, e);

      TS_ASSERT(d_map[a] == b);
      TS_ASSERT(d_map[b].isNull());
      TS_ASSERT(d_map[c] == d);
      TS_ASSERT(d_map[d].isNull());
      TS_ASSERT(d_map[e].isNull());
      TS_ASSERT(d_map[f] == e);
      TS_ASSERT(d_map[g].isNull());

      d_ctxt->push();
      {

        TS_ASSERT(d_map[a] == b);
        TS_ASSERT(d_map[b].isNull());
        TS_ASSERT(d_map[c] == d);
        TS_ASSERT(d_map[d].isNull());
        TS_ASSERT(d_map[e].isNull());
        TS_ASSERT(d_map[f] == e);
        TS_ASSERT(d_map[g].isNull());

        d_map.set(a, c);
        d_map.set(f, f);
        d_map.set(e, d);
        d_map.set(c, Node::null());
        d_map.set(g, a);

        TS_ASSERT(d_map[a] == c);
        TS_ASSERT(d_map[b].isNull());
        TS_ASSERT(d_map[c].isNull());
        TS_ASSERT(d_map[d].isNull());
        TS_ASSERT(d_map[e] == d);
        TS_ASSERT(d_map[f] == f);
        TS_ASSERT(d_map[g] == a);

      }
      d_ctxt->pop();

      TS_ASSERT(d_map[a] == b);
      TS_ASSERT(d_map[b].isNull());
      TS_ASSERT(d_map[c] == d);
      TS_ASSERT(d_map[d].isNull());
      TS_ASSERT(d_map[e].isNull());
      TS_ASSERT(d_map[f] == e);
      TS_ASSERT(d_map[g].isNull());
    }
    d_ctxt->pop();

    TS_ASSERT(d_map[a] == b);
    TS_ASSERT(d_map[b].isNull());
    TS_ASSERT(d_map[c].isNull());
    TS_ASSERT(d_map[d].isNull());
    TS_ASSERT(d_map[e].isNull());
    TS_ASSERT(d_map[f].isNull());
    TS_ASSERT(d_map[g].isNull());
  }
};

/*********************                                                        */
/*! \file congruence_closure_white.h
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
 ** \brief White box testing of CVC4::CongruenceClosure.
 **
 ** White box testing of CVC4::CongruenceClosure.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "context/context.h"
#include "context/cdset.h"
#include "context/cdmap.h"
#include "expr/node.h"
#include "expr/kind.h"
#include "expr/node_manager.h"
#include "util/congruence_closure.h"


using namespace CVC4;
using namespace CVC4::context;
using namespace std;


struct MyOutputChannel {
  CDSet<Node, NodeHashFunction> d_notifications;
  CDMap<Node, Node, NodeHashFunction> d_equivalences;
  NodeManager* d_nm;

  MyOutputChannel(Context* ctxt, NodeManager* nm) :
    d_notifications(ctxt),
    d_equivalences(ctxt),
    d_nm(nm) {
  }

  bool saw(TNode a, TNode b) {
    return d_notifications.contains(d_nm->mkNode(kind::EQUAL, a, b)) ||
      d_notifications.contains(d_nm->mkNode(kind::EQUAL, b, a));
  }

  TNode find(TNode n) {
    CDMap<Node, Node, NodeHashFunction>::iterator i = d_equivalences.find(n);
    if(i == d_equivalences.end()) {
      return n;
    } else {
      return (*i).second;
    }
  }

  bool areCongruent(TNode a, TNode b) {
    Debug("cc") << "=== a is  " << a << std::endl
                << "=== a' is " << find(a) << std::endl
                << "=== b is  " << b << std::endl
                << "=== b' is " << find(b) << std::endl;
    return find(a) == find(b);
  }

  void merge(TNode a, TNode b) {
    Debug("cc") << "======OI!  I've been notified of: "
                << a << " == " << b << std::endl;

    Node eq = d_nm->mkNode(kind::EQUAL, a, b);
    Node eqRev = d_nm->mkNode(kind::EQUAL, b, a);

    TS_ASSERT(!d_notifications.contains(eq));
    TS_ASSERT(!d_notifications.contains(eqRev));

    d_notifications.insert(eq);

    d_equivalences.insert(a, b);
  }
};/* class MyOutputChannel */


class CongruenceClosureWhite : public CxxTest::TestSuite {
  Context* d_context;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;
  MyOutputChannel* d_out;
  CongruenceClosure<MyOutputChannel>* d_cc;

  TypeNode U;
  Node a, f, fa, ffa, fffa, ffffa, b, fb, ffb, fffb, ffffb;
  Node g, gab, gba, gfafb, gfbfa, gfaa, gbfb;
  Node h, hab, hba, hfaa;
  Node a_eq_b, fa_eq_b, a_eq_fb, fa_eq_fb, h_eq_g;
public:

  void setUp() {
    d_context = new Context;
    d_nm = new NodeManager(d_context);
    d_scope = new NodeManagerScope(d_nm);
    d_out = new MyOutputChannel(d_context, d_nm);
    d_cc = new CongruenceClosure<MyOutputChannel>(d_context, d_out);

    U = d_nm->mkSort("U");

    f = d_nm->mkVar("f", d_nm->mkFunctionType(U, U));
    a = d_nm->mkVar("a", U);
    fa = d_nm->mkNode(kind::APPLY_UF, f, a);
    ffa = d_nm->mkNode(kind::APPLY_UF, f, fa);
    fffa = d_nm->mkNode(kind::APPLY_UF, f, ffa);
    ffffa = d_nm->mkNode(kind::APPLY_UF, f, fffa);
    b = d_nm->mkVar("b", U);
    fb = d_nm->mkNode(kind::APPLY_UF, f, b);
    ffb = d_nm->mkNode(kind::APPLY_UF, f, fb);
    fffb = d_nm->mkNode(kind::APPLY_UF, f, ffb);
    ffffb = d_nm->mkNode(kind::APPLY_UF, f, fffb);
    vector<TypeNode> args(2, U);
    g = d_nm->mkVar("g", d_nm->mkFunctionType(args, U));
    gab = d_nm->mkNode(kind::APPLY_UF, g, a, b);
    gfafb = d_nm->mkNode(kind::APPLY_UF, g, fa, fb);
    gba = d_nm->mkNode(kind::APPLY_UF, g, b, a);
    gfbfa = d_nm->mkNode(kind::APPLY_UF, g, fb, fa);
    gfaa = d_nm->mkNode(kind::APPLY_UF, g, fa, a);
    gbfb = d_nm->mkNode(kind::APPLY_UF, g, b, fb);
    h = d_nm->mkVar("h", d_nm->mkFunctionType(args, U));
    hab = d_nm->mkNode(kind::APPLY_UF, h, a, b);
    hba = d_nm->mkNode(kind::APPLY_UF, h, b, a);
    hfaa = d_nm->mkNode(kind::APPLY_UF, h, fa, a);

    a_eq_b = d_nm->mkNode(kind::EQUAL, a, b);
    fa_eq_b = d_nm->mkNode(kind::EQUAL, fa, b);
    a_eq_fb = d_nm->mkNode(kind::EQUAL, a, fb);
    fa_eq_fb = d_nm->mkNode(kind::EQUAL, fa, fb);

    h_eq_g = d_nm->mkNode(kind::EQUAL, h, g);
  }

  void tearDown() {
    try {
      f = a = fa = ffa = fffa = ffffa = Node::null();
      b = fb = ffb = fffb = ffffb = Node::null();
      g = gab = gba = gfafb = gfbfa = gfaa = gbfb = Node::null();
      h = hab = hba = hfaa = Node::null();
      a_eq_b = fa_eq_b = a_eq_fb = fa_eq_fb = h_eq_g = Node::null();
      U = TypeNode::null();

      delete d_cc;
      delete d_out;
      delete d_scope;
      delete d_nm;
      delete d_context;
    } catch(Exception& e) {
      Warning() << std::endl << e << std::endl;
      throw;
    }
  }

  void testSimple() {
    // add terms, then add equalities

    d_cc->addTerm(fa);
    d_cc->addTerm(fb);

    d_cc->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(fa, fb));
    TS_ASSERT(d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_cc->areCongruent(a, b));
  }

  void testSimpleReverse() {
    // add equalities, then add terms; should get the same as
    // testSimple()

    d_cc->addEquality(a_eq_b);

    d_cc->addTerm(fa);
    d_cc->addTerm(fb);

    TS_ASSERT(d_out->areCongruent(fa, fb));
    TS_ASSERT(d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_cc->areCongruent(a, b));
  }

  void testSimpleContextual() {
    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(!d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(!d_cc->areCongruent(a, b));

    {
      d_context->push();

      d_cc->addTerm(fa);
      d_cc->addTerm(fb);

      TS_ASSERT(!d_out->areCongruent(fa, fb));
      TS_ASSERT(!d_cc->areCongruent(fa, fb));

      TS_ASSERT(!d_out->areCongruent(a, b));
      TS_ASSERT(!d_cc->areCongruent(a, b));

      {
        d_context->push();

        d_cc->addEquality(a_eq_b);

        TS_ASSERT(d_out->areCongruent(fa, fb));
        TS_ASSERT(d_cc->areCongruent(fa, fb));

        TS_ASSERT(!d_out->areCongruent(a, b));
        TS_ASSERT(d_cc->areCongruent(a, b));

        d_context->pop();
      }

      TS_ASSERT(!d_out->areCongruent(fa, fb));
      TS_ASSERT(!d_cc->areCongruent(fa, fb));

      TS_ASSERT(!d_out->areCongruent(a, b));
      TS_ASSERT(!d_cc->areCongruent(a, b));

      d_context->pop();
    }

    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(!d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(!d_cc->areCongruent(a, b));
  }

  void testSimpleContextualReverse() {
    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(!d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(!d_cc->areCongruent(a, b));

    {
      d_context->push();

      d_cc->addEquality(a_eq_b);

      TS_ASSERT(!d_out->areCongruent(fa, fb));
      TS_ASSERT(d_cc->areCongruent(fa, fb));

      TS_ASSERT(!d_out->areCongruent(a, b));
      TS_ASSERT(d_cc->areCongruent(a, b));

      {
        d_context->push();

        d_cc->addTerm(fa);
        d_cc->addTerm(fb);

        TS_ASSERT(d_out->areCongruent(fa, fb));
        TS_ASSERT(d_cc->areCongruent(fa, fb));

        TS_ASSERT(!d_out->areCongruent(a, b));
        TS_ASSERT(d_cc->areCongruent(a, b));

        d_context->pop();
      }

      TS_ASSERT(!d_out->areCongruent(fa, fb));
      TS_ASSERT(d_cc->areCongruent(fa, fb));

      TS_ASSERT(!d_out->areCongruent(a, b));
      TS_ASSERT(d_cc->areCongruent(a, b));

      d_context->pop();
    }

    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(!d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(!d_cc->areCongruent(a, b));
  }

  void test_f_of_f_of_something() {
    d_cc->addTerm(ffa);
    d_cc->addTerm(ffb);

    d_cc->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(ffa, ffb));
    TS_ASSERT(d_cc->areCongruent(ffa, ffb));

    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_cc->areCongruent(a, b));
  }

  void test_f4_of_something() {
    d_cc->addTerm(ffffa);
    d_cc->addTerm(ffffb);

    d_cc->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(ffffa, ffffb));
    TS_ASSERT(d_cc->areCongruent(ffffa, ffffb));

    TS_ASSERT(!d_out->areCongruent(fffa, fffb));
    TS_ASSERT(d_cc->areCongruent(fffa, fffb));

    TS_ASSERT(!d_out->areCongruent(ffa, ffb));
    TS_ASSERT(d_cc->areCongruent(ffa, ffb));

    TS_ASSERT(!d_out->areCongruent(fa, fb));
    TS_ASSERT(d_cc->areCongruent(fa, fb));

    TS_ASSERT(!d_out->areCongruent(a, b));
    TS_ASSERT(d_cc->areCongruent(a, b));
  }

  void testSimpleBinaryFunction() {
    d_cc->addTerm(gab);
    d_cc->addTerm(gba);

    d_cc->addEquality(a_eq_b);

    TS_ASSERT(d_out->areCongruent(gab, gba));
    TS_ASSERT(d_cc->areCongruent(gab, gba));
  }

  void testSimpleBinaryFunction2() {
    Debug.on("cc");

    try {

    d_cc->addTerm(gfafb);
    d_cc->addTerm(gba);
    d_cc->addTerm(hfaa);

    d_cc->addEquality(a_eq_fb);
    d_cc->addEquality(fa_eq_b);
    d_cc->addEquality(h_eq_g);

    TS_ASSERT(d_cc->areCongruent(a, fb));
    TS_ASSERT(d_cc->areCongruent(b, fa));
    TS_ASSERT(d_cc->areCongruent(fb, ffa));

    Debug("cc") << "\n\n\n"
                << "a norm:     " << d_cc->normalize(a) << std::endl
                << "fb norm:    " << d_cc->normalize(fb) << std::endl
                << "b norm:     " << d_cc->normalize(b) << std::endl
                << "fa norm:    " << d_cc->normalize(fa) << std::endl
                << "ffa norm:   " << d_cc->normalize(ffa) << std::endl
                << "ffffa norm  " << d_cc->normalize(ffffa) << std::endl
                << "ffffb norm  " << d_cc->normalize(ffffb) << std::endl
                << "gba norm:   " << d_cc->normalize(gba) << std::endl
                << "gfaa norm:  " << d_cc->normalize(gfaa) << std::endl
                << "gbfb norm:  " << d_cc->normalize(gbfb) << std::endl
                << "gfafb norm: " << d_cc->normalize(gfafb) << std::endl
                << "hab norm:   " << d_cc->normalize(hab) << std::endl
                << "hba norm:   " << d_cc->normalize(hba) << std::endl
                << "hfaa norm:  " << d_cc->normalize(hfaa) << std::endl;

    TS_ASSERT(d_out->areCongruent(gfafb, gba));
    TS_ASSERT(d_cc->areCongruent(b, fa));
    TS_ASSERT(d_cc->areCongruent(gfafb, hba));
    TS_ASSERT(d_cc->areCongruent(gfafb, gba));
    TS_ASSERT(d_cc->areCongruent(hba, gba));
    TS_ASSERT(d_cc->areCongruent(hfaa, hba));
    TS_ASSERT(d_cc->areCongruent(hfaa, gba));

    } catch(Exception& e) {
      Debug("cc") << "\n\n" << e << "\n\n";
      throw;
    }
  }

};/* class CongruenceClosureWhite */

/*
 * theory_arrays_white.h
 *
 *  Created on: Jan 27, 2011
 *      Author: lianah
 */

#include <cxxtest/TestSuite.h>

#include "theory/theory.h"
#include "theory/arrays/theory_arrays.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "context/context.h"


#include "theory/theory_test_utils.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arrays;
using namespace CVC4::expr;
using namespace CVC4::context;
using namespace CVC4::kind;

using namespace std;

class TheoryArraysWhite : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  TestOutputChannel d_outputChannel;
  Theory::Effort d_level;

  TheoryArrays* d_arrays;

public:

  TheoryArraysWhite() : d_level(Theory::FULL_EFFORT) {}

  void setUp() {
    d_ctxt = new Context;
    d_nm = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nm);
    d_outputChannel.clear();
    d_arrays = new TheoryArrays(0, d_ctxt, d_outputChannel);

  }

  void tearDown() {
    delete d_arrays;
    d_outputChannel.clear();
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testRoW(){
   TS_ASSERT(true);
  }

};

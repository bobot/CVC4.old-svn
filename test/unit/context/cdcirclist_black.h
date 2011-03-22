/*********************                                                        */
/*! \file cdcirclist_black.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::CDCircList<>.
 **
 ** Black box testing of CVC4::context::CDCircList<>.
 **/

#include <cxxtest/TestSuite.h>

#include <vector>
#include <iostream>

#include <limits.h>

#include "memory.h"

#include "context/context.h"
#include "context/cdcirclist.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::test;

class CDCircListBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

public:

  void setUp() {
    d_context = new Context();
  }

  void tearDown() {
    delete d_context;
  }

  void testSimple() {
    CDCircList<int> l(d_context);
    l.append(1);
    l.append(2);
    l.append(3);
  }

};

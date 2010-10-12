/*********************                                                        */
/*! \file cdlist_context_memory_black.h
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
 ** \brief Black box testing of CVC4::context::CDList<>.
 **
 ** Black box testing of CVC4::context::CDList<>.
 **/

#include <cxxtest/TestSuite.h>

#include <vector>
#include <iostream>

#include <limits.h>

#include "memory.h"

#include "context/context.h"
#include "context/cdlist_context_memory.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::test;

struct DtorSensitiveObject {
  bool& d_dtorCalled;
  DtorSensitiveObject(bool& dtorCalled) : d_dtorCalled(dtorCalled) {}
  ~DtorSensitiveObject() { d_dtorCalled = true; }
};

class CDListContextMemoryBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

public:

  void setUp() {
    d_context = new Context();
  }

  void tearDown() {
    delete d_context;
  }

  // test at different sizes.  this triggers grow() behavior differently.
  // grow() was completely broken in revision 256
  void testCDList10() { listTest(10); }
  void testCDList15() { listTest(15); }
  void testCDList20() { listTest(20); }
  void testCDList35() { listTest(35); }
  void testCDList50() { listTest(50); }
  void testCDList99() { listTest(99); }

  void listTest(int N) {
    listTest(N, true);
    listTest(N, false);
  }

  void listTest(int N, bool callDestructor) {
    CDList<int, ContextMemoryAllocator<int> >
      list(d_context, callDestructor, ContextMemoryAllocator<int>(d_context->getCMM()));

    TS_ASSERT(list.empty());
    for(int i = 0; i < N; ++i) {
      TS_ASSERT_EQUALS(list.size(), unsigned(i));
      list.push_back(i);
      TS_ASSERT(!list.empty());
      TS_ASSERT_EQUALS(list.back(), i);
      int i2 = 0;
      for(CDList<int, ContextMemoryAllocator<int> >::const_iterator j = list.begin();
          j != list.end();
          ++j) {
        TS_ASSERT_EQUALS(*j, i2++);
      }
    }
    TS_ASSERT_EQUALS(list.size(), unsigned(N));

    for(int i = 0; i < N; ++i) {
      TS_ASSERT_EQUALS(list[i], i);
    }
  }

  void testDtorCalled() {
    bool shouldRemainFalse = false;
    bool shouldFlipToTrue = false;
    bool alsoFlipToTrue = false;
    bool shouldAlsoRemainFalse = false;
    bool aThirdFalse = false;

    CDList<DtorSensitiveObject, ContextMemoryAllocator<DtorSensitiveObject> > listT(d_context, true, ContextMemoryAllocator<DtorSensitiveObject>(d_context->getCMM()));
    CDList<DtorSensitiveObject, ContextMemoryAllocator<DtorSensitiveObject> > listF(d_context, false, ContextMemoryAllocator<DtorSensitiveObject>(d_context->getCMM()));

    DtorSensitiveObject shouldRemainFalseDSO(shouldRemainFalse);
    DtorSensitiveObject shouldFlipToTrueDSO(shouldFlipToTrue);
    DtorSensitiveObject alsoFlipToTrueDSO(alsoFlipToTrue);
    DtorSensitiveObject shouldAlsoRemainFalseDSO(shouldAlsoRemainFalse);
    DtorSensitiveObject aThirdFalseDSO(aThirdFalse);

    listT.push_back(shouldAlsoRemainFalseDSO);
    listF.push_back(shouldAlsoRemainFalseDSO);

    d_context->push();

    listT.push_back(shouldFlipToTrueDSO);
    listT.push_back(alsoFlipToTrueDSO);

    listF.push_back(shouldRemainFalseDSO);
    listF.push_back(shouldAlsoRemainFalseDSO);
    listF.push_back(aThirdFalseDSO);

    TS_ASSERT_EQUALS(shouldRemainFalse, false);
    TS_ASSERT_EQUALS(shouldFlipToTrue, false);
    TS_ASSERT_EQUALS(alsoFlipToTrue, false);
    TS_ASSERT_EQUALS(shouldAlsoRemainFalse, false);
    TS_ASSERT_EQUALS(aThirdFalse, false);

    d_context->pop();

    TS_ASSERT_EQUALS(shouldRemainFalse, false);
    TS_ASSERT_EQUALS(shouldFlipToTrue, true);
    TS_ASSERT_EQUALS(alsoFlipToTrue, true);
    TS_ASSERT_EQUALS(shouldAlsoRemainFalse, false);
    TS_ASSERT_EQUALS(aThirdFalse, false);
  }

  /* setrlimit() totally broken on Mac OS X */
  void testOutOfMemory() {
#ifdef __APPLE__

    TS_WARN("can't run memory tests on Mac OS X");

#else /* __APPLE__ */

    CDList<unsigned, ContextMemoryAllocator<unsigned> > list(d_context);
    WithLimitedMemory wlm(1);

    TS_ASSERT_THROWS({
        // We cap it at UINT_MAX, preferring to terminate with a
        // failure than run indefinitely.
        for(unsigned i = 0; i < UINT_MAX; ++i) {
          list.push_back(i);
        }
      }, bad_alloc);

#endif /* __APPLE__ */
  }
};

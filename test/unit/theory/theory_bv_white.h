/*********************                                                        */
/*! \file theory_bv_white.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include <cxxtest/TestSuite.h>

#include "theory/theory.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/bv_solver_types.h"
#include "theory/bv/bv_sat.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "context/context.h"

#include "theory/theory_test_utils.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils; 
using namespace CVC4::expr;
using namespace CVC4::context;

using namespace std;

class TheoryBVWhite : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  bool debug;

public:

  TheoryBVWhite() : debug(false) {}


  void setUp() {
    d_ctxt = new Context();
    d_nm = new NodeManager(d_ctxt, NULL);
    d_scope = new NodeManagerScope(d_nm);

  }

  void tearDown() {
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testClauseManager() {

    MinisatClauseManager* mgr = new MinisatClauseManager(d_ctxt);

    /// testing clause creation 
    
    SatVar var1 = mgr->newVar(); 
    SatLit v1 = mgr->mkLit(var1);
    SatVar var2 = mgr->newVar(); 
    SatLit v2 = mgr->mkLit(var2); 
    SatVar var3 = mgr->newVar(); 
    SatLit v3 = mgr->mkLit(var3);
    SatVar var4 = mgr->newVar(); 
    SatLit v4 = mgr->mkLit(var4); 
    SatVar var5 = mgr->newVar(); 
    SatLit v5 = mgr->mkLit(var5);
    SatVar var6 = mgr->newVar(); 
    SatLit v6 = mgr->mkLit(var6);


    SatLit marker1 = mgr->mkLit(mgr->newVar());
    SatLit marker2 = mgr->mkLit(mgr->newVar());
    SatLit marker3 = mgr->mkLit(mgr->newVar());
    SatLit marker4 = mgr->mkLit(mgr->newVar());    
    SatLit marker1 = mgr->mkLit(mgr->newVar());
    SatLit marker1 = mgr->mkLit(mgr->newVar());
    
    
    ClauseId id1 = mgr->mkClause(v1, ~v2, v3);

    SatClause* cl = new SatClause();
    cl->addLiteral(v3);
    cl->addLiteral(v1);
    cl->addLiteral(~v2);
    cl->sort(); 

    TS_ASSERT (id1 != 0); 
    TS_ASSERT (mgr->inPool(cl)); 
    TS_ASSERT (mgr->getId(cl) == id1);
    TS_ASSERT (*(mgr->getClause(id1)) == *cl);

    ClauseId id12 = mgr->mkClause(~v2, v1, v3);

    TS_ASSERT(id1 == id12); 
    TS_ASSERT (mgr->d_idClauseMap.size() == 1);

    TS_ASSERT (mgr->d_clauseIdMap.size() == 1);

    ClauseId id2 = mgr->mkClause(v1, ~v3);
    TS_ASSERT (mgr->d_idClauseMap.size() == 2);
    TS_ASSERT (mgr->d_clauseIdMap.size() == 2);

    TS_ASSERT (id1 != id2);
    
    /// creating a problem

    ClauseId id3 = mgr->mkClause(v2, ~v6);
    ClauseId id4 = mgr->mkClause(v6, ~v1);
    ClauseId id5 = mgr->mkClause(v6, v5, v2);
    ClauseId id6 = mgr->mkClause(v3, ~v4, v1); 
                               
    /// testing an unsat instance
    
    mgr->assertClause(id1);
    mgr->assertClause(id2);
    mgr->assertClause(id3);
    mgr->assertClause(id4);
    mgr->assertClause(id5); 
    mgr->assertClause(id6);
    
    bool res = mgr->solve();
    TS_ASSERT(res == false);

    /// Unsat core

    // ClauseIds unsatcore;
    // mgr->getUnsatCore(unsatcore);
    // TODO check that it's what it should be
    
    /// playing with the solve
    
    mgr->assertClause(id1);
    mgr->assertClause(id2);
    d_ctxt->push();
    
    mgr->assertClause(id3);
    mgr->assertClause(id4);
    d_ctxt->push(); 
    mgr->assertClause(id5); 
    mgr->assertClause(id6);
    
    res = mgr->solve();
    TS_ASSERT(res == false);

    d_ctxt->pop();
    res = mgr->solve();
    TS_ASSERT(res == false); 

    /// testing a sat instance

    d_ctxt->pop();
    res =  mgr->solve();
    TS_ASSERT(res == true);
    
  
  }



};

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

  void testSimpleClauseManager() {
    ClauseManager* mgr = new ClauseManager();
    
    SatLit v1 = mkLit(mgr->newVar());
    SatLit v2 = mkLit(mgr->newVar()); 
    SatLit v3 = mkLit(mgr->newVar());
    SatLit v4 = mkLit(mgr->newVar()); 
    SatLit v5 = mkLit(mgr->newVar());
    SatLit v6 = mkLit(mgr->newVar());

    mgr->mkClause(v1, neg(v2), v3);
    mgr->mkClause(v1, neg(v3) );
    mgr->mkClause(v2, neg(v6) );
    mgr->mkClause(v1, v6);
    mgr->mkClause(neg(v1) , v5);
    mgr->mkClause(neg(v1) , neg(v5) );
    mgr->mkClause(v6, v5, v2);
    mgr->mkClause(v3, neg(v4) , v1);
    
    SatClause* cl = new SatClause();
    cl->addLiteral(v3);
    cl->addLiteral(v1);
    cl->addLiteral(neg(v2));
    cl->sort(); 
    TS_ASSERT(mgr->inPool(cl)); 
    
    bool res = mgr->solve();
    TS_ASSERT(res == false); 
    
  }
  
  void testClauseManager() {

    ClauseManager* mgr = new ClauseManager();
    CDList<SatLit> assertions = CDList<SatLit>(d_ctxt);
    
    /// testing clause creation 
    
    SatLit v1 = mkLit(mgr->newVar());
    SatLit v2 = mkLit(mgr->newVar()); 
    SatLit v3 = mkLit(mgr->newVar());
    SatLit v4 = mkLit(mgr->newVar()); 
    SatLit v5 = mkLit(mgr->newVar());
    SatLit v6 = mkLit(mgr->newVar());


    SatVar varmarker1 = mgr->mkMarkerVar();
    SatVar varmarker2 = mgr->mkMarkerVar();
    SatVar varmarker3 = mgr->mkMarkerVar();
    SatVar varmarker4 = mgr->mkMarkerVar();
    SatVar varmarker5 = mgr->mkMarkerVar();    

    SatLit marker1 = mkLit(varmarker1);
    SatLit marker2 = mkLit(varmarker2);
    SatLit marker3 = mkLit(varmarker3);
    SatLit marker4 = mkLit(varmarker4);
    SatLit marker5 = mkLit(varmarker5); 
   
    /// creating a problem
    /// the clauses will be added to the sat solver
    mgr->mkClause(neg(marker1), v1, neg(v2), v3);
    mgr->mkClause(v1, neg(v3) );
    mgr->mkClause(neg(marker2), v6, v4, v2);
    mgr->mkClause(neg(marker3), v2, neg(v6) );
    mgr->mkClause(neg(marker3), v6, v1);
    mgr->mkClause(v3, neg(v4), v1); 
    mgr->mkClause(neg(marker4), neg(v1), v5);
    mgr->mkClause(neg(marker4), neg(v1), neg(v5));
    mgr->mkClause(neg(marker5), neg(v1)); 

    SatClause* cl = new SatClause();
    cl->addLiteral(neg(v4));
    cl->addLiteral(v3);
    cl->addLiteral(v1);
    cl->sort(); 
    
    TS_ASSERT(mgr->inPool(cl)); 
    /// testing an sat instance
    /// should only have the clause without marker literals asserted
    bool res = mgr->solve();
    TS_ASSERT (res == true); 

    d_ctxt->push();
    
    assertions.push_back(marker1);
    assertions.push_back(marker3);
    res = mgr->solve(assertions);
    TS_ASSERT(res == true);
    
    d_ctxt->push(); 

    assertions.push_back(marker4);
    res = mgr->solve(assertions);
    TS_ASSERT(res == false); 

    d_ctxt->pop(); 

    assertions.push_back(marker2);
    res = mgr->solve(assertions);
    TS_ASSERT(res == true);

    d_ctxt->push(); 
    
    assertions.push_back(marker4);
    res = mgr->solve(assertions);
    TS_ASSERT(res == false);

    /// Unsat core
    SatClause* core = mgr->getConflict();
    TS_ASSERT (core != 0);
    
    SatClause temp;
    temp.addLiteral(neg(marker1));
    temp.addLiteral(neg(marker3));
    temp.addLiteral(neg(marker4)); 
    temp.sort(); 
    
    TS_ASSERT (*core == temp);

    d_ctxt->pop();
    assertions.push_back(marker5);

    TS_ASSERT(mgr->solve(assertions) == false);
    core = mgr->getConflict();

    SatClause temp2;
    temp2.addLiteral(neg(marker3));
    temp2.addLiteral(neg(marker1));
    temp2.addLiteral(neg(marker5));
    temp2.sort(); 
    TS_ASSERT(*core == temp2);  
    
  }
  
  void testBitblasterCore() {
    // ClauseManager tests 
    Context* ctx = new Context();
    Bitblaster< DefaultPlusBB, DefaultMultBB, DefaultAndBB, DefaultOrBB, DefaultXorBB>* bb =
      new Bitblaster< DefaultPlusBB, DefaultMultBB, DefaultAndBB, DefaultOrBB, DefaultXorBB >(ctx);
    
    NodeManager* nm = NodeManager::currentNM();
    Node a = nm->mkVar("a", nm->mkBitVectorType(4));
    Node b = nm->mkVar("b", nm->mkBitVectorType(4));
    Node a1 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(2,1)), a);
    Node b1 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(2,1)), b);
    
    Node abeq = nm->mkNode(kind::EQUAL, a, b);
    Node neq = nm->mkNode(kind::NOT, abeq);
    Node a1b1eq = nm->mkNode(kind::EQUAL, a1, b1);
    
    bb->bbAtom(neq);
    bb->bbAtom(a1b1eq); 

    /// constructing the rest of the problem 
    Node a2 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(0,0)), a);
    Node b2 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(0,0)), b);
    Node eq2 = nm->mkNode(kind::EQUAL, a2, b2); 
    
    Node a3 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(3,3)), a);
    Node b3 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(3,3)), b);
    Node eq3 = nm->mkNode(kind::EQUAL, a3, b3);

    bb->bitblast(eq2);
    bb->bitblast(eq3); 

    ctx->push();
    bb->assertToSat(neq);
    bb->assertToSat(a1b1eq);
    bool res = bb->solve();
    TS_ASSERT (res == true);

    ctx->push();
    bb->assertToSat(eq2);
    bb->assertToSat(eq3); 

    res = bb->solve();
    TS_ASSERT(res == false); 
    
    //unsat core test
    
    
  }

    void testBitblasterAndXor() {
    // ClauseManager tests 
    Context* ctx = new Context();
    Bitblaster< DefaultPlusBB, DefaultMultBB, DefaultAndBB, DefaultOrBB, DefaultXorBB>* bb =
      new Bitblaster< DefaultPlusBB, DefaultMultBB, DefaultAndBB, DefaultOrBB, DefaultXorBB >(ctx);
    
    NodeManager* nm = NodeManager::currentNM();
    Node a = nm->mkVar("a", nm->mkBitVectorType(10));
    Node b = nm->mkVar("b", nm->mkBitVectorType(10));
    // Node c = nm->mkVar("c", nm->mkBitVectorType(1)); 
    // Node aEqb = nm->mkNode(kind::EQUAL, a, b);
    Node a_const = utils::mkConst(10,9);
    Node b_const = utils::mkConst(10,5);
    Node xor_const = utils::mkConst(10, 12); 
    Node ab = nm->mkNode(kind::BITVECTOR_XOR, a_const, b_const);
        
    Node atom = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, ab, xor_const));
    // BitVector val((unsigned)4, (unsigned int)3); 
    // Node x1 = utils::mkConst(4, 3);
    // Node x2 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(2, 1)), x1);
    // Node x3 = utils::mkConst(2, 1);
    // Node eq1 = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, x2, x3)); 
    //    Node d = nm->mkNode(nm->mkConst
    
    ctx->push();
    bb->bitblast(atom);
    // bb->bitblast(aEqb);
    // bb->bitblast(eq1); 
    
    // bb->assertToSat(atom);
    // bb->assertToSat(aEqb);
    bb->assertToSat(atom); 
    bool res = bb->solve();
    TS_ASSERT(res == false);
    
    }

};

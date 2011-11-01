/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
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

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/valuation.h"

#include "theory/bv/bv_sat.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::context;

using namespace std;

TheoryBV::TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation)
  : Theory(THEORY_BV, c, u, out, valuation), 
    d_context(c),
    d_assertions(c)
  {
    d_true = utils::mkTrue();
    d_solver = new BVMinisat::SimpSolver();
  }


void TheoryBV::preRegisterTerm(TNode node) {

  BVDebug("bitvector") << "TheoryBV::preRegister(" << node << ")" << std::endl;

}

void TheoryBV::check(Effort e) {
  BVDebug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;
  while (!done()) {
    TNode assertion = get();
    d_assertions.push_back(assertion); 
  }
  d_solver->solve(); 
  if (fullEffort(e)) {
    CDList<TNode>::const_iterator it = d_assertions.begin();
    for (; it != d_assertions.end(); ++it) {
      // TODO:
      //bitBlast(*it);
    }
    // TODO:
    //d_satSolver.solve(); 
  }
}


Node TheoryBV::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    Unhandled(kind::VARIABLE);

  default:
    Unhandled(n.getKind());
  }
}

Node TheoryBV::explain(TNode node) {
  BVDebug("bitvector") << "TheoryBV::explain(" << node << ")" << std::endl;

  TNode equality = node.getKind() == kind::NOT ? node[0] : node;
  Assert(equality.getKind() == kind::EQUAL);
  Assert(0); 
  return node; 

}

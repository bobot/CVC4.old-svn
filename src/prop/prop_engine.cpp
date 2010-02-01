/*********************                                           -*- C++ -*-  */
/** prop_engine.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "prop/prop_engine.h"
#include "prop/cnf_stream.h"

#include "theory/theory_engine.h"
#include "util/decision_engine.h"
#include "prop/minisat/mtl/Vec.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "util/Assert.h"
#include "util/output.h"

#include <utility>
#include <map>

using namespace CVC4::prop::minisat;
using namespace std;

namespace CVC4 {

PropEngine::PropEngine(DecisionEngine& de, TheoryEngine& te, NodeManager * nm) :
  d_de(de), 
  d_te(te)
  //Temporarily removing d_cnfConverter
  /*, 
	     d_cnfConverter(nm)*/ {
  d_cnfStream = new CVC4::prop::CnfStream(this);
}

PropEngine::~PropEngine(){
  delete d_cnfStream;
}


void PropEngine::assertClause(vec<Lit> & c){
  /*we can also here add a context dependent queue of assertions
   *for restarting the sat solver
   */
  d_sat.addClause(c);
}

void PropEngine::registerMapping(const Node & n, Lit l){
  d_node2lit.insert(make_pair(n,l));
  d_lit2node.insert(make_pair(l,n));
}

Lit PropEngine::requestFreshLit(){
  Var v = d_sat.newVar();
  Lit l(v,false);
  return l;
}

void PropEngine::solve(Node e) {
  
  d_cnfStream->convertAndAssert(e);

  d_sat.verbosity = 1;
  bool result = d_sat.solve();

  Notice() << "result is " << (result ? "sat/invalid" : "unsat/valid") << endl;
  /*
  if(result) {
    Notice() << "model:" << endl;
    for(int i = 0; i < d_sat.model.size(); ++i){
      Notice() << " " << toInt(d_sat.model[i]);
    }
    Notice() << endl;
    for(int i = 0; i < d_sat.model.size(); ++i){
      Notice() << " " << d_sat.model[i] << " is "
               << (d_sat.model[i] == l_False ? "FALSE" :
                   (d_sat.model[i] == l_Undef ? "UNDEF" :
                    "TRUE")) << endl;
    }
  } else {
    Notice() << "conflict:" << endl;
    for(int i = 0; i < d_sat.conflict.size(); ++i){
      Notice() << " " << (sign(d_sat.conflict[i]) ? "-" : "") << var(sat.conflict[i]);
    }
    Notice() << " [[";
    for(int i = 0; i < d_sat.conflict.size(); ++i){
      Notice() << " " << (sign(d_sat.conflict[i]) ? "-" : "") << varsReverse[var(sat.conflict[i])];
    }
    Notice() << " ]] " << endl;
  }
  */
}

}/* CVC4 namespace */

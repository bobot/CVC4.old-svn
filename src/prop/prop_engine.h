/*********************                                           -*- C++ -*-  */
/** prop_engine.h
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
 ** The PropEngine (proposiitonal engine); main interface point
 ** between CVC4's SMT infrastructure and the SAT solver.
 **/

#ifndef __CVC4__PROP_ENGINE_H
#define __CVC4__PROP_ENGINE_H

#include "cvc4_config.h"
#include "expr/node.h"
#include "util/decision_engine.h"
#include "theory/theory_engine.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"

#include <map>
#include "prop/cnf_stream.h"

namespace CVC4 {
  namespace prop {
    class CnfStream;
  }
}

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// Prover and above (and requires the services of) a specific
// propositional solver, DPLL or otherwise.

class PropEngine {
  DecisionEngine &d_de;
  TheoryEngine &d_te;
  
  /* Morgan: I added these back.
   * Why did you push these into solve()?
   * I am guessing this is for either a technical reason I'm not seeing,
   * or that you wanted to have a clean restart everytime solve() was called
   * and to start from scratch everytime. (Avoid push/pop problems?)
   * Is this right?
   */
  CVC4::prop::minisat::SimpSolver d_sat;
  std::map<Node, CVC4::prop::minisat::Lit> d_node2lit;
  std::map<CVC4::prop::minisat::Lit, Node> d_lit2node;

  /** 
   * Adds mapping of n -> l to d_node2lit, and
   * a mapping of l -> n to d_lit2node.
   */
  void registerMapping(const Node & n, CVC4::prop::minisat::Lit l);

  friend class CVC4::prop::CnfStream;

  CVC4::prop::minisat::Lit requestFreshLit();

  bool isNodeMapped(const Node & n) const;
  CVC4::prop::minisat::Lit lookupLit(const Node & n) const;
  

  /**
   * Asserts an internally constructed clause. 
   * Each literal is assumed to be in the 1:1 mapping contained in d_node2lit & d_lit2node.
   * @param c the clause to be asserted.
   */
  void assertClause(CVC4::prop::minisat::vec<CVC4::prop::minisat::Lit> & c);

  
  /** The CNF converter in use */
  //CVC4::prop::CnfConverter d_cnfConverter;
  CVC4::prop::CnfStream *d_cnfStream;
public:
  /**
   * Create a PropEngine with a particular decision and theory engine.
   */
  CVC4_PUBLIC PropEngine(CVC4::DecisionEngine&, CVC4::TheoryEngine&, CVC4::NodeManager*);
  CVC4_PUBLIC ~PropEngine();

  /**
   * Currently this takes a well-formed* Node,
   * converts it to a propositionally equisatisifiable formula for a sat solver,
   * and invokes the sat solver for a satisfying assignment.
   * TODO: what does well-formed mean here?
   */
  void solve(Node);

};/* class PropEngine */


inline bool PropEngine::isNodeMapped(const Node & n) const{
  return d_node2lit.find(n) != d_node2lit.end();
}

inline CVC4::prop::minisat::Lit PropEngine::lookupLit(const Node & n) const{
  Assert(isNodeMapped(n));
  return d_node2lit.find(n)->second;
}



}/* CVC4 namespace */

#endif /* __CVC4__PROP_ENGINE_H */

/*********************                                           -*- C++ -*-  */
/** cnf_stream.h
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** This class takes a sequence of formulas.
 ** It outputs a stream of clauses that is propositional
 ** equisatisfiable with the conjunction of the formulas.
 ** This stream is maintained in an online fashion.
 **
 ** Unlike other parts of the system it is aware of the PropEngine's
 ** internals such as the representation and translation of 
 **/


#ifndef __CVC4__CNF_STREAM_H
#define __CVC4__CNF_STREAM_H

//TODO: Why am i including this? Who knows...
#include "cvc4_config.h"

#include "expr/node.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/prop_engine.h"

namespace CVC4 {
  class PropEngine;
}


namespace CVC4 {
namespace prop {

class CnfStream {
  PropEngine *d_pl;

  //Uniform interface for sending a clause back to
  //the prop engine.
  //May want to have internal datastructures later on
  void insertClauseIntoStream(minisat::vec<minisat::Lit> & c);
  void insertClauseIntoStream(minisat::Lit a);
  void insertClauseIntoStream(minisat::Lit a,minisat::Lit b);
  void insertClauseIntoStream(minisat::Lit a,minisat::Lit b, minisat::Lit c);
  

  //negotiates the mapping of literals with PropEngine
  minisat::Lit registerLit(const Node & n, minisat::Lit intermsOf, bool negate = false);
  //Requests a fresh literal from the prop engine
  //and registers the node to map to that literal
  minisat::Lit setupLit(const Node & n);

  /* handler for each Kind.
   * each is responsibile for returning a literal that is equivalent to 
   * the node in the equisatisfiable cnf being sent back.
   * A handle can assume that the Node has not yet been mapped.
   */
  minisat::Lit handleAtom(const Node & n);
  minisat::Lit handleNot(const Node & n);
  minisat::Lit handleXor(const Node & n);
  
  minisat::Lit handleImplies(const Node & n);
  minisat::Lit handleIff(const Node & n);
  
  
  minisat::Lit handleIte(const Node & n);

  minisat::Lit handleAnd(const Node& n);
  minisat::Lit handleOr(const Node& n);

  //helper for n-ary handles (OR, AND)
  //Non n-ary Kinds should avoid this extra overhead and directly
  //access their children.
  //Iterates over a node's children and push the result to the back of target
  void childLiterals(const Node& n, minisat::vec<minisat::Lit> & target);

  //Recurisively dispatches the various Kinds to the appropriate handler.
  minisat::Lit naiveRecConvertToCnf(const Node & n);

public:
  CnfStream(CVC4::PropEngine *);
  void convertAndAssert(const Node & n);
}; /* class PropEngine */


}/* prop namespace */
}/* CVC4 namespace */



#endif /* __CVC4__CNF_STREAM_H */

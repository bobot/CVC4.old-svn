/*********************                                                        */
/*! \file inst_strategy_model_find.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief inst strategy model find
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_STRATEGY_MODEL_FIND_H
#define __CVC4__INST_STRATEGY_MODEL_FIND_H

#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/quantifiers_engine.h"
#include "theory/uf/fmf_model.h"

namespace CVC4 {
namespace theory {
namespace uf {

/** this class iterates over a RepAlphabet */
class RepAlphabetIterator {
public:
  RepAlphabetIterator( QuantifiersEngine* qe, Node f, FmfModel* model );
  ~RepAlphabetIterator(){}
  Node d_f;
  FmfModel* d_model;
  std::vector< int > d_index;
  void increment( QuantifiersEngine* qe );
  bool isFinished();
  void getMatch( QuantifiersEngine* qe, InstMatch& m );
  Node getTerm( int i );
  int getNumTerms() { return d_f[0].getNumChildren(); }
};

//instantiation strategies
class InstStrategyFiniteModelFind : public InstStrategy{
private:
  /** finite model */
  FmfModel* d_fmf_model;
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_ith;
  /** strong solver class */
  StrongSolverTheoryUf* d_ss;
  ///** map of current used instantiations */
  std::vector< RepAlphabet > d_inst_group;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e, int limitInst );
public:
  InstStrategyFiniteModelFind( context::Context* c, InstantiatorTheoryUf* ith, StrongSolverTheoryUf* ss, QuantifiersEngine* qe );
  ~InstStrategyFiniteModelFind(){}
  /** identify */
  std::string identify() const { return std::string("FinteModelFind"); }
};

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

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

namespace CVC4 {
namespace theory {
namespace uf {

class RepAlphabetIterator;

/** representative alphabet */
class RepAlphabet {
public:
  RepAlphabet(){}
  RepAlphabet( RepAlphabet& ra, QuantifiersEngine* ie );
  ~RepAlphabet(){}
  std::map< TypeNode, std::vector< Node > > d_type_reps;
  std::map< Node, int > d_tmap;
  void set( TypeNode t, std::vector< Node >& reps );
  bool didInstantiation( RepAlphabetIterator& riter );
};
class RepAlphabetIterator {
public:
  RepAlphabetIterator( Node f, RepAlphabet* ra ) : d_f( f ), d_ra( ra ){
    d_index.resize( f[0].getNumChildren(), 0 );
  }
  ~RepAlphabetIterator(){}
  Node d_f;
  RepAlphabet* d_ra;
  std::vector< int > d_index;
  void increment();
  bool isFinished();
  void getMatch( QuantifiersEngine* ie, InstMatch& m );
  Node getTerm( int i );
};

//instantiation strategies
class InstStrategyFinteModelFind : public InstStrategy{
private:
  /** was the current instantiation of this already done? */
  bool didInstantiation( RepAlphabetIterator& riter );
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_ith;
  /** strong solver class */
  StrongSolverTheoryUf* d_ss;
  /** map of current used instantiations */
  std::vector< RepAlphabet > d_inst_group;
  std::vector< RepAlphabet > d_inst_group_temp;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e, int limitInst );
public:
  InstStrategyFinteModelFind( context::Context* c, InstantiatorTheoryUf* ith, StrongSolverTheoryUf* ss, QuantifiersEngine* ie );
  ~InstStrategyFinteModelFind(){}
  /** identify */
  std::string identify() const { return std::string("FinteModelFind"); }
};

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

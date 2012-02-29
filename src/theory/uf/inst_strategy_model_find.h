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

//instantiation strategies

class InstStrategyFinteModelFind : public InstStrategy{
private:
  /** representative alphabet */
  class RepAlphabet {
  public:
    std::map< TypeNode, std::vector< Node > > d_type_reps;
    std::map< Node, int > d_indicies;
    void set( TypeNode t, std::vector< Node >& reps );
  };
  /** partial instantiation set */
  class PartialInstSet {
  public:
    PartialInstSet( RepAlphabet* ra, Node f ) : d_ra( ra ), d_f( f ){
      for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
        d_index.push_back( 0 );
      }
    }
    ~PartialInstSet(){}
    RepAlphabet* d_ra;
    Node d_f;
    std::vector< int > d_index;
    bool didCurrentInstantiation( PartialInstSet* pi );
    void increment();
    bool isFinished();
    void getMatch( QuantifiersEngine* ie, InstMatch& m );
    Node getTerm( int i );
  };
  /** was the current instantiation of this already done? */
  bool didCurrentInstantiation( PartialInstSet* pi );
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** map from types to sets of representatives */
  RepAlphabet* d_curr_ra;
  /** finding model */
  context::CDO< bool > d_finding_model;
  /** map of current used instantiations */
  std::map< Node, std::vector< PartialInstSet* > > d_inst_group;
public:
  InstStrategyFinteModelFind( context::Context* c, InstantiatorTheoryUf* th, QuantifiersEngine* ie );
  ~InstStrategyFinteModelFind(){}
  void resetInstantiationRound();
  int process( Node f, int effort );
  /** identify */
  std::string identify() const { return std::string("FinteModelFind"); }
};

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

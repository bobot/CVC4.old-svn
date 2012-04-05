/*********************                                                        */
/*! \file instantiation_engine.h
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
 ** \brief Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATION_ENGINE_H
#define __CVC4__INSTANTIATION_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstantiationEngine : public QuantifiersModule
{
private:
  TheoryQuantifiers* d_th;
  QuantifiersEngine* getQuantifiersEngine();
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** list of universally quantifiers currently asserted */
  BoolMap d_forall_asserts;
  /** are we in the middle of an instantiation round */
  context::CDO< bool > d_in_instRound;
  bool d_in_instRound_no_c;
  /** status of instantiation round (one of InstStrategy::STATUS_*) */
  int d_inst_round_status;
private:
  /** helper functions */
  bool hasNonArithmeticVariable( Node f );
  bool hasApplyUf( Node f );
  /** whether to do CBQI for quantifier f */
  bool doCbqi( Node f );
private:
  /** do instantiation round */
  bool doInstantiationRound( Theory::Effort effort );
  /** register literals of n, f is the quantifier it belongs to */
  void registerLiterals( Node n, Node f );
private:
  enum{
    SAT_CBQI,
    SAT_INST_STRATEGY,
  };
  /** debug sat */
  void debugSat( int reason );
public:
  InstantiationEngine( TheoryQuantifiers* th );
  ~InstantiationEngine(){}

  void check( Theory::Effort e );
  void registerQuantifier( Node n );
  void assertNode( Node n );
  Node explain(TNode n){return Node::null();};

};

}
}
}

#endif

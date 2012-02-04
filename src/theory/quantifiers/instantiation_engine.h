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
  typedef context::CDMap< Node, bool, NodeHashFunction > BoolMap;
  /** list of universally quantifiers currently asserted */
  BoolMap d_forall_asserts;
  /** status */
  int d_status;
  /** do instantiation round */
  bool doInstantiationRound();
private:
  /** register term, f is the quantifier it belongs to */
  void registerTerm( Node n, Node f );
  /** compute phase requirements */
  void computePhaseReqs( Node n, bool polarity );
public:
  InstantiationEngine( TheoryQuantifiers* th );
  ~InstantiationEngine(){}

  void check( Theory::Effort e );
  void registerQuantifier( Node n );
  void assertNode( Node n );
};

}
}
}

#endif

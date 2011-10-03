/*********************                                                        */
/*! \file instantiator_arith_instantiator.h
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
 ** \brief instantiator_arith_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATOR_ARITH_H
#define __CVC4__INSTANTIATOR_ARITH_H

#include "theory/instantiation_engine.h"
#include "theory/arith/arithvar_node_map.h"

namespace CVC4 {
namespace theory {
namespace arith {

class InstantiatorTheoryArith : public Instantiator{
  friend class InstantiationEngine;
private:
  /** delta */
  std::map< TypeNode, Node > d_deltas;
  /** for each quantifier, simplex rows */
  std::map< Node, std::vector< ArithVar > > d_instRows;
  /** tableaux */
  std::map< ArithVar, Node > d_tableaux_term;
  std::map< ArithVar, std::map< Node, Node > > d_tableaux;
  /** ce tableaux */
  std::map< ArithVar, std::map< Node, Node > > d_ceTableaux;
public:
  InstantiatorTheoryArith(context::Context* c, InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryArith() {}

  /** check function, assertion is asserted to theory */
  void check( Node assertion );
  /**  reset instantiation */
  void resetInstantiation();
  /** prepare instantiation method
    * post condition: set d_solved_ic and d_lemmas fields */
  bool doInstantiation( int effort );
private:
  /** add term to row */
  void addTermToRow( ArithVar x, Node n, Node& f, NodeBuilder<>& t );
  /** print debug */
  void printDebug();
  /** process at effort */
  void process( Node f, int effort );
  /** get delta for node */
  Node getDelta( Node n );
};/* class InstantiatiorTheoryArith  */

}
}
}

#endif
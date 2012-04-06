/*********************                                                        */
/*! \file arith_prop_manager.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
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

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROP_MANAGER_H
#define __CVC4__THEORY__ARITH__ARITH_PROP_MANAGER_H

#include "theory/valuation.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/arith/atom_database.h"
#include "theory/arith/delta_rational.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "theory/rewriter.h"
#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace arith {


class APM {
private:
  const ArithVarNodeMap& d_arithvarNodeMap;
  const ArithAtomDatabase& d_atomDatabase;
  Valuation d_valuation;

  Node boundAsNode(bool upperbound, ArithVar var, const DeltaRational& b) const;

  /**
   * Returns true if the node has a value in sat solver in the current context.
   * In debug mode this fails an Assert() if the node has a negative assignment.
   */
  bool isAsserted(TNode n) const;

  bool containsLiteral(TNode n) const {
    return d_atomDatabase.containsLiteral(n);
  }

public:
  APM(const ArithVarNodeMap& map,
                   const ArithAtomDatabase& db,
                   Valuation v):
    d_arithvarNodeMap(map), d_atomDatabase(db), d_valuation(v)
  {}


  Node strictlyWeakerLowerBound(TNode n) const{
    return d_atomDatabase.getWeakerImpliedLowerBound(n);
  }
  Node strictlyWeakerUpperBound(TNode n) const{
    return d_atomDatabase.getWeakerImpliedUpperBound(n);
  }

  Node strictlyWeakerAssertedUpperBound(ArithVar v, const DeltaRational& b) const;

  Node strictlyWeakerAssertedLowerBound(ArithVar v, const DeltaRational& b) const;

  Node getBestImpliedLowerBound(ArithVar v, const DeltaRational& b) const;
  Node getBestImpliedUpperBound(ArithVar v, const DeltaRational& b) const;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_PROP_MANAGER_H */

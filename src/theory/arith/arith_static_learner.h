/*********************                                                        */
/*! \file arith_static_learner.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H
#define __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H


#include "util/statistics_registry.h"
#include "theory/arith/arith_utilities.h"
#include "theory/substitutions.h"

#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include <set>

namespace CVC4 {
namespace theory {
namespace arith {

class ArithStaticLearner {
private:

  /* Maps a variable, x, to the set of defTrue nodes of the form
   *  (=> _ (= x c))
   * where c is a constant.
   */
  //typedef __gnu_cxx::hash_map<Node, std::set<Node>, NodeHashFunction> VarToNodeSetMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> CDNodeToNodeListMap;
  // The domain is an implicit list OR(x, OR(y, ..., FALSE ))
  // or FALSE
  CDNodeToNodeListMap d_miplibTrick;

  /**
   * Map from a node to it's minimum and maximum.
   */
  //typedef __gnu_cxx::hash_map<Node, DeltaRational, NodeHashFunction> NodeToMinMaxMap;
  typedef context::CDHashMap<Node, DeltaRational, NodeHashFunction> CDNodeToMinMaxMap;
  CDNodeToMinMaxMap d_minMap;
  CDNodeToMinMaxMap d_maxMap;

public:
  ArithStaticLearner(context::Context* userContext);
  void staticLearning(TNode n, NodeBuilder<>& learned);

  void addBound(TNode n);

private:
  void process(TNode n, NodeBuilder<>& learned, const TNodeSet& defTrue);

  void postProcess(NodeBuilder<>& learned);

  void iteMinMax(TNode n, NodeBuilder<>& learned);
  void iteConstant(TNode n, NodeBuilder<>& learned);

  void miplibTrick(TNode var, std::set<Rational>& values, NodeBuilder<>& learned);


  /** These fields are designed to be accessible to ArithStaticLearner methods. */
  class Statistics {
  public:
    IntStat d_iteMinMaxApplications;
    IntStat d_iteConstantApplications;

    IntStat d_miplibtrickApplications;
    AverageStat d_avgNumMiplibtrickValues;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};/* class ArithStaticLearner */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H */

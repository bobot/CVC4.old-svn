/*********************                                                        */
/*! \file theory_quantifiers.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): bobot, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of quantifiers.
 **
 ** Theory of quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H
#define __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H

#include "theory/theory.h"
#include "util/hash.h"
#include "util/statistics_registry.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {
class TheoryEngine;

namespace theory {
namespace quantifiers {

class ModelEngine;
class InstantiationEngine;

class TheoryQuantifiers : public Theory {
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** number of instantiations */
  int d_numInstantiations;
  int d_baseDecLevel;
  /** number of restarts */
  int d_numRestarts;

  KEEP_STATISTIC(TimerStat, d_theoryTime, "theory::quantifiers::theoryTime");

public:
  TheoryQuantifiers(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe);
  ~TheoryQuantifiers();

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void preRegisterTerm(TNode n);
  void presolve();
  void check(Effort e);
  void propagate(Effort level);
  Node getNextDecisionRequest();
  void collectModelInfo( TheoryModel* m, bool fullModel );
  void shutdown() { }
  std::string identify() const { return std::string("TheoryQuantifiers"); }
  bool flipDecision();
  void setUserAttribute( std::string& attr, Node n );
private:
  bool restart();
};/* class TheoryQuantifiers */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H */

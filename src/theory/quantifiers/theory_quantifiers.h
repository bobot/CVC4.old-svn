/*********************                                                        */
/*! \file theory_quantifiers.h
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
 ** \brief Theory of quantifiers.
 **
 ** Theory of quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H
#define __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H

#include "theory/theory.h"
#include "util/hash.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TheoryEngine;

class TheoryQuantifiers : public Theory {
private:
  typedef context::CDMap< Node, bool, NodeHashFunction > BoolMap;

  /** list of existential quantifiers currently asserted */
  BoolMap d_exists_asserts;
  /** list of counterexamples currently asserted */
  BoolMap d_counterexample_asserts;
  /** quantifiers that have been skolemized */
  std::map< Node, bool > d_skolemized;
  /** number of instantiations */
  int d_numInstantiations;
  int d_baseDecLevel;
  /** number of restarts */
  int d_numRestarts;
public:
  TheoryQuantifiers(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, QuantifiersEngine* qe );
  ~TheoryQuantifiers();

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void preRegisterTerm(TNode n);
  void presolve();
  void check(Effort e);
  Node getValue(TNode n);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryQuantifiers"); }
  bool flipDecision();
private:
  void assertUniversal( Node n );
  void assertExistential( Node n );
  void assertCounterexample( Node n );
  bool restart();
public:
  static bool isRewriteKind( Kind k ){
    return k==kind::REWRITE_RULE || k==kind::REDUCTION_RULE || k==kind::DEDUCTION_RULE;
  }
};/* class TheoryQuantifiers */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H */

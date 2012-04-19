/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__THEORY_BV_H
#define __CVC4__THEORY__BV__THEORY_BV_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdhashset.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/stats.h"
#include "theory/uf/equality_engine.h"
#include "context/cdqueue.h"

namespace BVMinisat {
class SimpSolver; 
}


namespace CVC4 {
namespace theory {
namespace bv {

/// forward declarations 
class Bitblaster;

static inline std::string spaces(int level)
{
  std::string indentStr(level, ' ');
  return indentStr;
}

class TheoryBV : public Theory {


private:

  /** The context we are using */
  context::Context* d_context;

  /** The asserted stuff */
  context::CDList<TNode> d_assertions;
  
  /** Bitblaster */
  Bitblaster* d_bitblaster; 
  Node d_true;
  Node d_false;
    
  /** Context dependent set of atoms we already propagated */
  context::CDHashSet<TNode, TNodeHashFunction> d_alreadyPropagatedSet;

public:

  TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation);
  ~TheoryBV(); 

  void preRegisterTerm(TNode n);

  void check(Effort e);

  Node explain(TNode n);

  Node getValue(TNode n);

  std::string identify() const { return std::string("TheoryBV"); }

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions); 

private:
  
  class Statistics {
  public:
    AverageStat d_avgConflictSize;
    IntStat     d_solveSubstitutions;
    TimerStat   d_solveTimer;  
    Statistics();
    ~Statistics(); 
  }; 
  
  Statistics d_statistics;
  
  // Added by Clark
  // NotifyClass: template helper class for d_equalityEngine - handles call-back from congruence closure module
  class NotifyClass {
    TheoryBV& d_bv;
  public:
    NotifyClass(TheoryBV& uf): d_bv(uf) {}

    bool notify(TNode propagation) {
      Debug("bitvector") << spaces(d_bv.getContext()->getLevel()) << "NotifyClass::notify(" << propagation << ")" << std::endl;
      // Just forward to bv
      return d_bv.storePropagation(propagation, SUB_EQUALITY);
    }

    void notify(TNode t1, TNode t2) {
      Debug("arrays") << spaces(d_bv.getContext()->getLevel()) << "NotifyClass::notify(" << t1 << ", " << t2 << ")" << std::endl;
      // Propagate equality between shared terms
      Node equality = Rewriter::rewriteEquality(theory::THEORY_UF, t1.eqNode(t2));
      d_bv.storePropagation(t1.eqNode(t2), SUB_EQUALITY);
    }
  };

  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** Equaltity engine */
  uf::EqualityEngine<NotifyClass> d_equalityEngine;

  // Are we in conflict?
  context::CDO<bool> d_conflict;

  /** The conflict node */
  Node d_conflictNode;

  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  context::CDQueue<Node> d_toBitBlast;

  enum SubTheory {
    SUB_EQUALITY = 1,
    SUB_BITBLASTER = 2
  };

  /**
   * Keeps a map from nodes to the subtheory that propagated it so that we can explain it
   * properly.
   */
  typedef context::CDHashMap<Node, SubTheory, NodeHashFunction> PropagatedMap;
  PropagatedMap d_propagatedBy;

  bool propagatedBy(TNode literal, SubTheory subtheory) const {
    PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
    if (find == d_propagatedBy.end()) return false;
    else return (*find).second == subtheory;
  }

  /** Should be called to propagate the literal.  */
  bool storePropagation(TNode literal, SubTheory subtheory);

  /**
   * Explains why this literal (propagated by subtheory) is true by adding assumptions.
   */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  void addSharedTerm(TNode t);

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  friend class Bitblaster;

public:

  void propagate(Effort e);
  
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */

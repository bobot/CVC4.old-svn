/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
#include "context/cdset.h"
#include "context/cdlist.h"
#include "theory/bv/core/slice_manager.h"
#include "theory/bv/core/watch_manager.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TheoryBV : public Theory {

public:

  /**
   * Enumeration of sub-theories of bit-vectors.
   */
  enum SubTheory {
    EQUALITY_CORE,
    SUBTHEORY_LAST
  };

private:

  /** Information to recover explanations of propagations */
  struct propagation_info {
    /** Subtheory that spawned the propagation */
    SubTheory subTheory;
    /** Specific information to recover the propagation */
    unsigned info;
    /** The propagated literal */
    TNode literal;
    /** Constructor */
    propagation_info(SubTheory subTheory, unsigned info, TNode literal):
      subTheory(subTheory),
      info(info),
      literal(literal)
    {}
    /** Default constructor for maps */
    propagation_info():
      subTheory(SUBTHEORY_LAST)
    {}
  };

  /**
   * This is the notify class for the watch manager. All propagated equalities are passed on to the instance
   * of this class.
   */
  class WatchNotify {
    /** The responsible theory instance */
    TheoryBV& d_theoryBV;
  public:
    /** Construct the notify class with the theory instance */
    WatchNotify(TheoryBV& theoryBV) :
      d_theoryBV(theoryBV) {
    }

    /** Propagates that equality is true or false (based on value), return true if in conflict */
    bool operator ()(unsigned watchIndex, TNode eq, bool value) {
      Debug("theory::bv") << "WatchNotify(" << eq << ", " << (value ? "true" : "false") << ")" << std::endl;
      return d_theoryBV.propagate(propagation_info(EQUALITY_CORE, watchIndex, value ? eq : (TNode) eq.notNode()));
    }
  };

  /** List of things to propagate */
  context::CDList<propagation_info> d_toPropagateList;

  /** Index of the last propagated node */
  context::CDO<unsigned> d_toPropagateIndex;

private:

  /** Watch manager notify object */
  WatchNotify d_watchNotify;

  /** Watch manager */
  ConcatWatchManager<WatchNotify> d_watchManager;

  /** Slice manager */
  SliceManager< ConcatWatchManager<WatchNotify> > d_sliceManager;
  
  /** The context we are using */
  context::Context* d_context;

  /** The asserted stuff */
  context::CDSet<TNode, TNodeHashFunction> d_assertions;

  /** Map from propagated literal to their propagation information */
  context::CDMap<TNode, propagation_info, TNodeHashFunction> d_propagationInfo;

  /** Explain the reason why node is true */
  void explainPropagation(TNode node, std::vector<TNode>& reasons);

  /** Called by a sub-theory to propagate, return true if in conflict */
  bool propagate(const propagation_info& propInfo);

public:

  TheoryBV(context::Context* c, OutputChannel& out, Valuation valuation):
    Theory(THEORY_BV, c, out, valuation),
    d_toPropagateList(c),
    d_toPropagateIndex(c, 0),
    d_watchNotify(*this),
    d_watchManager(d_watchNotify, c),
    d_sliceManager(d_watchManager.getEqualityManager(), c),
    d_context(c),
    d_assertions(c),
    d_propagationInfo(c)
  {
  }

  void preRegisterTerm(TNode n);

  void check(Effort e);

  void explain(TNode n);

  Node getValue(TNode n);

  void propagate(Effort level);

  std::string identify() const { return std::string("TheoryBV"); }
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */

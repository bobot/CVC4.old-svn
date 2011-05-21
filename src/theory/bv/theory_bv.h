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
#include "theory/bv/core/equality_engine.h"
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
    EQUALITY_CORE
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
      info(info),
      literal(literal)
    {}
  };

  /** List of things to propagate */
  context::CDList<propagation_info> d_toPropagateList;

  /** Index of the last propagated node */
  context::CDO<unsigned> d_toPropagateIndex;

public:

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
      d_theoryBV(theoryBV)
    {}

    /** Propagates that equality is true or false (based on value) */
    void operator () (unsigned watchIndex, TNode eq, bool value) {
      Debug("theory::bv") << "WatchNotify(" << eq << ", " << (value ? "true" : "false") << ")" << std::endl;
      d_theoryBV.d_toPropagateList.push_back(propagation_info(EQUALITY_CORE, watchIndex, value ? eq : (TNode) eq.notNode()));
    }
  };

  struct BVEqualitySettings {
    static inline bool descend(TNode node) {
      return node.getKind() == kind::BITVECTOR_CONCAT || node.getKind() == kind::BITVECTOR_EXTRACT;
    }

    /** Returns true if node1 has preference to node2 as a representative, otherwise node2 is used */
    static inline bool mergePreference(TNode node1, unsigned node1size, TNode node2, unsigned node2size) {
      if (node1.getKind() == kind::CONST_BITVECTOR) {
        Assert(node2.getKind() != kind::CONST_BITVECTOR);
        return true;
      }
      if (node2.getKind() == kind::CONST_BITVECTOR) {
        Assert(node1.getKind() != kind::CONST_BITVECTOR);
        return false;
      }
      if (node1.getKind() == kind::BITVECTOR_CONCAT) {
        Assert(node2.getKind() != kind::BITVECTOR_CONCAT);
        return true;
      }
      if (node2.getKind() == kind::BITVECTOR_CONCAT) {
        Assert(node1.getKind() != kind::BITVECTOR_CONCAT);
        return false;
      }
      return node2size < node1size;
    }
  };

private:

  /** Watch manager notify object */
  WatchNotify d_watchNotify;

  /** Watch manager */
  typedef ConcatWatchManager<WatchNotify> watch_manager;
  watch_manager d_watchManager;

  /** Equality reasoning engine */
  typedef EqualityEngine<watch_manager, BVEqualitySettings> equality_engine;
  equality_engine d_eqEngine;

  /** Slice manager */
  typedef SliceManager<equality_engine> slice_manager;
  slice_manager d_sliceManager;
  
  /** The context we are using */
  context::Context* d_context;

  /** The asserted stuff */
  context::CDSet<TNode, TNodeHashFunction> d_assertions;

public:

  TheoryBV(context::Context* c, OutputChannel& out, Valuation valuation):
    Theory(THEORY_BV, c, out, valuation),
    d_toPropagateList(c),
    d_toPropagateIndex(c, 0),
    d_watchNotify(*this),
    d_watchManager(d_watchNotify, c),
    d_eqEngine(d_watchManager, c, "bv_eq_engine"),
    d_sliceManager(d_eqEngine, c), 
    d_context(c),
    d_assertions(c)
  {
  }

  void preRegisterTerm(TNode n);

  void check(Effort e);

  void propagate(Effort e) { }

  void explain(TNode n);

  Node getValue(TNode n);

  std::string identify() const { return std::string("TheoryBV"); }
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */

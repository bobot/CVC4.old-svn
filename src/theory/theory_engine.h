/*********************                                                        */
/*! \file theory_engine.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory engine.
 **
 ** The theory engine.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_ENGINE_H
#define __CVC4__THEORY_ENGINE_H

#include "expr/node.h"
#include "theory/theory.h"
#include "theory/theoryof_table.h"

#include "prop/prop_engine.h"
#include "theory/booleans/theory_bool.h"
#include "theory/uf/theory_uf.h"
#include "theory/arith/theory_arith.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * CVC4.
 */
class TheoryEngine {

  /** Associated PropEngine engine */
  prop::PropEngine* d_propEngine;

  /** A table of Kinds to pointers to Theory */
  theory::TheoryOfTable d_theoryOfTable;

  /**
   * An output channel for Theory that passes messages
   * back to a TheoryEngine.
   */
  class EngineOutputChannel : public theory::OutputChannel {

    friend class TheoryEngine;

    TheoryEngine* d_engine;
    context::Context* d_context;
    context::CDO<Node> d_conflictNode;
    context::CDO<Node> d_explanationNode;

    /**
     * Literals that are propagated by the theory. Note that these are TNodes.
     * The theory can only propagate nodes that have an assigned literal in the
     * sat solver and are hence referenced in the SAT solver.
     */
    std::vector<TNode> d_propagatedLiterals;

  public:

    EngineOutputChannel(TheoryEngine* engine, context::Context* context) :
      d_engine(engine),
      d_context(context),
      d_conflictNode(context),
      d_explanationNode(context){
    }

    void conflict(TNode conflictNode, bool safe) throw(theory::Interrupted, AssertionException) {
      Debug("theory") << "EngineOutputChannel::conflict(" << conflictNode << ")" << std::endl;
      d_conflictNode = conflictNode;
      if(safe) {
        throw theory::Interrupted();
      }
    }

    void propagate(TNode lit, bool) throw(theory::Interrupted, AssertionException) {
      d_propagatedLiterals.push_back(lit);
    }

    void lemma(TNode node, bool) throw(theory::Interrupted, AssertionException) {
      d_engine->newLemma(node);
    }
    void augmentingLemma(TNode node, bool) throw(theory::Interrupted, AssertionException) {
      d_engine->newAugmentingLemma(node);
    }
    void explanation(TNode explanationNode, bool) throw(theory::Interrupted, AssertionException) {
      d_explanationNode = explanationNode;
    }
  };

  EngineOutputChannel d_theoryOut;

  theory::booleans::TheoryBool d_bool;
  theory::uf::TheoryUF d_uf;
  theory::arith::TheoryArith d_arith;
  theory::arrays::TheoryArrays d_arrays;
  theory::bv::TheoryBV d_bv;

  /**
   * Check whether a node is in the rewrite cache or not.
   */
  static bool inRewriteCache(TNode n) throw() {
    return n.hasAttribute(theory::RewriteCache());
  }

  /**
   * Get the value of the rewrite cache (or Node::null()) if there is
   * none).
   */
  static Node getRewriteCache(TNode n) throw() {
    return n.getAttribute(theory::RewriteCache());
  }

  /**
   * Get the value of the rewrite cache (or Node::null()) if there is
   * none).
   */
  static void setRewriteCache(TNode n, TNode v) throw() {
    return n.setAttribute(theory::RewriteCache(), v);
  }

  /**
   * This is the top rewrite entry point, called during preprocessing.
   * It dispatches to the proper theories to rewrite the given Node.
   */
  Node rewrite(TNode in);

  /**
   * Convenience function to recurse through the children, rewriting,
   * while leaving the Node's kind alone.
   */
  Node rewriteChildren(TNode in) {
    if(in.getMetaKind() == kind::metakind::CONSTANT) {
      return in;
    }

    NodeBuilder<> b(in.getKind());
    if(in.getMetaKind() == kind::metakind::PARAMETERIZED){
      Assert(in.hasOperator());
      b << in.getOperator();
    }
    for(TNode::iterator c = in.begin(); c != in.end(); ++c) {
      b << rewrite(*c);
    }
    Debug("rewrite") << "rewrote-children of " << in << std::endl
                     << "got " << b << std::endl;
    Node ret = b;
    return ret;
  }

  /**
   * Rewrite Nodes with builtin kind (that is, those Nodes n for which
   * theoryOf(n) == NULL).  The master list is in expr/builtin_kinds.
   */
  Node rewriteBuiltins(TNode in) {
    switch(Kind k = in.getKind()) {
    case kind::EQUAL:
      return rewriteChildren(in);

    case kind::ITE:
      Unhandled(k);

    case kind::SKOLEM:
    case kind::VARIABLE:
      return in;

    case kind::TUPLE:
      return rewriteChildren(in);

    default:
      Unhandled(k);
    }
  }

  Node removeITEs(TNode t);

public:

  /**
   * Construct a theory engine.
   */
  TheoryEngine(context::Context* ctxt) :
    d_propEngine(NULL),
    d_theoryOut(this, ctxt),
    d_bool(ctxt, d_theoryOut),
    d_uf(ctxt, d_theoryOut),
    d_arith(ctxt, d_theoryOut),
    d_arrays(ctxt, d_theoryOut),
    d_bv(ctxt, d_theoryOut) {

    d_theoryOfTable.registerTheory(&d_bool);
    d_theoryOfTable.registerTheory(&d_uf);
    d_theoryOfTable.registerTheory(&d_arith);
    d_theoryOfTable.registerTheory(&d_arrays);
    d_theoryOfTable.registerTheory(&d_bv);
  }

  void setPropEngine(prop::PropEngine* propEngine)
  {
    Assert(d_propEngine == NULL);
    d_propEngine = propEngine;
  }

  /**
   * This is called at shutdown time by the SmtEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory.
   */
  void shutdown() {
    d_bool.shutdown();
    d_uf.shutdown();
    d_arith.shutdown();
    d_arrays.shutdown();
    d_bv.shutdown();
  }

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  theory::Theory* theoryOf(TNode n) {
    Kind k = n.getKind();

    Assert(k >= 0 && k < kind::LAST_KIND);

    if(k == kind::VARIABLE) {
      TypeNode t = n.getType();
      if(t.isBoolean()){
        return &d_bool;
      }else if(t.isReal()){
        return &d_arith;
      }else{
        return &d_uf;
      }
      //Unimplemented();
    } else if(k == kind::EQUAL) {
      // if LHS is a VARIABLE, use theoryOf(LHS.getType())
      // otherwise, use theoryOf(LHS)
      TNode lhs = n[0];
      if(lhs.getKind() == kind::VARIABLE) {
        // FIXME: we don't yet have a Type-to-Theory map.  When we do,
        // look up the type of the LHS and return that Theory (?)

        //The following JUST hacks around this lack of a table
        TypeNode type_of_n = lhs.getType();
        if(type_of_n.isReal()){
          return &d_arith;
        }else{
          return &d_uf;
          //Unimplemented();
        }
      } else {
        return theoryOf(lhs);
      }
    } else {
      // use our Kind-to-Theory mapping
      return d_theoryOfTable[k];
    }
  }

  /**
   * Preprocess a node.  This involves theory-specific rewriting, then
   * calling preRegisterTerm() on what's left over.
   * @param n the node to preprocess
   */
  Node preprocess(TNode n);

  /**
   * Assert the formula to the apropriate theory.
   * @param node the assertion
   */
  inline void assertFact(TNode node) {
    Debug("theory") << "TheoryEngine::assertFact(" << node << ")" << std::endl;
    theory::Theory* theory =
      node.getKind() == kind::NOT ? theoryOf(node[0]) : theoryOf(node);
    if(theory != NULL) {
      theory->assertFact(node);
    }
  }

  /**
   * Check all (currently-active) theories for conflicts.
   * @param effort the effort level to use
   */
  inline bool check(theory::Theory::Effort effort)
  {
    d_theoryOut.d_conflictNode = Node::null();
    d_theoryOut.d_propagatedLiterals.clear();
    // Do the checking
    try {
      //d_bool.check(effort);
      d_uf.check(effort);
      d_arith.check(effort);
      //d_arrays.check(effort);
      //d_bv.check(effort);
    } catch(const theory::Interrupted&) {
      Debug("theory") << "TheoryEngine::check() => conflict" << std::endl;
    }
    // Return wheather we have a conflict
    return d_theoryOut.d_conflictNode.get().isNull();
  }

  inline const std::vector<TNode>& getPropagatedLiterals() const {
    return d_theoryOut.d_propagatedLiterals;
  }

  void clearPropagatedLiterals() {
    d_theoryOut.d_propagatedLiterals.clear();
  }

  inline void newLemma(TNode node) {
    d_propEngine->assertLemma(node);
  }

  inline void newAugmentingLemma(TNode node) {
    Node preprocessed = preprocess(node);
    d_propEngine->assertFormula(preprocessed);
  }

  /**
   * Returns the last conflict (if any).
   */
  inline Node getConflict() {
    return d_theoryOut.d_conflictNode;
  }

  inline void propagate() {
    d_theoryOut.d_propagatedLiterals.clear();
    // Do the propagation
    d_uf.propagate(theory::Theory::FULL_EFFORT);
    d_arith.propagate(theory::Theory::FULL_EFFORT);
  }

  inline Node getExplanation(TNode node){
    theory::Theory* theory = theoryOf(node);
    d_theoryOut.d_explanationNode = Node::null();
    theory->explain(node);
    return d_theoryOut.d_explanationNode;
  }

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */

/*********************                                                        */
/*! \file cnf_stream.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters, dejan
 ** Minor contributors (to current version): barrett, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This class transforms a sequence of formulas into clauses.
 **
 ** This class takes a sequence of formulas.
 ** It outputs a stream of clauses that is propositionally
 ** equi-satisfiable with the conjunction of the formulas.
 ** This stream is maintained in an online fashion.
 **
 ** Unlike other parts of the system it is aware of the PropEngine's
 ** internals such as the representation and translation of [??? -Chris]
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROP__CNF_STREAM_H
#define __CVC4__PROP__CNF_STREAM_H

#include "expr/node.h"
#include "prop/sat.h"
#include "theory/registrar.h"

#include <ext/hash_map>

namespace CVC4 {
namespace prop {


class PropEngine;

/**
 * Comments for the behavior of the whole class... [??? -Chris]
 * @author Tim King <taking@cs.nyu.edu>
 */
class CnfStream {

public:

  /** Cache of what nodes have been registered to a literal. */
  typedef __gnu_cxx::hash_map<SatLiteral, TNode, SatSolver::SatLiteralHashFunction> NodeCache;

  /** Per node translation information */
  struct TranslationInfo {
    bool recorded;
    /** The level at which this node was translated (negative if not translated) */
    int level;
    /** The literal of this node */
    SatLiteral literal;
  };

  /** Cache of what literals have been registered to a node. */
  typedef __gnu_cxx::hash_map<Node, TranslationInfo, NodeHashFunction> TranslationCache;

protected:

  /** The SAT solver we will be using */
  SatInputInterface *d_satSolver;

  TranslationCache d_translationCache;
  NodeCache d_nodeCache;

  /** The "registrar" for pre-registration of terms */
  theory::Registrar d_registrar;

  /** Top level nodes that we translated */
  std::vector<TNode> d_translationTrail;

  /**
   * How many literals were already mapped at the top-level when we
   * tried to convertAndAssert() something.  This
   * achieves early detection of units and leads to fewer
   * clauses.  It's motivated by the following pattern:
   *
   *   ASSERT  BIG FORMULA => x
   *   (and then later...)
   *   ASSERT  BIG FORMULA
   *
   * With the first assert, BIG FORMULA is clausified, and a literal
   * is assigned for the top level so that the final clause for the
   * implication is "lit => x".  But without "fortunate literal
   * detection," when BIG FORMULA is later asserted, it is clausified
   * separately, and "lit" is never asserted as a unit clause.
   */
  KEEP_STATISTIC(IntStat, d_fortunateLiterals, "prop::CnfStream::fortunateLiterals", 0);

  /** Remove nots from the node */
  TNode stripNot(TNode node) {
    while (node.getKind() == kind::NOT) {
      node = node[0];
    }
    return node;
  }

  /** Record this translation */
  void recordTranslation(TNode node, bool alwaysRecord = false);

  /**
   * Moves the node and all of it's parents to level 0.
   */
  void moveToBaseLevel(TNode node);

  /**
   * Mark the node, and all parent at levels above level as untranslated.
   */
  void undoTranslate(TNode node, int level);

  /**
   * Are we asserting a removable clause (true) or a permanent clause (false).
   * This is set at the begining of convertAndAssert so that it doesn't
   * need to be passed on over the stack.
   */
  bool d_removable;

  /**
   * Asserts the given clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param clause the clause to assert
   */
  void assertClause(TNode node, SatClause& clause);

  /**
   * Asserts the unit clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the unit literal of the clause
   */
  void assertClause(TNode node, SatLiteral a);

  /**
   * Asserts the binary clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   */
  void assertClause(TNode node, SatLiteral a, SatLiteral b);

  /**
   * Asserts the ternary clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   * @param c the thirs literal in the clause
   */
  void assertClause(TNode node, SatLiteral a, SatLiteral b, SatLiteral c);

  /**
   * Acquires a new variable from the SAT solver to represent the node
   * and inserts the necessary data it into the mapping tables.
   * @param node a formula
   * @param theoryLiteral whether this literal a theory literal (and
   * therefore the theory is to be informed when set to true/false)
   * @return the literal corresponding to the formula
   */
  SatLiteral newLiteral(TNode node, bool theoryLiteral = false);

  /**
   * Constructs a new literal for an atom and returns it.  Calls
   * newLiteral().
   *
   * @param node the node to convert; there should be no boolean
   * structure in this expression.  Assumed to not be in the
   * translation cache.
   */
  SatLiteral convertAtom(TNode node);

public:

  /**
   * Constructs a CnfStream that sends constructs an equi-satisfiable
   * set of clauses and sends them to the given sat solver.
   * @param satSolver the sat solver to use
   * @param registrar the entity that takes care of preregistration of Nodes
   */
  CnfStream(SatInputInterface* satSolver, theory::Registrar registrar);

  /**
   * Destructs a CnfStream.  This implementation does nothing, but we
   * need a virtual destructor for safety in case subclasses have a
   * destructor.
   */
  virtual ~CnfStream() {
  }

  /**
   * Converts and asserts a formula.
   * @param node node to convert and assert
   * @param removable whether the sat solver can choose to remove the clauses
   * @param negated whether we are asserting the node negated
   */
  virtual void convertAndAssert(TNode node, bool removable, bool negated) = 0;

  /**
   * Get the node that is represented by the given SatLiteral.
   * @param literal the literal from the sat solver
   * @return the actual node
   */
  TNode getNode(const SatLiteral& literal);

  /**
   * Returns true if the node has been cached in the translation cache.
   * @param node the node
   * @return true if the node has been cached
   */
  bool isTranslated(TNode node) const;

  /**
   * Returns true iff the node has an assigned literal (it might not be translated).
   * @param node the node
   */
  bool hasLiteral(TNode node) const;

  /**
   * Ensure that the given node will have a designated SAT literal
   * that is definitionally equal to it.  The result of this function
   * is that the Node can be queried via getSatValue().  Essentially,
   * this is like a "convert-but-don't-assert" version of
   * convertAndAssert().
   */
  virtual void ensureLiteral(TNode n) = 0;

  /**
   * Returns the literal that represents the given node in the SAT CNF
   * representation.
   * @param node [Presumably there are some constraints on the kind of
   * node? E.g., it needs to be a boolean? -Chris]
   */
  SatLiteral getLiteral(TNode node);

  const TranslationCache& getTranslationCache() const {
    return d_translationCache;
  }

  const NodeCache& getNodeCache() const {
    return d_nodeCache;
  }

  /**
   * Removes all the translation information of clauses that have the given associated assert level.
   */
  void removeClausesAboveLevel(int level);

};/* class CnfStream */


/**
 * TseitinCnfStream is based on the following recursive algorithm
 * http://people.inf.ethz.ch/daniekro/classes/251-0247-00/f2007/readings/Tseitin70.pdf
 * The general idea is to introduce a new literal that
 * will be equivalent to each subexpression in the constructed equi-satisfiable
 * formula, then substitute the new literal for the formula, and so on,
 * recursively.
 *
 * This implementation does this in a single recursive pass. [??? -Chris]
 */
class TseitinCnfStream : public CnfStream {

public:

  /**
   * Convert a given formula to CNF and assert it to the SAT solver.
   * @param node the formula to assert
   * @param removable is this something that can be erased
   * @param negated true if negated
   */
  void convertAndAssert(TNode node, bool removable, bool negated);

  /**
   * Constructs the stream to use the given sat solver.
   * @param satSolver the sat solver to use
   * @param registrar the entity that takes care of pre-registration of Nodes
   */
  TseitinCnfStream(SatInputInterface* satSolver, theory::Registrar registrar);

private:

  /**
   * Same as above, except that removable is rememebered.
   */
  void convertAndAssert(TNode node, bool negated);

  // Each of these formulas handles takes care of a Node of each Kind.
  //
  // Each handleX(Node &n) is responsible for:
  //   - constructing a new literal, l (if necessary)
  //   - calling registerNode(n,l)
  //   - adding clauses assure that l is equivalent to the Node
  //   - calling toCNF on its children (if necessary)
  //   - returning l
  //
  // handleX( n ) can assume that n is not in d_translationCache
  SatLiteral handleNot(TNode node);
  SatLiteral handleXor(TNode node);
  SatLiteral handleImplies(TNode node);
  SatLiteral handleIff(TNode node);
  SatLiteral handleIte(TNode node);
  SatLiteral handleAnd(TNode node);
  SatLiteral handleOr(TNode node);

  void convertAndAssertAnd(TNode node, bool negated);
  void convertAndAssertOr(TNode node, bool negated);
  void convertAndAssertXor(TNode node, bool negated);
  void convertAndAssertIff(TNode node, bool negated);
  void convertAndAssertImplies(TNode node, bool negated);
  void convertAndAssertIte(TNode node, bool negated);

  /**
   * Transforms the node into CNF recursively.
   * @param node the formula to transform
   * @param negated wheather the literal is negated
   * @return the literal representing the root of the formula
   */
  SatLiteral toCNF(TNode node, bool negated = false);

  void ensureLiteral(TNode n);

};/* class TseitinCnfStream */


}/* CVC4::prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PROP__CNF_STREAM_H */

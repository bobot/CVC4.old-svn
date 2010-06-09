/*********************                                                        */
/*! \file cnf_stream.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: cconway, dejan
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

#ifndef __CVC4__CNF_STREAM_H
#define __CVC4__CNF_STREAM_H

#include "expr/node.h"
#include "prop/sat.h"

#include <ext/hash_map>
#include <ext/hash_set>

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
  typedef __gnu_cxx::hash_map<SatLiteral, Node, SatSolver::SatLiteralHashFunction> LiteralToNodeMap;

  /** Cache of what literals have been registered to a node. */
  typedef __gnu_cxx::hash_map<Node, SatLiteral, NodeHashFunction> NodeToLiteralMap;

  /** Nodes that have pure clauses */
  typedef __gnu_cxx::hash_set<Node, NodeHashFunction> NodesWithPureClausesSet;

  /** Map the clauses to the nodes that generated them */
  typedef __gnu_cxx::hash_map<unsigned, TNode> ClauseToNodeMap;

  /** Map from nodes to their reference counts (in the CNF context) */
  typedef __gnu_cxx::hash_map<TNode, unsigned, NodeHashFunction> NodeRefCountMap;

private:

  /** The SAT solver we will be using */
  SatInputInterface *d_satSolver;

  /** Cache of what literals have been registered to a node. */
  NodeToLiteralMap d_nodeToLiteralMap;

  /** Cache of nodes that are not mapped to a literal, but produced a clause */
  NodesWithPureClausesSet d_nodesWithPureClauseSet;

  /** Cache of what nodes have been registered to a literal. */
  LiteralToNodeMap d_literalToNodeMap;

  /** Map the clauses to the nodes that generated them */
  ClauseToNodeMap d_clauseToNodeMap;

  /**
   * Map from atomic nodes to their reference counts (in the CNF context).
   * The count includes the negated literals.
   */
  NodeRefCountMap d_nodeRefCountLiterals;

  /** Map from nodes to their clause reference counts (in the CNF context) */
  NodeRefCountMap d_nodeRefCountClauses;

protected:

  /**
   * Are we asserting a lemma (true) or a permanent clause (false).
   * This is set at the begining of convertAndAssert so that it doesn't
   * need to be passed on over the stack.
   */
  bool d_assertingLemma;

  /**
   * Asserts the given clause to the sat solver.
   * @param clause the clasue to assert
   */
  void assertClause(TNode node, SatClause& clause);

  /**
   * Asserts the unit clause to the sat solver.
   * @param a the unit literal of the clause
   */
  void assertClause(TNode node, SatLiteral a);

  /**
   * Asserts the binary clause to the sat solver.
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   */
  void assertClause(TNode node, SatLiteral a, SatLiteral b);

  /**
   * Asserts the ternary clause to the sat solver.
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   * @param c the third literal in the clause
   */
  void assertClause(TNode node, SatLiteral a, SatLiteral b, SatLiteral c);

  /**
   * Returns true if the node has been cashed in the translation cache.
   * @param node the node
   * @return true if the node has been cached
   */
  bool isCached(TNode node) const;

  /**
   * Returns the cashed literal corresponding to the given node.
   * @param node the node to lookup
   * @return returns the corresponding literal
   */
  SatLiteral lookupInCache(TNode n) const;

  /**
   * Caches the pair of the node and the literal corresponding to the
   * translation.
   * @param node node
   * @param lit
   */
  void cacheTranslation(TNode node, SatLiteral lit);

  /**
   * Marks a node as being translated to pure clauses. For example, (x or y)
   * does not procude a literal, but wee need to keep track of the translation.
   */
  void cachePureTranslation(TNode node);

  /**
   * Acquires a new variable from the SAT solver to represent the node and
   * inserts the necessary data it into the mapping tables.
   * @param node a formula
   * @param theoryLiteral is this literal a theory literal (i.e. theory to be
   *        informed when set to true/false
   * @return the literal corresponding to the formula
   */
  SatLiteral newLiteral(TNode node, bool theoryLiteral = false);

  /**
   * Returns the positive version of the node. If the node is !a it returns a
   * otherwise it returns the node itself.
   * @param node the node to process
   * @return the node stripped of the top negation (if there)
   */
  static inline Node getPositive(TNode node) {
    return node.getKind() == kind::NOT ? node[0] : node;
  }

  /**
   * Increase the literal to node reference count.
   * @param node the node that the literal points to
   */
  void incLiteralRefCount(TNode node);

  /**
   * Decrease the literal to node reference count. Note that reference counts
   * are kept together for the node and it's negation, so either can be passed
   * in.
   * @param node the node that the literal points to
   * @return the resulting reference count
   */
  unsigned decLiteralRefCount(TNode node);

  /**
   * Returns the literal to node reference count.
   * @return the reference count
   */
  unsigned getLiteralRefCount(TNode node) const;

  /**
   * Increase the clause to node reference count.
   * @param node the node that the clause points to
   */
  void incClauseRefCount(TNode node) { Assert(!node.isNull()); ++ d_nodeRefCountClauses[node]; }

  /**
   * Decrease the clause to node reference count.
   * @param node the node that the clause points to
   * @return the resulting reference count
   */
  unsigned decClauseRefCount(TNode node) { Assert(!node.isNull()); return -- d_nodeRefCountClauses[node]; }

  /**
   * Returns the clause to node reference count.
   * @return the reference count
   */
  unsigned getClauseRefCount(TNode node) const;

  /**
   * Returns the global reference count for the node and it's negation.
   */
  unsigned getTotalRefCount(TNode node) const;

  /**
   * Returns the node that generated the clause with the given id.
   * @param clauseId the SAT solver id of the clause
   */
  TNode getGeneratingNode(int clauseId) const;

  /**
   * Remove the given node (and it's negation) from all the maps.
   * An actuall NODE must be passed in as it might be the last reference.
   * @param node node to erase
   */
  void releaseNode(Node node);

public:

  /**
   * Constructs a CnfStream that sends constructs an equi-satisfiable set of clauses
   * and sends them to the given sat solver.
   * @param satSolver the sat solver to use
   */
  CnfStream(SatInputInterface* satSolver);

  /**
   * Destructs a CnfStream.  This implementation does nothing, but we
   * need a virtual destructor for safety in case subclasses have a
   * destructor.
   */

  virtual ~CnfStream();

  /**
   * Converts and asserts a formula.
   * @param node node to convert and assert
   * @param whether the sat solver can choose to remove the clauses
   * @param negated wheather we are asserting the node negated
   */
  virtual void convertAndAssert(TNode node, bool lemma, bool negated = false) = 0;

  /**
   * Get the node that is represented by the given SatLiteral.
   * @param literal the literal from the sat solver
   * @return the actual node
   */
  Node getNode(const SatLiteral& literal) const;

  /**
   * Returns the literal that represents the given node in the SAT CNF
   * representation. [Presumably there are some constraints on the kind
   * of node? E.g., it needs to be a boolean? -Chris]
   *
   */
  SatLiteral getLiteral(TNode node);

  /**
   * Returns true if the state of the CNF translation is such that the
   * clause can be erased. A clause can be erased if the no other clause
   * is using the node that generated this clause, i.e. the reference count
   * of the node is 0. This should only be called for the lemmas (no problem
   * clauses, no conflict clauses)
   * @param clauseId the SAT id of the clause
   * @return true if the clause can be erased
   */
  bool canErase(int clauseId) const;

  /**
   * This method is called by the SAT solver every time is starts using a literal.
   */
  void usingLiteral(const SatLiteral& l);

  /**
   * This method is called by the SAT solver every time it stops an occurance of
   * a literal.
   * @return true if this this release was the last occurance of the literal,
   *         i.e. the reference count went to 0
   */
  bool releasingLiteral(const SatLiteral& lit);

  /**
   * This method is called by the SAT solver every time it erases a clause.
   */
  void releasingClause(int clauseId);

  // TODO: Remove these methods
  const NodeToLiteralMap& getTranslationCache() const;
  const LiteralToNodeMap& getNodeCache() const;

}; /* class CnfStream */

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
   * @param lemma is this a lemma that is erasable
   * @param negated true if negated
   */
  void convertAndAssert(TNode node, bool lemma, bool negated = false);

  /**
   * Constructs the stream to use the given sat solver.
   * @param satSolver the sat solver to use
   */
  TseitinCnfStream(SatInputInterface* satSolver);

private:

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
  SatLiteral handleAtom(TNode node);
  SatLiteral handleNot(TNode node);
  SatLiteral handleXor(TNode node);
  SatLiteral handleImplies(TNode node);
  SatLiteral handleIff(TNode node);
  SatLiteral handleIte(TNode node);
  SatLiteral handleAnd(TNode node);
  SatLiteral handleOr(TNode node);

  void convertAndAssertAnd(TNode node, bool lemma, bool negated);
  void convertAndAssertOr(TNode node, bool lemma, bool negated);
  void convertAndAssertXor(TNode node, bool lemma, bool negated);
  void convertAndAssertIff(TNode node, bool lemma, bool negated);
  void convertAndAssertImplies(TNode node, bool lemma, bool negated);
  void convertAndAssertIte(TNode node, bool lemma, bool negated);

  /**
   * Transforms the node into CNF recursively.
   * @param node the formula to transform
   * @param negated wheather the literal is negated
   * @return the literal representing the root of the formula
   */
  SatLiteral toCNF(TNode node, bool negated = false);

}; /* class TseitinCnfStream */

}/* prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CNF_STREAM_H */

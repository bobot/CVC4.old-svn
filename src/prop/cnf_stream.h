/*********************                                                        */
/** cnf_stream.h
 ** Original author: taking
 ** Major contributors: dejan
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** This class takes a sequence of formulas.
 ** It outputs a stream of clauses that is propositional
 ** equisatisfiable with the conjunction of the formulas.
 ** This stream is maintained in an online fashion.
 **
 ** Unlike other parts of the system it is aware of the PropEngine's
 ** internals such as the representation and translation of 
 **/

#ifndef __CVC4__CNF_STREAM_H
#define __CVC4__CNF_STREAM_H

#include "expr/node.h"
#include "prop/sat.h"

#include <ext/hash_map>

namespace __gnu_cxx {
template<>
  struct hash<CVC4::Node> {
    size_t operator()(const CVC4::Node& node) const {
      return (size_t)node.hash();
    }
  };
} /* __gnu_cxx namespace */

namespace CVC4 {
namespace prop {

class PropEngine;

/**
 * This class is responsible for the translation to CNF. The main requirements
 * are the following
 * <li> When notified of a deletion of a removable clause, make a note of it,
 *      so that we can rebuild the CNF
 *
 * @author Tim King <taking@cs.nyu.edu>
 */
class CnfStream {

protected:

  /** The SAT solver we will be using */
  SatSolver *d_satSolver;

  /**
   * Asserts the given clause to the sat solver.
   * @param clause the clause to assert
   */
  void assertClause(SatClause& clause, bool removable = false);

  /**
   * Asserts the unit clause to the sat solver.
   * @param a the unit literal of the clause
   */
  void assertClause(SatLiteral a, bool removable = false);

  /**
   * Asserts the binary clause to the sat solver.
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   */
  void assertClause(SatLiteral a, SatLiteral b, bool removable = false);

  /**
   * Asserts the ternary clause to the sat solver.
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   * @param c the thirs literal in the clause
   */
  void assertClause(SatLiteral a, SatLiteral b, SatLiteral c, bool removable = false);

public:

  /**
   * Constructs a CnfStream that sends constructs an equi-satisfiable set of clauses
   * and sends them to the given sat solver.
   * @param satSolver the sat solver to use
   */
  CnfStream(SatSolver* satSolver);

  /**
   * Converts and asserts a formula.
   * @param node node to convert and assert
   * @param whether the sat solver can choose to remove this clause
   */
  virtual void convertAndAssert(const Node& node, bool removable = false) = 0;

}; /* class CnfStream */

/**
 * TseitinCnfStream is based on the following recursive algorithm
 * http://people.inf.ethz.ch/daniekro/classes/251-0247-00/f2007/readings/Tseitin70.pdf
 * The general gist of the algorithm is to introduce a new literal that 
 * will be equivalent to each subexpression in the constructed equisatisfiable
 * formula then substitute the new literal for the formula, and to do this
 * recursively.
 * 
 * This implementation does this in a single recursive pass.
 */
class TseitinCnfStream : public CnfStream {

public:

  /**
   * Convert a given formula to CNF and assert it to the SAT solver.
   * @param node the formula to assert
   */
  void convertAndAssert(const Node& node, bool removable);

  /**
   * Constructs the stream to use the given sat solver.
   * @param satSolver the sat solver to use
   */
  TseitinCnfStream(SatSolver* satSolver);

private:

  /**
   * Acquires a new variable from the SAT solver to represent the node and
   * inserts the necessary data it into the mapping tables.
   * @param node a formula
   * @return the literal corresponding to the formula
   */
  SatLiteral newLiteral(const Node& node);

/**
   * Returns true if the node has been cashed in the translation cache.
   * @param node the node
   * @return true if the node has been cached
   */
  bool isCached(const Node& node) const;

  /**
   * Returns the cashed literal corresponding to the given node.
   * @param node the node to lookup
   * @return returns the corresponding literal
   */
  SatLiteral lookupInCache(const Node& n) const;

  /**
   * Caches the pair of the node and the literal corresponding to the
   * translation.
   * @param node node
   * @param lit
   */
  void cacheTranslation(const Node& node, SatLiteral lit);

  /** The translation data we need to recover the translation */
  struct NodeTranslationData {

    /** The parts of the translation that got erased */
    std::vector<int> d_missing;
    /** The clauses that represent this node */
    std::vector<SatClause> d_clauses;
    /** The literal that represents this node */
    SatLiteral d_literal;

    void assertClause(SatClause& clause);
    void assertClause(SatLiteral a);
    void assertClause(SatLiteral a, SatLiteral b);
    void assertClause(SatLiteral a, SatLiteral b, SatLiteral c);

    operator bool() const { return d_clauses.size() != 0; }
  };

  /** Cache of what literal have been registered to a node. */
  __gnu_cxx::hash_map<Node, NodeTranslationData> d_translationCache;

  SatLiteral handleAtom(const Node& node);
  SatLiteral handleNot(const Node& node);
  SatLiteral handleXor(const Node& node);
  SatLiteral handleImplies(const Node& node);
  SatLiteral handleIff(const Node& node);
  SatLiteral handleIte(const Node& node);
  SatLiteral handleAnd(const Node& node);
  SatLiteral handleOr(const Node& node);

  /**
   * Transforms the node into CNF recursively.
   * @param node the formula to transform
   * @return the literal representing the root of the formula
   */
  SatLiteral toCNF(const Node& node);

}; /* class TseitinCnfStream */

}/* prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CNF_STREAM_H */

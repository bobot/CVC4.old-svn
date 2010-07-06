/*********************                                                        */
/*! \file cnf_stream.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: dejan
 ** Minor contributors (to current version): mdeters, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **
 ** A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **/

#include "sat.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "expr/node.h"
#include "util/Assert.h"
#include "util/output.h"

#include <queue>

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace prop {

#define PRINT_MAP(out, type, map)                            \
{                                                            \
  out << "Map: " << #map << endl;                            \
  type::const_iterator it = map.begin();                     \
  type::const_iterator it_end = map.end();                   \
  for (; it != it_end; ++ it) {                              \
    out << it->first << " -> " << it->second << endl;        \
  }                                                          \
}                                                            \

CnfStream::~CnfStream() {
#ifdef CVC4_TRACING
#ifdef PRINT_MAPS
  if (false) {
    PRINT_MAP(cerr, NodeToLiteralMap, d_nodeToLiteralMap);
    PRINT_MAP(cerr, LiteralToNodeMap, d_literalToNodeMap);
    PRINT_MAP(cerr, ClauseToNodeMap,  d_clauseToNodeMap);
    PRINT_MAP(cerr, NodeRefCountMap,  d_nodeRefCountLiterals);
    PRINT_MAP(cerr, NodeRefCountMap,  d_nodeRefCountClauses);
  }
#endif
#endif
}

void CnfStream::incLiteralRefCount(TNode node) {
  Assert(!node.isNull());
  Assert(!(node.getKind() == NOT));
  // Decrease and return the reference count
  ++ d_nodeRefCountLiterals[node];
}

unsigned CnfStream::decLiteralRefCount(TNode node) {
  Assert(!node.isNull());
  Assert(!(node.getKind() == NOT));
  // Decrease and return the reference count
  return -- d_nodeRefCountLiterals[node];
}

void CnfStream::releaseNode(Node node) {

  Debug("cnf") << "Releasing node " << node << endl;
  Assert(!(node.getKind() == NOT));
  Assert(getTotalRefCount(node) == 0);

  // Release the node from the theories
  d_satSolver->theoryUnPreRegisterAtom(node);

  // d_clauseToNodeMap should have been erased while erasing the clauses

  // Erase from the literal maps if the node has an associated literal
  if (isCached(node)) {
    SatLiteral l = getLiteral(node);
    d_literalToNodeMap.erase(l);
    d_literalToNodeMap.erase(~l);
  }

  // Erase the nodes maps
  d_nodeToLiteralMap.erase(node);
  d_nodeToLiteralMapRegenerateClause.erase(node);
  d_nodeRefCountLiterals.erase(node);
  d_nodeRefCountClauses.erase(node);
  d_nodesWithPureClauseSet.erase(node);
  d_nodesWithPureClauseSetRegenerateClause.erase(node);

  // Erase the negated node maps
  Node negatedNode = getNegation(node);
  d_nodeToLiteralMap.erase(negatedNode);
  d_nodeToLiteralMapRegenerateClause.erase(negatedNode);
  d_nodesWithPureClauseSet.erase(negatedNode);
  // We don't erase this guy as they the negative and positive are different translations
  // d_nodesWithPureClauseSetRegenerateClause.erase(negatedNode);
  d_nodeRefCountLiterals.erase(negatedNode);
  d_nodeRefCountClauses.erase(negatedNode);
}

bool CnfStream::releasingLiteral(const SatLiteral& l) {

  Debug("cnf") << "Releasing literal " << l << endl;

  // Get the node of this literal -- has to be a node as this might be the last reference
  Node node = getPositive(getNode(l));

  // Decrease the node's reference count
  unsigned refCount = decLiteralRefCount(node);

  // If the refCount goes to zero, we can erase both the positive and the
  // negative literal from the maps
  if (refCount == 0 && getClauseRefCount(node) == 0) {
    if (isCached(node)) {
      SatLiteral lit = getLiteral(node);
      SatLiteral assigned_value;
      if (d_satSolver->isInUse(lit, assigned_value)) {
        usingLiteral(assigned_value);
        d_satSolver->eraseWhenUnassigned(assigned_value);
        return false;
      } else {
        releaseNode(node);
        return true;
      }
    } else {
      releaseNode(node);
      return true;
    }
  }
  // There is still some stuff left
  return false;
}

void CnfStream::releasingClause(int clauseId) {
  Debug("cnf") << "Releasing clause with id " << clauseId << endl;

  // Get the node -- has to be a node, as this might be the last reference
  ClauseToNodeMapEntry entry = d_clauseToNodeMap[clauseId];
  Node node = getPositive(entry.node);

  // Depending on the type of the clause mark the node to regenerate clauses
  // if asserted again
  if (!entry.isPure) {
    d_nodeToLiteralMapRegenerateClause.insert(node);
    d_nodeToLiteralMapRegenerateClause.insert(getNegation(node));
  } else {
    d_nodesWithPureClauseSetRegenerateClause.insert(entry.node);
  }

  // Erase the clause from the clause map
  d_clauseToNodeMap.erase(clauseId);

  // Decrease the reference count of the node
  unsigned refCount = decClauseRefCount(node);

  // If there is no one pointing this node, we can/should erase it
  if (refCount == 0 && getLiteralRefCount(node) == 0) {
    if (isCached(node)) {
      SatLiteral lit = getLiteral(node);
      SatLiteral assigned_value;
      if (d_satSolver->isInUse(lit, assigned_value)) {
        usingLiteral(assigned_value);
        d_satSolver->eraseWhenUnassigned(assigned_value);
      } else {
        releaseNode(node);
      }
    } else {
      releaseNode(node);
    }
  }
}

void CnfStream::usingLiteral(const SatLiteral& l) {
  Debug("cnf") << "Using literal " << l << endl;
  incLiteralRefCount(getPositive(getNode(l)));
}

unsigned CnfStream::getTotalRefCount(TNode node) const {
  Assert(!node.isNull());
  Assert(!(node.getKind() == NOT));
  return getLiteralRefCount(node) + getClauseRefCount(node);
}

unsigned CnfStream::getLiteralRefCount(TNode node) const {
  Assert(!node.isNull());
  Assert(!(node.getKind() == NOT));
  NodeRefCountMap::const_iterator nodeFind = d_nodeRefCountLiterals.find(node);
  if (nodeFind != d_nodeRefCountLiterals.end()) {
    return (nodeFind->second);
  } else {
    return 0;
  }
}

unsigned CnfStream::getClauseRefCount(TNode node) const {
  Assert(!node.isNull());
  Assert(!(node.getKind() == NOT));
  NodeRefCountMap::const_iterator nodeFind = d_nodeRefCountClauses.find(node);
  if (nodeFind != d_nodeRefCountClauses.end()) {
    return (nodeFind->second);
  } else {
    return 0;
  }
}

TNode CnfStream::getGeneratingNode(int clauseId) const {
  ClauseToNodeMap::const_iterator nodeFind = d_clauseToNodeMap.find(clauseId);
  Assert(nodeFind != d_clauseToNodeMap.end());
  return nodeFind->second.node;
}

bool CnfStream::canErase(int clauseId) const {
  // Think hard dejan :)
  Node postiveNode = getPositive(getGeneratingNode(clauseId));
  return getLiteralRefCount(postiveNode) <= getClauseRefCount(postiveNode);
}

CnfStream::CnfStream(SatInputInterface *satSolver) :
  d_satSolver(satSolver) {
}

TseitinCnfStream::TseitinCnfStream(SatInputInterface* satSolver) :
  CnfStream(satSolver) {
}

void CnfStream::assertClause(TNode node, SatClause& c, bool isPure) {
  Debug("cnf") << "Inserting into stream " << c << endl;
  int clauseId = d_satSolver->addClause(c, d_assertingLemma);
  if (clauseId > 0) {
    Debug("cnf") << "Clause inserted with id " << clauseId << endl;
    Node positive = getPositive(node);
    d_clauseToNodeMap[clauseId] = ClauseToNodeMapEntry(positive, isPure);
    incClauseRefCount(positive);
  }
}

void CnfStream::assertClause(TNode node, SatLiteral a, bool isPure) {
  SatClause clause(1);
  clause[0] = a;
  assertClause(node, clause, isPure);
}

void CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b, bool isPure) {
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  assertClause(node, clause, isPure);
}

void CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b, SatLiteral c, bool isPure) {
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  assertClause(node, clause, isPure);
}

bool CnfStream::isCached(TNode n) const {
  return d_nodeToLiteralMap.find(n) != d_nodeToLiteralMap.end();
}

bool CnfStream::shouldRegenerateClauses(TNode node, bool pure) const {
  if (!pure) {
    return d_nodeToLiteralMapRegenerateClause.find(node) != d_nodeToLiteralMapRegenerateClause.end();
  } else {
    return d_nodesWithPureClauseSetRegenerateClause.find(node) != d_nodesWithPureClauseSetRegenerateClause.end();
  }
}

void CnfStream::markAsGenerated(TNode node, bool pure) {
  if (!pure) {
    d_nodeToLiteralMapRegenerateClause.erase(node);
    d_nodeToLiteralMapRegenerateClause.erase(getNegation(node));
  } else {
    d_nodesWithPureClauseSetRegenerateClause.erase(node);
  }
}

SatLiteral CnfStream::lookupInCache(TNode n) const {
  Assert(isCached(n), "Node is not in CNF translation cache");
  return d_nodeToLiteralMap.find(n)->second;
}

void CnfStream::cacheTranslation(TNode node, SatLiteral lit) {
  Debug("cnf") << "caching translation " << node << " to " << lit << endl;
  // We always cash both the node and the negation at the same time
  d_nodeToLiteralMap[node] = lit;
  d_nodeToLiteralMap[getNegation(node)] = ~lit;
}

bool CnfStream::cachePureTranslation(TNode node, bool negated) {
  Debug("cnf") << "caching translation " << node << " to pure clauses" << endl;
  // For the top level we only cache the node itself, not the negated one
  if (negated) {
    Node negatedNode = getNegation(node);
    bool added = d_nodesWithPureClauseSet.insert(negatedNode).second;
    if (!added) return shouldRegenerateClauses(negatedNode, true);
  } else {
    bool added = d_nodesWithPureClauseSet.insert(node).second;
    if (!added) return shouldRegenerateClauses(node, true);
  }
  return true;
}

SatLiteral CnfStream::newLiteral(TNode node, bool theoryLiteral) {
  Debug("cnf") << "CnfStream::newLiteral(" << node << ", " << (theoryLiteral ? "true)" : "false)") << endl;
  SatLiteral lit = SatLiteral(d_satSolver->newVar(theoryLiteral));
  cacheTranslation(node, lit);
  d_literalToNodeMap[lit] = node;
  d_literalToNodeMap[~lit] = getNegation(node);
  Debug("cnf") << "CnfStream::newLiteral(" << node << ", " << (theoryLiteral ? "true)" : "false) => ") << lit << endl;
  return lit;
}

SatLiteral CnfStream::newLiteralOrCached(TNode node, bool theoryLiteral) {
  Debug("cnf") << "CnfStream::newLiteralOrCached(" << node << ", " << (theoryLiteral ? "true)" : "false)") << endl;
  Assert(!isCached(node) || shouldRegenerateClauses(node, false));
  if (isCached(node)) return lookupInCache(node);
  else return newLiteral(node, theoryLiteral);
}

Node CnfStream::getNode(const SatLiteral& l) const {
  // If the node is not in the literal map, the negation has to
  LiteralToNodeMap::const_iterator findNode = d_literalToNodeMap.find(l);
  if (findNode == d_literalToNodeMap.end()) {
    Assert(d_literalToNodeMap.find(~l) != d_literalToNodeMap.end());
    Node negatedNode = d_literalToNodeMap.find(~l)->second;
    return getNegation(negatedNode);
  } else {
    return findNode->second;
  }
}

SatLiteral CnfStream::getLiteral(TNode node) {
  Debug("cnf") << "CnfStream::getLiteral(" << node << ")" << std::endl;
  NodeToLiteralMap::iterator find = d_nodeToLiteralMap.find(node);
  Assert(find != d_nodeToLiteralMap.end(), "Literal not in the CNF Cache");
  SatLiteral literal = find->second;
  Debug("cnf") << "CnfStream::getLiteral(" << node << ") => " << literal << std::endl;
  return literal;
}

const CnfStream::LiteralToNodeMap& CnfStream::getNodeCache() const {
  return d_literalToNodeMap;
}

const CnfStream::NodeToLiteralMap& CnfStream::getTranslationCache() const {
  return d_nodeToLiteralMap;
}

SatLiteral TseitinCnfStream::handleAtom(TNode node) {
  Assert(!isCached(node) || shouldRegenerateClauses(node, false), "atom already mapped!");

  Debug("cnf") << "handleAtom(" << node << ")" << endl;

  bool theoryLiteral = node.getKind() != kind::VARIABLE;
  SatLiteral lit = newLiteralOrCached(node, theoryLiteral);

  if(node.getKind() == kind::CONST_BOOLEAN) {
    if(node.getConst<bool>()) {
      assertClause(node, lit, false);
    } else {
      assertClause(node, ~lit, false);
    }
  }

  return lit;
}

SatLiteral TseitinCnfStream::handleXor(TNode xorNode) {
  Assert(!isCached(xorNode) || shouldRegenerateClauses(xorNode, false), "Atom already mapped!");
  Assert(xorNode.getKind() == XOR, "Expecting an XOR expression!");
  Assert(xorNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  SatLiteral a = toCNF(xorNode[0]);
  SatLiteral b = toCNF(xorNode[1]);

  SatLiteral xorLit = newLiteralOrCached(xorNode);

  assertClause(xorNode, a, b, ~xorLit, false);
  assertClause(xorNode, ~a, ~b, ~xorLit, false);
  assertClause(xorNode, a, ~b, xorLit, false);
  assertClause(xorNode, ~a, b, xorLit, false);

  return xorLit;
}

SatLiteral TseitinCnfStream::handleOr(TNode orNode) {
  Assert(!isCached(orNode) || shouldRegenerateClauses(orNode, false), "Atom already mapped!");
  Assert(orNode.getKind() == OR, "Expecting an OR expression!");
  Assert(orNode.getNumChildren() > 1, "Expecting more then 1 child!");

  // Number of children
  unsigned n_children = orNode.getNumChildren();

  // Transform all the children first
  TNode::const_iterator node_it = orNode.begin();
  TNode::const_iterator node_it_end = orNode.end();
  SatClause clause(n_children + 1);
  for(int i = 0; node_it != node_it_end; ++node_it, ++i) {
    clause[i] = toCNF(*node_it);
  }

  // Get the literal for this node
  SatLiteral orLit = newLiteralOrCached(orNode);

  // lit <- (a_1 | a_2 | a_3 | ... | a_n)
  // lit | ~(a_1 | a_2 | a_3 | ... | a_n)
  // (lit | ~a_1) & (lit | ~a_2) & (lit & ~a_3) & ... & (lit & ~a_n)
  for(unsigned i = 0; i < n_children; ++i) {
    assertClause(orNode, orLit, ~clause[i], false);
  }

  // lit -> (a_1 | a_2 | a_3 | ... | a_n)
  // ~lit | a_1 | a_2 | a_3 | ... | a_n
  clause[n_children] = ~orLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(orNode, clause, false);

  // Return the literal
  return orLit;
}

SatLiteral TseitinCnfStream::handleAnd(TNode andNode) {
  Assert(!isCached(andNode)  || shouldRegenerateClauses(andNode, false), "Atom already mapped!");
  Assert(andNode.getKind() == AND, "Expecting an AND expression!");
  Assert(andNode.getNumChildren() > 1, "Expecting more than 1 child!");

  // Number of children
  unsigned n_children = andNode.getNumChildren();

  // Transform all the children first (remembering the negation)
  TNode::const_iterator node_it = andNode.begin();
  TNode::const_iterator node_it_end = andNode.end();
  SatClause clause(n_children + 1);
  for(int i = 0; node_it != node_it_end; ++node_it, ++i) {
    clause[i] = ~toCNF(*node_it);
  }

  // Get the literal for this node
  SatLiteral andLit = newLiteralOrCached(andNode);

  // lit -> (a_1 & a_2 & a_3 & ... & a_n)
  // ~lit | (a_1 & a_2 & a_3 & ... & a_n)
  // (~lit | a_1) & (~lit | a_2) & ... & (~lit | a_n)
  for(unsigned i = 0; i < n_children; ++i) {
    assertClause(andNode, ~andLit, ~clause[i], false);
  }

  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[n_children] = andLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(andNode, clause, false);
  return andLit;
}

SatLiteral TseitinCnfStream::handleImplies(TNode impliesNode) {
  Assert(!isCached(impliesNode) || shouldRegenerateClauses(impliesNode, false), "Atom already mapped!");
  Assert(impliesNode.getKind() == IMPLIES, "Expecting an IMPLIES expression!");
  Assert(impliesNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  // Convert the children to cnf
  SatLiteral a = toCNF(impliesNode[0]);
  SatLiteral b = toCNF(impliesNode[1]);

  SatLiteral impliesLit = newLiteralOrCached(impliesNode);

  // lit -> (a->b)
  // ~lit | ~ a | b
  assertClause(impliesNode, ~impliesLit, ~a, b, false);

  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  assertClause(impliesNode, a, impliesLit, false);
  assertClause(impliesNode, ~b, impliesLit, false);

  return impliesLit;
}


SatLiteral TseitinCnfStream::handleIff(TNode iffNode) {
  Assert(!isCached(iffNode) || shouldRegenerateClauses(iffNode, false), "Atom already mapped!");
  Assert(iffNode.getKind() == IFF, "Expecting an IFF expression!");
  Assert(iffNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  // Convert the children to CNF
  SatLiteral a = toCNF(iffNode[0]);
  SatLiteral b = toCNF(iffNode[1]);

  // Get the now literal
  SatLiteral iffLit = newLiteralOrCached(iffNode);

  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  assertClause(iffNode, ~a, b, ~iffLit, false);
  assertClause(iffNode, a, ~b, ~iffLit, false);

  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  assertClause(iffNode, ~a, ~b, iffLit, false);
  assertClause(iffNode, a, b, iffLit, false);

  return iffLit;
}


SatLiteral TseitinCnfStream::handleNot(TNode notNode) {
  Assert(!isCached(notNode) || shouldRegenerateClauses(notNode, false), "Atom already mapped!");
  Assert(notNode.getKind() == NOT, "Expecting a NOT expression!");
  Assert(notNode.getNumChildren() == 1, "Expecting exactly 1 child!");

  SatLiteral notLit = ~toCNF(notNode[0]);

  // Since we don't introduce new variables, we need to cache the translation
  cacheTranslation(notNode, notLit);

  return notLit;
}

SatLiteral TseitinCnfStream::handleIte(TNode iteNode) {
  Assert(iteNode.getKind() == ITE);
  Assert(iteNode.getNumChildren() == 3);

  Debug("cnf") << "handlIte(" << iteNode[0] << " " << iteNode[1] << " " << iteNode[2] << ")" << endl;

  SatLiteral condLit = toCNF(iteNode[0]);
  SatLiteral thenLit = toCNF(iteNode[1]);
  SatLiteral elseLit = toCNF(iteNode[2]);

  SatLiteral iteLit = newLiteralOrCached(iteNode);

  // If ITE is true then one of the branches is true and the condition
  // implies which one
  // lit -> (ite b t e)
  // lit -> (t | e) & (b -> t) & (!b -> e)
  // lit -> (t | e) & (!b | t) & (b | e)
  // (!lit | t | e) & (!lit | !b | t) & (!lit | b | e)
  assertClause(iteNode, ~iteLit, thenLit, elseLit, false);
  assertClause(iteNode, ~iteLit, ~condLit, thenLit, false);
  assertClause(iteNode, ~iteLit, condLit, elseLit, false);

  // If ITE is false then one of the branches is false and the condition
  // implies which one
  // !lit -> !(ite b t e)
  // !lit -> (!t | !e) & (b -> !t) & (!b -> !e)
  // !lit -> (!t | !e) & (!b | !t) & (b | !e)
  // (lit | !t | !e) & (lit | !b | !t) & (lit | b | !e)
  assertClause(iteNode, iteLit, ~thenLit, ~elseLit, false);
  assertClause(iteNode, iteLit, ~condLit, ~thenLit, false);
  assertClause(iteNode, iteLit, condLit, ~elseLit, false);

  return iteLit;
}


SatLiteral TseitinCnfStream::toCNF(TNode node, bool negated) {
  Debug("cnf") << "toCNF(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  SatLiteral nodeLit;

  // If the non-negated node has already been translated, get the translation
  if(isCached(node)) {
    nodeLit = lookupInCache(node);
    if (negated) {
      if (!shouldRegenerateClauses(getNegation(node), false)) return ~nodeLit;
    } else {
      if (!shouldRegenerateClauses(node, false)) return nodeLit;
    }
  }

  // Handle each Boolean operator case
  switch(node.getKind()) {
  case NOT:
    nodeLit = handleNot(node);
    break;
  case XOR:
    nodeLit = handleXor(node);
    break;
  case ITE:
    nodeLit = handleIte(node);
    break;
  case IFF:
    nodeLit = handleIff(node);
    break;
  case IMPLIES:
    nodeLit = handleImplies(node);
    break;
  case OR:
    nodeLit = handleOr(node);
    break;
  case AND:
    nodeLit = handleAnd(node);
    break;
  default:
    {
      //TODO make sure this does not contain any boolean substructure
      nodeLit = handleAtom(node);
    }
  }

  // We've generated the clauses so we can mark it as regenerated now
  markAsGenerated(getPositive(node), false);

  // Return the appropriate (negated) literal
  if (!negated) return nodeLit;
  else return ~nodeLit;
}

void TseitinCnfStream::convertAndAssertAnd(TNode node, bool lemma, bool negated) {
  Assert(node.getKind() == AND);
  if (!negated) {
    // If the node is a conjunction, we handle each conjunct separately
    for(TNode::const_iterator conjunct = node.begin(), node_end = node.end();
        conjunct != node_end; ++conjunct ) {
      convertAndAssert(*conjunct, lemma, false);
    }
  } else {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCNF(*disjunct, true);
    }
    Assert(disjunct == node.end());
    assertClause(node, clause, true);
  }
}

void TseitinCnfStream::convertAndAssertOr(TNode node, bool lemma, bool negated) {
  Assert(node.getKind() == OR);
  if (!negated) {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCNF(*disjunct, false);
    }
    Assert(disjunct == node.end());
    assertClause(node, clause, true);
  } else {
    // If the node is a conjunction, we handle each conjunct separately
    for(TNode::const_iterator conjunct = node.begin(), node_end = node.end();
        conjunct != node_end; ++conjunct ) {
      convertAndAssert(*conjunct, lemma, true);
    }
  }
}

void TseitinCnfStream::convertAndAssertXor(TNode node, bool lemma, bool negated) {
  if (!negated) {
    // p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    assertClause(node, clause1, true);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node, clause2, true);
  } else {
    // !(p XOR q) is the same as p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    assertClause(node, clause1, true);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node, clause2, true);
  }
}

void TseitinCnfStream::convertAndAssertIff(TNode node, bool lemma, bool negated) {
  if (!negated) {
    // p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    assertClause(node, clause1, true);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node, clause2, true);
  } else {
    // !(p <=> q) is the same as p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    assertClause(node, clause1, true);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node, clause2, true);
  }
}

void TseitinCnfStream::convertAndAssertImplies(TNode node, bool lemma, bool negated) {
  if (!negated) {
    // p => q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clause ~p || q
    SatClause clause(2);
    clause[0] = ~p;
    clause[1] = q;
    assertClause(node, clause, true);
  } else {// Construct the
    // !(p => q) is the same as (p && ~q)
    convertAndAssert(node[0], lemma, false);
    convertAndAssert(node[1], lemma, true);
  }
}

void TseitinCnfStream::convertAndAssertIte(TNode node, bool lemma, bool negated) {
  // ITE(p, q, r)
  SatLiteral p = toCNF(node[0], false);
  SatLiteral q = toCNF(node[1], negated);
  SatLiteral r = toCNF(node[2], negated);
  // Construct the clauses:
  // (p => q) and (!p => r) and (!q => !p) and (!r => p)
  SatClause clause1(2);
  clause1[0] = ~p;
  clause1[1] = q;
  assertClause(node, clause1, true);
  SatClause clause2(2);
  clause2[0] = p;
  clause2[1] = r;
  assertClause(node, clause2, true);
  SatClause clause3(2);
  clause3[0] = q;
  clause3[1] = ~p;
  assertClause(node, clause3, true);
  SatClause clause4(2);
  clause4[0] = r;
  clause4[1] = p;
  assertClause(node, clause4, true);
}

// At the top level we must ensure that all clauses that are asserted are
// not unit, except for the direct assertions. This allows us to remove the
// clauses later when they are not needed anymore (lemmas for example).
void TseitinCnfStream::convertAndAssert(TNode node, bool lemma, bool negated) {
  Debug("cnf") << "convertAndAssert(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;
  d_assertingLemma = lemma;

  if (node.getKind() != NOT) {
    // We cache and check all translations but NOT expressions, which are
    // special. If we would cache the not, cache(!a, false), next call would be
    // cache(a, true) which would return true, and we wouldn't add anything.
    bool shouldGenerate = cachePureTranslation(node, negated);
    if (!shouldGenerate) return;
  }

  switch(node.getKind()) {
  case AND:
    convertAndAssertAnd(node, lemma, negated);
    break;
  case OR:
    convertAndAssertOr(node, lemma, negated);
    break;
  case IFF:
    convertAndAssertIff(node, lemma, negated);
    break;
  case XOR:
    convertAndAssertXor(node, lemma, negated);
    break;
  case IMPLIES:
    convertAndAssertImplies(node, lemma, negated);
    break;
  case ITE:
    convertAndAssertIte(node, lemma, negated);
    break;
  case NOT:
    convertAndAssert(node[0], lemma, !negated);
    break;
  default:
    // Atoms
    assertClause(node, toCNF(node, negated), true);
    break;
  }

  if (node.getKind() != NOT) {
    Node positiveNode = getPositive(node);
    if (negated) markAsGenerated(getNegation(positiveNode), true);
    else markAsGenerated(positiveNode, true);
  }
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */

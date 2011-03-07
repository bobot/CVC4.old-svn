/*********************                                                        */
/*! \file sat.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters, taking
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/sat.h"
#include "context/context.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace prop {

void SatSolver::theoryCheck(theory::Theory::Effort effort, SatClause& conflict) {
  // Try theory propagation
  bool ok = d_theoryEngine->check(effort);
  // If in conflict construct the conflict clause
  if (!ok) {
    // We have a conflict, get it
    Node conflictNode = d_theoryEngine->getConflict();
    Debug("prop") << "SatSolver::theoryCheck() => conflict: " << conflictNode << std::endl;
    // Go through the literals and construct the conflict clause
    Node::const_iterator literal_it = conflictNode.begin();
    Node::const_iterator literal_end = conflictNode.end();
    while (literal_it != literal_end) {
      // Get the literal corresponding to the node
      SatLiteral l = d_cnfStream->getLiteral(*literal_it);
      // Add the negation to the conflict clause and continue
      conflict.push(~l);
      literal_it ++;
    }
  }
}

void SatSolver::theoryPropagate(std::vector<SatLiteral>& output) {
  // Propagate
  d_theoryEngine->propagate();
  // Get the propagated literals
  const std::vector<TNode>& outputNodes = d_theoryEngine->getPropagatedLiterals();
  // If any literals, make a clause
  const unsigned i_end = outputNodes.size();
  for (unsigned i = 0; i < i_end; ++ i) {
    Debug("prop-explain") << "theoryPropagate() => " << outputNodes[i].toString() << std::endl;
    SatLiteral l = d_cnfStream->getLiteral(outputNodes[i]);
    if(d_minisat->value(l) != l_True) {
      Assert(d_minisat->value(l) == l_Undef, "tried to theory-propagate something already defined");
      output.push_back(l);
    }
  }
}

void SatSolver::explainPropagation(SatLiteral l, SatClause& explanation) {
  TNode lNode = d_cnfStream->getNode(l);
  Debug("prop-explain") << "explainPropagation(" << lNode << ")" << std::endl;
  Node theoryExplanation = d_theoryEngine->getExplanation(lNode);
  Debug("prop-explain") << "explainPropagation() => " <<  theoryExplanation << std::endl;
  if (theoryExplanation.getKind() == kind::AND) {
    Node::const_iterator it = theoryExplanation.begin();
    Node::const_iterator it_end = theoryExplanation.end();
    explanation.push(l);
    for (; it != it_end; ++ it) {
      explanation.push(~d_cnfStream->getLiteral(*it));
    }
  } else {
    explanation.push(l);
    explanation.push(~d_cnfStream->getLiteral(theoryExplanation));
  }
}

void SatSolver::clearPropagatedLiterals() {
  d_theoryEngine->clearPropagatedLiterals();
}

void SatSolver::enqueueTheoryLiteral(const SatLiteral& l) {
  Node literalNode = d_cnfStream->getNode(l);
  Debug("prop") << "enqueueing theory literal " << l << " " << literalNode << std::endl;
  Assert(!literalNode.isNull());
  d_theoryEngine->assertFact(literalNode);
}

void SatSolver::setCnfStream(CnfStream* cnfStream) {
  d_cnfStream = cnfStream;
}

void SatSolver::removeClausesAboveLevel(int level) {
  d_cnfStream->removeClausesAboveLevel(level);
}

TNode SatSolver::getNode(SatLiteral lit) {
  return d_cnfStream->getNode(lit);
}

void SatSolver::notifyRestart() {
  d_theoryEngine->notifyRestart();
}

void SatSolver::notifyNewLemma(SatClause& lemma) {
  Assert(lemma.size() > 0);
  if(d_options->lemmaOutputChannel != NULL) {
    if(lemma.size() == 1) {
      d_options->lemmaOutputChannel->notifyNewLemma(d_cnfStream->getNode(lemma[0]).toExpr());
    } else {
      NodeBuilder<> b(kind::OR);
      for(unsigned i = 0, i_end = lemma.size(); i < i_end; ++i) {
        b << d_cnfStream->getNode(lemma[i]);
      }
      Node n = b;
      d_options->lemmaOutputChannel->notifyNewLemma(n.toExpr());
    }
  }
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */

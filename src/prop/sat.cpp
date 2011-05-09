/*********************                                                        */
/*! \file sat.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: dejan, mdeters, taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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
#include "expr/expr_stream.h"

namespace CVC4 {
namespace prop {

void SatSolver::theoryCheck(theory::Theory::Effort effort, SatClause& conflict) {
  Assert(conflict.size() == 0);
  // Try theory propagation
  bool ok = d_theoryEngine->check(effort);
  // If in conflict construct the conflict clause
  if (!ok) {
    // We have a conflict, get it
    Node conflictNode = d_theoryEngine->getConflict();
    Debug("prop") << "SatSolver::theoryCheck() => conflict: " << conflictNode << std::endl;
    if(conflictNode.getKind() == kind::AND) {
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
    } else { // unit conflict
      // Get the literal corresponding to the node
      SatLiteral l = d_cnfStream->getLiteral(conflictNode);
      // construct the unit conflict clause
      conflict.push(~l);
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

  static uint32_t lemmaCount = 0;

  if(Options::current()->lemmaInputChannel != NULL){
    while(Options::current()->lemmaInputChannel->hasNewLemma()) {
      Debug("shared") << "shared" << std::endl;
      Expr lemma = Options::current()->lemmaInputChannel->getNewLemma();
      Node asNode = lemma.getNode();

      if(not Debug.isOn("shared-dropall") and d_shared.find(asNode) == d_shared.end()){
        d_shared.insert(asNode);
        if(asNode.getKind() == kind::OR){
          ++lemmaCount;
          if(lemmaCount % 100 == 0){
            Debug("shared-terse") << "=) " << asNode << std::endl;
          }
          d_propEngine->assertLemma(d_theoryEngine->preprocess(asNode));
        }else{
          Debug("shared") << "=(" << asNode << std::endl;
        }
      }else{
        Debug("shared") <<"drop shared " << asNode << std::endl;
      }
    }
  }
}

void SatSolver::notifyNewLemma(SatClause& lemma) {
  Assert(lemma.size() > 0);
  if(Options::current()->lemmaOutputChannel != NULL) {
    if(lemma.size() == 1) {
      //Options::current()->lemmaOutputChannel->notifyNewLemma(d_cnfStream->getNode(lemma[0]).toExpr());
    } else {
      NodeBuilder<> b(kind::OR);
      for(unsigned i = 0, i_end = lemma.size(); i < i_end; ++i) {
        b << d_cnfStream->getNode(lemma[i]);
      }
      Node n = b;

      if(d_shared.find(n) == d_shared.end()){
        d_shared.insert(n);
        Options::current()->lemmaOutputChannel->notifyNewLemma(n.toExpr());
      }else{
        Debug("shared") <<"drop new " << n << std::endl;
      }
    }
  }
}

SatLiteral SatSolver::getNextReplayDecision() {
#ifdef CVC4_REPLAY
  if(Options::current()->replayStream != NULL) {
    Expr e = Options::current()->replayStream->nextExpr();
    if(!e.isNull()) { // we get null node when out of decisions to replay
      // convert & return
      return d_cnfStream->getLiteral(e);
    }
  }
#endif /* CVC4_REPLAY */
  return Minisat::lit_Undef;
}

void SatSolver::logDecision(SatLiteral lit) {
#ifdef CVC4_REPLAY
  if(Options::current()->replayLog != NULL) {
    Assert(lit != Minisat::lit_Undef, "logging an `undef' decision ?!");
    *Options::current()->replayLog << d_cnfStream->getNode(lit) << std::endl;
  }
#endif /* CVC4_REPLAY */
}


}/* CVC4::prop namespace */
}/* CVC4 namespace */

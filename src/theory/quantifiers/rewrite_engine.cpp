/*********************                                                        */
/*! \file rewrite_engine.cpp
 ** \verbatim
 ** Original author: ajreynolds
 ** Major contributors: bobot
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011
 ** The Analysis of Computer Systems Group (ACSys)
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

#include "theory/valuation.h"
#include "theory/quantifiers/rewrite_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

RewriteEngine::RewriteEngine( TheoryQuantifiers* th ) :
  d_th( th ){
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
}

Node RewriteEngine::getPattern(QuantifiersEngine* qe, Node r){
  /*    qe->getSubstitutedNode(getPattern(r),r);*/
  Assert(r.getKind () == kind::FORALL);
  switch(r[1].getKind()){
  case kind::REDUCTION_RULE:
  case kind::DEDUCTION_RULE:
  case kind::REWRITE_RULE:
    /** the rewritten term */
    /** Perhaps should give an atom and not a literal */
    return qe->getSubstitutedNode(r[1][1],r);
  default:
    Unhandled(r[1].getKind());
  }
}

std::vector<Node> RewriteEngine::getSubstitutedGuards
(Node r, std::vector< Node > vars, std::vector< Node > match  ){
  std::vector<Node> gs;
  Node guard = r[1][0];
  switch(guard.getKind()){
  case kind::AND:
    for(Node::iterator i = guard.begin(); i != guard.end(); ++i) {
      gs.push_back(*i);
    };
    break;
  default:
    gs.push_back(guard);
  };
  return gs;
}

Node RewriteEngine::getSubstitutedBody
(Node r, std::vector< Node > vars, std::vector< Node > match){
  std::vector<Node> gs;
  /** todo */
  Assert(r.getKind () == kind::FORALL);
  switch(r[1].getKind()){
  case kind::REWRITE_RULE:
    return (r[1][1].eqNode(r[1][2])).
      substitute(vars.begin(),vars.end(),match.begin(),match.end());
  case kind::REDUCTION_RULE:
  case kind::DEDUCTION_RULE:
    return r[1][2].
      substitute(vars.begin(),vars.end(),match.begin(),match.end());
  default:
    Unhandled(r[1].getKind());
    return r;
  }
}

Node RewriteEngine::getSubstitutedLemma
(Node r, std::vector< Node > vars, std::vector< Node > match){
  std::vector<Node> gs;
  Node lemma;
  Assert(r.getKind () == kind::FORALL);
  switch(r[1].getKind()){
  case kind::REWRITE_RULE:
    lemma = r[1][0].impNode(r[1][1].eqNode(r[1][2]));
    return lemma.
      substitute(vars.begin(),vars.end(),match.begin(),match.end());
  case kind::REDUCTION_RULE:
  case kind::DEDUCTION_RULE:
    lemma = r[1][1].impNode(r[1][2]);
    lemma = r[1][0].impNode(lemma);
    return lemma
      .substitute(vars.begin(),vars.end(),match.begin(),match.end());
  default:
    Unhandled(r[1].getKind());
    return r;
  }
}

void RewriteEngine::check( Theory::Effort e ){
  Debug("rewriterules") << "check: " << e << std::endl;
  QuantifiersEngine* qe = d_th->getQuantifiersEngine();
  Valuation val = d_th->getValuation();

  /** Test each rewrite rule */
  for(std::vector<Node>::const_iterator i = d_rules.begin();
      i != d_rules.end(); ++i) {
    Node r = *i;
    Debug("rewriterules") << "  rule: " << r << std::endl;
    /* Create the pattern */
    Node p = getPattern(qe,r);
    std::vector<Node> pattern; pattern.push_back(p);
    Debug("rewriterules") << "pattern creation:" << p << std::endl;
    Trigger* tr = new Trigger(qe,r,pattern, false);

    /** Test the possible matching one by one */
    while(tr->getNextMatch ()){
      InstMatch* im = tr->getCurrent();
      Debug("rewriterules") << "One matching found" << std::endl;

      /* Create the substitution */
      std::vector<Node> vars = qe->d_vars[r];
      std::vector<Node> subst;
      im->computeTermVec(qe, vars, subst);

      /* Test the guards */
      bool verified = true;
      std::vector<Node> gs = getSubstitutedGuards(r, vars, subst);
      for(std::vector<Node>::iterator g = gs.begin();
          g != gs.end(); ++g) {
        Node value = val.getValue(*g);
        Debug("rewriterules") << "Value of " << *g << " is "
                              << value << std::endl;
        if(value != d_true){
          verified=false;
          break;
        }
      };

      /* Add a lemmas if the guards are verified */
      if(verified){
        Debug("rewriterules") << "A rewrite rules is verified"
                              << std::endl;
        Node lemma = getSubstitutedLemma(r, vars, subst);
        d_th->getOutputChannel().lemma(lemma);
      }
    }
  }
}

void RewriteEngine::registerQuantifier( Node n ){
  Debug("rewriterules") << "registerQuantifier: " << n << std::endl;
  if( TheoryQuantifiers::isRewriteKind( n[1].getKind() ) ){
    if (d_th->getValuation().getDecisionLevel()>0)
      Unhandled(d_th->getValuation().getDecisionLevel());
    d_rules.push_back(n);
  };
}

void RewriteEngine::assertNode( Node n ){
  Debug("rewriterules") << "assertNode: " << n << std::endl;
}

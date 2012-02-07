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
    /* Todo */
    /*    qe->getSubstitutedNode(getPattern(r),r);*/
    Assert(r.getKind () == kind::FORALL);
    switch(r[1].getKind()){
    case kind::REWRITE_RULE:
        /** the rewritten term */
        return qe->getSubstitutedNode(r[1][1],r);
    default:
      Unhandled(r[1].getKind());
    }
}

std::vector<Node> RewriteEngine::getSubstitutedGuards
(Node r, std::vector< Node > vars, std::vector< Node > match  ){
    std::vector<Node> gs;
    switch(r[1].getKind()){
    case kind::REWRITE_RULE:
      switch(r[1][0].getKind()){
      case kind::AND:
        /* todo */
        Unhandled(r[1][0].getKind());
      default:
        gs.push_back(r[1][0]);
      };
      break;
    default:
      Unhandled(r[1].getKind());
    }
    return gs;
}

Node RewriteEngine::getSubstitutedBody
(Node r, std::vector< Node > vars, std::vector< Node > match){
    std::vector<Node> gs;
    /** todo */
    Assert(r.getKind () == kind::FORALL);
    switch(r[1].getKind()){
    case kind::REWRITE_RULE:
      return (r[1].eqNode(r[2])).
          substitute(vars.begin(),vars.end(),match.begin(),match.end());
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
            Node body = getSubstitutedBody(r, vars, subst);
            d_th->getOutputChannel().lemma(body);
        }
      }
    }
}

void RewriteEngine::registerQuantifier( Node n ){
    unsigned level = d_th->getValuation().getDecisionLevel();
    Debug("rewriterules") << "registerQuantifier: " << n
                          << " level: " << level << std::endl;
    switch(n.getKind()) {
    case kind::FORALL:
        if( TheoryQuantifiers::isRewriteKind( n[1].getKind() ) ){
            //TODO? test if the rewrite rule is already there
            d_rules.push_back(n);
        };
        break;
    default:
        Unhandled(n.getKind());
    }
}

void RewriteEngine::assertNode( Node n ){
    Debug("rewriterules") << "assertNode: " << n << std::endl;
}

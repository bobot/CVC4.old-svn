/*********************                                                       */
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
 ** \brief [[ Deals with rewrite rules ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/rewriterules/theory_rewriterules_rules.h"
#include "theory/rewriterules/theory_rewriterules_params.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rewriterules;


namespace CVC4 {
namespace theory {
namespace rewriterules {

RewriteRule const TheoryRewriteRules::makeRewriteRule(const Node r)
{
  Assert(r.getKind() == kind::REWRITE_RULE);
  Assert(r[2].getKind() == kind::RR_REWRITE);
  Debug("rewriterules") << "create rewriterule:" << r << std::endl;
  /* Equality */
  TNode head = r[2][0];
  TNode body = r[2][1];
  Node equality = head.eqNode(body);
  /* Guards */
  TNode guards = r[1];
  /* Trigger */
  std::vector<Node> pattern;
  /*   Replace variables by Inst_* variable and tag the terms that
       contain them */
  std::vector<Node> vars;
  vars.reserve(r[0].getNumChildren());
  for( Node::const_iterator v = r[0].begin(); v != r[0].end(); ++v ){
    vars.push_back(*v);
  };
  std::vector<Node> inst_constants =
    getQuantifiersEngine()->createInstVariable(vars);
  pattern.push_back(getQuantifiersEngine()->
                    convertNodeToPattern(head,r,vars,inst_constants));
  Trigger trigger = createTrigger(r,pattern);
  Trigger trigger2 = createTrigger(r,pattern); //Hack
  // final construction
  return RewriteRule(*this, trigger, trigger2,
                     guards, equality, vars, inst_constants);
};


/** A rewrite rule */
void RewriteRule::toStream(std::ostream& out) const{
  for(std::vector<Node>::const_iterator
        iter = guards.begin(); iter != guards.end(); ++iter){
    out << *iter;
  };
  out << "=>" << equality << std::endl;
  out << "[";
  for(BodyMatch::const_iterator
        iter = body_match.begin(); iter != body_match.end(); ++iter){
    out << (*iter).first << "(" << (*iter).second << ")" << ",";
  };
  out << "]" << std::endl;
}

RewriteRule::RewriteRule(TheoryRewriteRules & re,
                         Trigger & tr, Trigger & tr2, Node g, Node eq,
                         std::vector<Node> & fv,std::vector<Node> & iv) :
  trigger(tr), equality(eq), free_vars(), inst_vars(),
  body_match(),trigger_for_body_match(tr2),
  d_cache(re.getContext()){
  free_vars.swap(fv);inst_vars.swap(iv);
  switch(g.getKind()){
  case kind::AND:
    guards.reserve(g.getNumChildren());
    for(Node::iterator i = g.begin(); i != g.end(); ++i) {
      guards.push_back(*i);
    };
    break;
  default:
    if (g != re.d_true) guards.push_back(g);
    /** otherwise guards is empty */
  };
};

bool RewriteRule::noGuard()const{ return guards.size() == 0; };

bool RewriteRule::inCache(std::vector<Node> & subst)const{
  /* INST_PATTERN because its 1: */
  NodeBuilder<> nodeb(kind::INST_PATTERN);
  for(std::vector<Node>::const_iterator p = subst.begin();
      p != subst.end(); ++p){
    if (rewrite_before_cache) nodeb << Rewriter::rewrite(*p);
    else nodeb << *p;
  };
  Node node = nodeb;
  CacheNode::const_iterator e = d_cache.find(node);
  /* Already in the cache */
  if( e != d_cache.end() ) return true;
  /* Because we add only context dependent data and the const is for that */
  RewriteRule & rule = const_cast<RewriteRule &>(*this);
  rule.d_cache.insert(node);
  return false;
};



}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

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

#include "theory/rewriterules/theory_rewriterules.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rewriterules;


namespace CVC4 {
namespace theory {
namespace rewriterules {

// std::ostream& operator <<(std::ostream& stream, const RewriteRule& r) {
//   for(std::vector<Node>::const_iterator
//         iter = r.guards.begin(); iter != r.guards.end(); ++iter){
//     stream << *iter;
//   };
//   return stream << "=>" << r.equality;
// }

static const bool propagate_as_lemma = false;
static const bool cache_match = true;

static const size_t RULEINSTID_TRUE = ((size_t) -1);
static const size_t RULEINSTID_FALSE = ((size_t) -2);

  /** Rule an instantiation with the given match */
RuleInst::RuleInst(TheoryRewriteRules & re, RewriteRuleId r, InstMatch & im,
                   RuleInstId i):
  rule(r),id(i)
{
  Assert(i != RULEINSTID_TRUE && i != RULEINSTID_FALSE);
  const RewriteRule & rule = re.get_rule(r);
  im.computeTermVec(re.getQuantifiersEngine(), rule.inst_vars , subst);
  if(cache_match) rule.checkCache(subst);
  start = findGuard(re, 0);
  if(start == (rule.guards).size()) throw true;
};

Node RuleInst::substNode(const TheoryRewriteRules & re, TNode r)const{
  const RewriteRule & rrule = re.get_rule(rule);
  return r.substitute(rrule.free_vars.begin(),rrule.free_vars.end(),
                      subst.begin(),subst.end());
};

size_t RuleInst::findGuard(TheoryRewriteRules & re, size_t start)const{
  const RewriteRule & r = re.get_rule(rule);
  while (start < (r.guards).size()){
    Node g = substNode(re,r.guards[start]);
    switch(re.addWatchIfDontKnow(g,id,start)){
    case ATRUE:
      ++start;
      continue;
    case AFALSE:
      return -1;
    case ADONTKNOW:
      return start;
    }
    /** the literal is already true pick another */
    ++start;;
  }
  /** All the guards are verified */
  re.propagateRule(*this);
  return start;
};

void Guarded::nextGuard(TheoryRewriteRules & re)const{
  Assert(inst != RULEINSTID_TRUE && inst != RULEINSTID_FALSE);
  re.get_inst(inst).findGuard(re,d_guard+1);
};

/** start indicate the first guard which is not true */
Guarded::Guarded(RuleInstId ri, const size_t start) :
  d_guard(start),inst(ri) {};
Guarded::Guarded(const Guarded & g) :
  d_guard(g.d_guard),inst(g.inst) {};
Guarded::Guarded() :
  d_guard(-1),inst(-1) {};

RewriteRule const makeRewriteRule(TheoryRewriteRules & re, const Node r)
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
    re.getQuantifiersEngine()->createInstVariable(vars);
  pattern.push_back(re.getQuantifiersEngine()->
                    convertNodeToPattern(head,r,vars,inst_constants));
  Trigger trigger = re.createTrigger(r,pattern);
  return RewriteRule(re, trigger, guards, equality, vars, inst_constants);
};


/** A rewrite rule */
RewriteRule::RewriteRule(TheoryRewriteRules & re,
                         Trigger & tr, Node g, Node eq,
                         std::vector<Node> & fv,std::vector<Node> & iv) :
  trigger(tr), equality(eq), free_vars(), inst_vars(),
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

void RewriteRule::checkCache(std::vector<Node> & subst)const{
  /* INST_PATTERN because its 1: */
  NodeBuilder<> nodeb(kind::INST_PATTERN);
  for(std::vector<Node>::const_iterator p = subst.begin();
      p != subst.end(); ++p) nodeb << *p;
  Node node = nodeb;
  CacheNode::const_iterator e = d_cache.find(node);
  /* Already in the cache */
  if( e != d_cache.end() ) throw false;
  /* Because we add only context dependent data and the const is for that */
  RewriteRule & rule = const_cast<RewriteRule &>(*this);
  rule.d_cache.insert(node);
};

TheoryRewriteRules::TheoryRewriteRules(context::Context* c,
                                       context::UserContext* u,
                                       OutputChannel& out,
                                       Valuation valuation,
                                       QuantifiersEngine* qe) :
  Theory(THEORY_REWRITERULES, c, u, out, valuation,qe),
  d_rules(c), d_ruleinsts(c), d_guardeds(c),
  d_literalsToPropagate(c), d_literalsToPropagateIndex(c, 0),d_explanations(c)
  {
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  Debug("rewriterules") << Node::setdepth(-1);
}

void TheoryRewriteRules::check(Effort level) {

  while(!done()) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("rewriterules") << "TheoryRewriteRules::check(): processing " << fact << std::endl;
      if (getValuation().getDecisionLevel()>0)
        Unhandled(getValuation().getDecisionLevel());

      d_rules.push_back(makeRewriteRule(*this,fact));
    };

  /** Test each rewrite rule */
  for(size_t rid = 0, end = d_rules.size(); rid < end; ++rid) {
    const RewriteRule & r = d_rules[rid];
    // Debug("rewriterules") << "  rule: " << r << std::endl;
    Trigger & tr = const_cast<Trigger &> (r.trigger);
    //reset instantiation round for trigger (set up match production)
    tr.resetInstantiationRound();
    //begin iterating from the first match produced by the trigger
    tr.reset( Node::null() );

    /** Test the possible matching one by one */
    InstMatch im;
    while(tr.getNextMatch( im )){
      Debug("rewriterules") << "One matching found" << std::endl;
      try{
        RuleInstId id = d_ruleinsts.size();
        RuleInst ri = RuleInst(*this,rid,im,id);
        d_ruleinsts.push_back(ri);
      }catch (bool b){
        Debug("rewriterules") << "RuleInst create:" << b << std::endl;
      };
      im.clear();
    }
  }


  /** Temporary way. Poll value */
  for (GuardedMap::const_iterator p = d_guardeds.begin();
       p != d_guardeds.end(); ++p){
    TNode g = (*p).first;
    const GList * const l = (*p).second;
    const Guarded & glast = (*l)[l->size()-1];
    if(glast.inst == RULEINSTID_TRUE||glast.inst == RULEINSTID_FALSE) continue;
    bool value;
    if(getValuation().hasSatValue(g,value)) notification(g,value);
  }

};

void TheoryRewriteRules::registerQuantifier( Node n ){};

Trigger TheoryRewriteRules::createTrigger( TNode n, std::vector<Node> & pattern )
  const{
  Debug("rewriterules") << "createTrigger:";
  getQuantifiersEngine()->registerPattern(pattern);
  return *Trigger::mkTrigger(getQuantifiersEngine(),n,pattern, false, true);
};

bool TheoryRewriteRules::notifyIfKnown(const GList * const ltested,
                                        GList * const lpropa) {
    Assert(ltested->size() > 0);
    const Guarded & glast = (*ltested)[ltested->size()-1];
    if(glast.inst == RULEINSTID_TRUE || glast.inst == RULEINSTID_FALSE){
      notification(lpropa,glast.inst == RULEINSTID_TRUE);
      return true;
    };
    return false;
};

void TheoryRewriteRules::notification(GList * const lpropa, bool b){
  if (b){
    for(GList::const_iterator g = lpropa->begin();
        g != lpropa->end(); ++g) {
      (*g).nextGuard(*this);
    };
    lpropa->push_back(Guarded(RULEINSTID_TRUE,0));
  }else{
    lpropa->push_back(Guarded(RULEINSTID_FALSE,0));
  };
};



Answer TheoryRewriteRules::addWatchIfDontKnow(Node g0, RuleInstId rid,
                                         const size_t gid){
  /** TODO: Should use the representative of g, but should I keep the
      mapping for myself? */
  /** Currently create a node with a literal */
  Node g = getValuation().ensureLiteral(g0);
  GuardedMap::iterator l_i = d_guardeds.find(g);
  GList* l;
  if( l_i == d_guardeds.end() ) {
    /** Not watched so IDONTNOW */
    l = new(getContext()->getCMM())
      GList(true, getContext(), false,
            ContextMemoryAllocator<Guarded>(getContext()->getCMM()));
    d_guardeds.insertDataFromContextMemory(g, l);
    /* TODO Add register propagation */
  } else {
    l = (*l_i).second;
    Assert(l->size() > 0);
    const Guarded & glast = (*l)[l->size()-1];
    if(glast.inst == RULEINSTID_TRUE) return ATRUE;
    if(glast.inst == RULEINSTID_FALSE) return AFALSE;

  };
  /** I DONT KNOW because not watched or because not true nor false */
  l->push_back(Guarded(rid,gid));
  return ADONTKNOW;
};

void TheoryRewriteRules::notification(Node g, bool b){
  GuardedMap::const_iterator l = d_guardeds.find(g);
  /** Should be a propagated node already known */
  Assert(l != d_guardeds.end());
  notification((*l).second,b);
}


void TheoryRewriteRules::notifyEq(TNode lhs, TNode rhs) {
  GuardedMap::const_iterator ilhs = d_guardeds.find(lhs);
  GuardedMap::const_iterator irhs = d_guardeds.find(rhs);
  /** Should be a propagated node already known */
  Assert(ilhs != d_guardeds.end());
  if( irhs == d_guardeds.end() ) {
    /** Not watched so points to the list directly */
    d_guardeds.insertDataFromContextMemory(rhs, (*ilhs).second);
  } else {
    GList * const llhs = (*ilhs).second;
    GList * const lrhs = (*irhs).second;
    if(!(notifyIfKnown(llhs,lrhs) || notifyIfKnown(lrhs,llhs))){
      /** If none of the two is known */
      for(GList::const_iterator g = llhs->begin(); g != llhs->end(); ++g){
        lrhs->push_back(*g);
      };
    };
  };
};


void TheoryRewriteRules::propagateRule(const RuleInst & inst){
  //   Debug("rewriterules") << "A rewrite rules is verified. Add lemma:";
  const RewriteRule & rule = get_rule(inst.rule);
  Node equality = inst.substNode(*this,rule.equality);
  if(propagate_as_lemma){
    Node lemma = equality;
    if(rule.guards.size() > 0){
      lemma = substGuards(inst,rule).impNode(equality);
    };
    //  Debug("rewriterules") << "lemma:" << lemma << std::endl;
    getOutputChannel().lemma(lemma);
  }else{
    Node lemma_lit = getValuation().ensureLiteral(equality);
    bool value;
    if(getValuation().hasSatValue(lemma_lit,value)){
      /* Already assigned */
      if (!value){
        Node conflict = substGuards(inst,rule,lemma_lit);
        getOutputChannel().conflict(conflict);
      };
    }else{
      d_literalsToPropagate.push_back(lemma_lit);
      d_explanations.insert(lemma_lit,inst.id);
   };
  };
};

void TheoryRewriteRules::propagate(Effort e){
  for (; d_literalsToPropagateIndex < d_literalsToPropagate.size();
       d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1){
    TNode lemma_lit = d_literalsToPropagate[d_literalsToPropagateIndex];
    bool value;
    if(getValuation().hasSatValue(lemma_lit,value)){
      /* Already assigned */
      /* TODO generalize explain */
      ExplanationMap::const_iterator rinstid = d_explanations.find(lemma_lit);
      Assert(rinstid!=d_explanations.end(),"I forget the explanation...");
      const RuleInst & inst = get_inst((*rinstid).second);
      const RewriteRule & rule = get_rule(inst.rule);
      if (!value){
        Node conflict = substGuards(inst,rule,lemma_lit);
        getOutputChannel().conflict(conflict);
      };
    }else{
      getOutputChannel().propagate(lemma_lit);
    };
  }
}


Node TheoryRewriteRules::substGuards(const RuleInst & inst,
                                     const RewriteRule & r,
                                     /* Already substituted */
                                     Node last){
  /** No guards */
  const size_t size = r.guards.size();
  if(size == 0) return d_true;
  /** One guard */
  if(size == 1) return inst.substNode(*this,r.guards[0]);
  /** Guards */ /* TODO remove the duplicate with a set like in uf? */
  NodeBuilder<> conjunction(kind::AND);
  for(std::vector<Node>::const_iterator p = r.guards.begin();
      p != r.guards.end(); ++p) {
    conjunction << inst.substNode(*this,*p);
  };
  if (last != Node::null()) conjunction << last;
  return conjunction;
}

Node TheoryRewriteRules::explain(TNode n){
  ExplanationMap::const_iterator rinstid = d_explanations.find(n);
  Assert(rinstid!=d_explanations.end(),"I forget the explanation...");
  const RuleInst & inst = get_inst((*rinstid).second);
  const RewriteRule & r = get_rule(inst.rule);
  return substGuards(inst,r);
}


}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

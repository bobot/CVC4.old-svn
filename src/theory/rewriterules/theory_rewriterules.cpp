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
#include "theory/rewriterules/theory_rewriterules_rules.h"
#include "theory/rewriterules/theory_rewriterules_params.h"

#include "theory/rewriter.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rewriterules;


namespace CVC4 {
namespace theory {
namespace rewriterules {

inline std::ostream& operator <<(std::ostream& stream, const RuleInst& ri) {
  ri.toStream(stream);
  return stream;
}

static const size_t RULEINSTID_TRUE = ((size_t) -1);
static const size_t RULEINSTID_FALSE = ((size_t) -2);

  /** Rule an instantiation with the given match */
RuleInst::RuleInst(TheoryRewriteRules & re, RewriteRuleId r,
                   std::vector<Node> & inst_subst):
  rule(r),id(RULEINSTID_TRUE)
{
  subst.swap(inst_subst);
};

void RuleInst::setId(RuleInstId nid){
  Assert(nid != RULEINSTID_TRUE && nid != RULEINSTID_FALSE);
  Assert(id == RULEINSTID_TRUE);
  id = nid;
}

Node RuleInst::substNode(const TheoryRewriteRules & re, TNode r,
                         TCache cache ) const {
  Assert(id != RULEINSTID_TRUE && id != RULEINSTID_FALSE);
  const RewriteRule & rrule = re.get_rule(rule);
  return r.substitute (rrule.free_vars.begin(),rrule.free_vars.end(),
                       subst.begin(),subst.end(),cache);
};

size_t RuleInst::findGuard(TheoryRewriteRules & re, size_t start)const{
  TCache cache;
  Assert(id != RULEINSTID_TRUE && id != RULEINSTID_FALSE);
  const RewriteRule & r = re.get_rule(rule);
  while (start < (r.guards).size()){
    Node g = substNode(re,r.guards[start],cache);
    switch(re.addWatchIfDontKnow(g,id,start)){
    case ATRUE:
      Debug("rewriterules") << g << "is true" << std::endl;
      ++start;
      continue;
    case AFALSE:
      Debug("rewriterules") << g << "is false" << std::endl;
      return -1;
    case ADONTKNOW:
      Debug("rewriterules") << g << "is unknown" << std::endl;
      return start;
    }
  }
  /** All the guards are verified */
  re.propagateRule(*this,cache);
  return start;
};

void RuleInst::toStream(std::ostream& out) const{
  out << "(" << rule << ") ";
  for(std::vector<Node>::const_iterator
        iter = subst.begin(); iter != subst.end(); ++iter){
    out << *iter;
  };
}


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

TheoryRewriteRules::TheoryRewriteRules(context::Context* c,
                                       context::UserContext* u,
                                       OutputChannel& out,
                                       Valuation valuation,
                                       QuantifiersEngine* qe) :
  Theory(THEORY_REWRITERULES, c, u, out, valuation,qe),
  d_rules(c), d_ruleinsts(c), d_guardeds(c), d_checkLevel(c,0),
  d_explanations(c), d_ruleinsts_to_add(c)
  {
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  Debug("rewriterules") << Node::setdepth(-1);
}


void TheoryRewriteRules::addMatchRuleTrigger(const RewriteRuleId rid,
                                             const RewriteRule & r,
                                             InstMatch & im,
                                             bool delay){
  std::vector<Node> subst;
  im.computeTermVec(getQuantifiersEngine(), r.inst_vars , subst);
  if(!cache_match || !r.inCache(subst)){
    RuleInst ri = RuleInst(*this,rid,subst);
    Debug("rewriterules") << "One matching found"
                          << (delay? "(delayed)":"")
                          << ":" << ri << std::endl;
    // Find the first non verified guard, don't save the rule if the
    // rule can already be fired In fact I save it otherwise strange
    // things append.
    if(delay) d_ruleinsts_to_add.push(ri);
    else{
      ri.setId(d_ruleinsts.size());
      if(ri.findGuard(*this, 0) != (r.guards).size())
        d_ruleinsts.push_back(ri);
    };
  };
}


void TheoryRewriteRules::check(Effort level) {

  while(!done()) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("rewriterules") << "TheoryRewriteRules::check(): processing " << fact << std::endl;
      if (getValuation().getDecisionLevel()>0)
        Unhandled(getValuation().getDecisionLevel());

      addRewriteRule(fact);

    };

  Debug("rewriterules") << "Check:" << d_checkLevel << std::endl;

  /** Test each rewrite rule */
  for(size_t rid = 0, end = d_rules.size(); rid < end; ++rid) {
    const RewriteRule & r = d_rules[rid];
    Debug("rewriterules") << "  rule: " << r << std::endl;
    Trigger & tr = const_cast<Trigger &> (r.trigger);
    //reset instantiation round for trigger (set up match production)
    tr.resetInstantiationRound();
    //begin iterating from the first match produced by the trigger
    tr.reset( Node::null() );

    /** Test the possible matching one by one */
    InstMatch im;
    while(tr.getNextMatch( im )){
      addMatchRuleTrigger(rid, r, im, false);
      im.clear();
    }
  }

  const bool do_notification = d_checkLevel == 0 || level==FULL_EFFORT;
  bool polldone = false;

  GuardedMap::const_iterator p = d_guardeds.begin();
  do{


    //dequeue instantiated rules
    for(; !d_ruleinsts_to_add.empty(); d_ruleinsts_to_add.pop()){
      RuleInst ri = d_ruleinsts_to_add.front();
      ri.setId(d_ruleinsts.size());
      if(ri.findGuard(*this, 0) != (get_rule(ri.rule).guards).size())
        d_ruleinsts.push_back(ri);
    };

    if(do_notification)
    /** Temporary way. Poll value */
    for (; p != d_guardeds.end(); ++p){
      TNode g = (*p).first;
      const GList * const l = (*p).second;
      const Guarded & glast = (*l).back();
      // cout << "Polled?:" << g << std::endl;
      if(glast.inst == RULEINSTID_TRUE||glast.inst == RULEINSTID_FALSE) continue;
      // cout << "Polled!:" << g << "->" << (glast.inst == RULEINSTID_TRUE||glast.inst == RULEINSTID_FALSE) << std::endl;
      bool value;
      if(getValuation().hasSatValue(g,value)){
        polldone = true;
        Debug("rewriterules") << "Poll value:" << g
                             << " is " << (value ? "true" : "false") << std::endl;
        notification(g,value);
        //const Guarded & glast2 = (*l)[l->size()-1];
        // cout << "Polled!!:" << g << "->" << (glast2.inst == RULEINSTID_TRUE||glast2.inst == RULEINSTID_FALSE) << std::endl;
      };
    };

  }while(!d_ruleinsts_to_add.empty() ||
         (p != d_guardeds.end() && do_notification));

  if(polldone) d_checkLevel = checkSlowdown;
  else d_checkLevel = d_checkLevel > 0 ? (d_checkLevel - 1) : 0;

  /** Narrowing by splitting on the guards */
  /** Perhaps only when no notification? */
  if(level==FULL_EFFORT){
    for (GuardedMap::const_iterator p = d_guardeds.begin();
         p != d_guardeds.end(); ++p){
      TNode g = (*p).first;
      const GList * const l = (*p).second;
      const Guarded & glast = (*l)[l->size()-1];
      if(glast.inst == RULEINSTID_TRUE||glast.inst == RULEINSTID_FALSE)
        continue;
      // If it has a value it should already has been notified
      bool value; value = value; // avoiding the warning in non debug mode
      Assert(!getValuation().hasSatValue(g,value));
      Debug("rewriterules") << "Narrowing on:" << g << std::endl;
      getOutputChannel().split(g);
    }
  }

  Debug("rewriterules") << "Check done:" << d_checkLevel << std::endl;

};


void TheoryRewriteRules::registerQuantifier( Node n ){};

Trigger TheoryRewriteRules::createTrigger( TNode n, std::vector<Node> & pattern )
  const{
  //  Debug("rewriterules") << "createTrigger:";
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
      GList(true, getContext(), false);//,
            //ContextMemoryAllocator<Guarded>(getContext()->getCMM()));
    d_guardeds.insert(g ,l);//.insertDataFromContextMemory(g, l);
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


void TheoryRewriteRules::propagateRule(const RuleInst & inst, TCache cache){
  //   Debug("rewriterules") << "A rewrite rules is verified. Add lemma:";
  Debug("rewriterules") << "propagateRule" << inst << std::endl;
  const RewriteRule & rule = get_rule(inst.rule);
  Node equality = inst.substNode(*this,rule.body,cache);
  if(propagate_as_lemma){
    Node lemma = equality;
    if(rule.guards.size() > 0){
      lemma = substGuards(inst,rule, cache).impNode(equality);
    };
    //  Debug("rewriterules") << "lemma:" << lemma << std::endl;
    getOutputChannel().lemma(lemma);
  }else{
    Node lemma_lit = getValuation().ensureLiteral(equality);
    bool value;
    if(getValuation().hasSatValue(lemma_lit,value)){
      /* Already assigned */
      if (!value){
        Node conflict = substGuards(inst,rule, cache,lemma_lit);
        getOutputChannel().conflict(conflict);
      };
    }else{
      getOutputChannel().propagate(lemma_lit);
      d_explanations.insert(lemma_lit,inst.id);
   };
  };

  //Verify that this instantiation can't immediately fire another rule
  for(RewriteRule::BodyMatch::const_iterator p = rule.body_match.begin();
      p != rule.body_match.end(); ++p){
    const RewriteRuleId rid = (*p).second;
    const RewriteRule & r = d_rules[rid];
    // Debug("rewriterules") << "  rule: " << r << std::endl;
    // Use trigger2 since we can be in check
    Trigger & tr = r.trigger_for_body_match;
    InstMatch im;
    tr.getMatch(inst.substNode(*this,(*p).first, cache),im);
    if(!im.empty()) addMatchRuleTrigger(rid, r, im);
  }
};


Node TheoryRewriteRules::substGuards(const RuleInst & inst,
                                     const RewriteRule & r,
                                     TCache cache,
                                     /* Already substituted */
                                     Node last){
  /** No guards */
  const size_t size = r.guards.size();
  if(size == 0) return d_true;
  /** One guard */
  if(size == 1) return inst.substNode(*this,r.guards[0],cache);
  /** Guards */ /* TODO remove the duplicate with a set like in uf? */
  NodeBuilder<> conjunction(kind::AND);
  for(std::vector<Node>::const_iterator p = r.guards.begin();
      p != r.guards.end(); ++p) {
    conjunction << inst.substNode(*this,*p,cache);
  };
  if (last != Node::null()) conjunction << last;
  return conjunction;
}

Node TheoryRewriteRules::explain(TNode n){
  ExplanationMap::const_iterator rinstid = d_explanations.find(n);
  Assert(rinstid!=d_explanations.end(),"I forget the explanation...");
  const RuleInst & inst = get_inst((*rinstid).second);
  const RewriteRule & r = get_rule(inst.rule);
  return substGuards(inst,r, TCache ());
}


}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

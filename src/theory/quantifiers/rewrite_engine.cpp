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
 ** \brief [[ Deals with rewrite rules ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/quantifiers/rewrite_engine.h"
#include <utility>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

// std::ostream& operator <<(std::ostream& stream, const RewriteRule& r) {
//   for(std::vector<Node>::const_iterator
//         iter = r.guards.begin(); iter != r.guards.end(); ++iter){
//     stream << *iter;
//   };
//   return stream << "=>" << r.equality;
// }

static const bool propagate_as_lemma = true;

static const size_t RULEINSTID_TRUE = ((size_t) -1);
static const size_t RULEINSTID_FALSE = ((size_t) -2);

  /** Rule an instantiation with the given match */
RuleInst::RuleInst(RewriteEngine & re, RewriteRuleId r, InstMatch & im,
                   RuleInstId i):
  rule(r),id(i)
{
  Assert(i != RULEINSTID_TRUE && i != RULEINSTID_FALSE);
  im.computeTermVec(re.qe, re.get_rule(r).inst_vars , subst);
  start = -1; /* So that any temporary Guard doesn't delete this */
  start = findGuard(re, 0);
};

Node RuleInst::substNode(const RewriteEngine & re, TNode r)const{
  const RewriteRule & rrule = re.get_rule(rule);
  return r.substitute(rrule.free_vars.begin(),rrule.free_vars.end(),
                      subst.begin(),subst.end());
};

size_t RuleInst::findGuard(RewriteEngine & re, size_t start)const{
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

bool RuleInst::startedTrue(const RewriteEngine & re)const{
  return start == (re.get_rule(rule).guards).size();
};

void Guarded::nextGuard(RewriteEngine & re)const{
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

RewriteRule const makeRewriteRule(RewriteEngine & re, const Node r)
{
  Assert(r.getKind () == kind::FORALL);
  Assert(r[1].getKind() == kind::REWRITE_RULE);
  Debug("rewriterules") << "create rewriterule:" << r << std::endl;
  /* Equality */
  TNode head = r[1][1];
  TNode body = r[1][2];
  Node equality = head.eqNode(body);
  /* Guards */
  TNode guards = r[1][0];
  /* Trigger */
  std::vector<Node> pattern;
  /*   Replace variables by Inst_* variable and tag the terms that
       contain them */
  pattern.push_back(re.qe->getSubstitutedNode(head,r));
  Trigger trigger = re.createTrigger(r,pattern);
  return RewriteRule(re, trigger, guards, equality,
                     re.d_vars(r),
                     re.d_inst_constants(r)
                     );
};


/** A rewrite rule */
RewriteRule::RewriteRule(RewriteEngine & re,
                         Trigger & tr, Node g, Node eq,
                         std::vector<Node> & fv,std::vector<Node> & iv) :
  trigger(tr), equality(eq), free_vars(fv), inst_vars(iv){
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

RewriteEngine::RewriteEngine(context::Context* c, TheoryQuantifiers* th ) :
  d_th( th ), d_rules(c), d_ruleinsts(c), d_guardeds(c),
  d_literalsToPropagate(c), d_literalsToPropagateIndex(c, 0),d_explanations(c),
  qe(th->getQuantifiersEngine()){
  uf=((uf::TheoryUF*) qe->d_te->getTheory(theory::THEORY_UF));
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  Debug("rewriterules") << Node::setdepth(-1);
}

Node getPattern(QuantifiersEngine* qe, Node r){
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

// std::vector<Node> RewriteEngine::getSubstitutedGuards
// (Node r, std::vector< Node > &vars, std::vector< Node > &match  ){
//   std::vector<Node> gs;
//   Node guard = r[1][0];
//   switch(guard.getKind()){
//   case kind::AND:
//     for(Node::iterator i = guard.begin(); i != guard.end(); ++i) {
//       gs.push_back(*i);
//     };
//     break;
//   default:
//     gs.push_back(guard);
//   };
//   return gs;
// }

// Node RewriteEngine::getSubstitutedBody
// (Node r, std::vector< Node > &vars, std::vector< Node > &match){
//   std::vector<Node> gs;
//   /** todo */
//   Assert(r.getKind () == kind::FORALL);
//   switch(r[1].getKind()){
//   case kind::REWRITE_RULE:
//     return (r[1][1].eqNode(r[1][2])).
//       substitute(vars.begin(),vars.end(),match.begin(),match.end());
//   case kind::REDUCTION_RULE:
//   case kind::DEDUCTION_RULE:
//     return r[1][2].
//       substitute(vars.begin(),vars.end(),match.begin(),match.end());
//   default:
//     Unhandled(r[1].getKind());
//     return r;
//   }
// }

// Node RewriteEngine::getSubstitutedLemma
// (Node r, std::vector< Node > &vars, std::vector< Node > &match){
//   std::vector<Node> gs;
//   Node lemma;
//   Assert(r.getKind () == kind::FORALL);
//   switch(r[1].getKind()){
//   case kind::REWRITE_RULE:
//     lemma = r[1][0].impNode(r[1][1].eqNode(r[1][2]));
//     return lemma.
//       substitute(vars.begin(),vars.end(),match.begin(),match.end());
//   case kind::REDUCTION_RULE:
//   case kind::DEDUCTION_RULE:
//     lemma = r[1][1].impNode(r[1][2]);
//     lemma = r[1][0].impNode(lemma);
//     return lemma
//       .substitute(vars.begin(),vars.end(),match.begin(),match.end());
//   default:
//     Unhandled(r[1].getKind());
//     return r;
//   }
// }

void RewriteEngine::check( Theory::Effort e ){
  Debug("rewriterules") << "check: " << e << std::endl;

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
      RuleInstId id = d_ruleinsts.size();
      RuleInst ri = RuleInst(*this,rid,im,id);
      /** true from the start so we don't add it */
      if (!ri.startedTrue(*this)) d_ruleinsts.push_back(ri);
      im.clear();
    }
  }
};

void RewriteEngine::registerQuantifier( Node n ){};

void RewriteEngine::assertNode( Node n ){
  Debug("rewriterules") << "assertNode: " << n << std::endl;
  if( TheoryQuantifiers::isRewriteKind( n[1].getKind() ) ){
    if (d_th->getValuation().getDecisionLevel()>0)
      Unhandled(d_th->getValuation().getDecisionLevel());

    d_rules.push_back(makeRewriteRule(*this,n));
  };
};

Trigger RewriteEngine::createTrigger( TNode n, std::vector<Node> & pattern )
  const{
  Debug("rewriterules") << "createTrigger:";
  /** to put that in init */
  uf::UfTermDb* db =
    ((uf::TheoryUF*) qe->d_te->getTheory(theory::THEORY_UF))
    ->getTermDatabase();
  for(std::vector<Node>::iterator p = pattern.begin();
      p != pattern.end(); ++p) {
    Debug("rewriterules") << *p << ", ";
    db->add(*p);
  };
  return *Trigger::mkTrigger(qe,n,pattern, false, true);
};

Answer RewriteEngine::addWatchIfDontKnow(Node g, RuleInstId rid,
                                         const size_t gid){
  /** TODO: Should use the representative of g, but should I keep the
      mapping for myself? */
  GuardedMap::iterator l_i = d_guardeds.find(g);
  GList* l;
  if( l_i == d_guardeds.end() ) {
    /** Not watched so IDONTNOW */
    l = new(d_th->getContext()->getCMM())
      GList(true, d_th->getContext(), false,
            ContextMemoryAllocator<Guarded>(d_th->getContext()->getCMM()));
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


void RewriteEngine::notification(GList * const lpropa, bool b){
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


void RewriteEngine::notification(Node g, bool b){
  GuardedMap::const_iterator l = d_guardeds.find(g);
  /** Should be a propagated node already known */
  Assert(l != d_guardeds.end());
  notification((*l).second,b);
}

bool RewriteEngine::notifyIfKnown(const GList * const ltested,
                                        GList * const lpropa) {
    Assert(ltested->size() > 0);
    const Guarded & glast = (*ltested)[ltested->size()-1];
    if(glast.inst == RULEINSTID_TRUE || glast.inst == RULEINSTID_FALSE){
      notification(lpropa,glast.inst == RULEINSTID_TRUE);
      return true;
    };
    return false;
};

void RewriteEngine::notifyEq(TNode lhs, TNode rhs) {
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


void RewriteEngine::propagateRule(const RuleInst & inst){
  //   Debug("rewriterules") << "A rewrite rules is verified. Add lemma:";
  Assert(get_rule(inst.rule).guards.size() == 0);
  Node lemma = inst.substNode(*this,get_rule(inst.rule).equality);
  if(propagate_as_lemma){
    //  Debug("rewriterules") << "lemma:" << lemma << std::endl;
    d_th->getOutputChannel().lemma(lemma);
  }else{
    Node lemma_lit = d_th->getValuation().ensureLiteral(lemma);
    d_th->getOutputChannel().propagate(lemma_lit);
    d_explanations.insert(lemma_lit,inst.id);
  };
};


Node RewriteEngine::explain(TNode n){
  ExplanationMap::const_iterator rinstid = d_explanations.find(n);
  Assert(rinstid!=d_explanations.end(),"I forget the explanation...");
  const RuleInst & inst = get_inst((*rinstid).second);
  const RewriteRule & r = get_rule(inst.rule);
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
  return conjunction;
}

/*********************                                                       */
/*! \file rewrite_engine.h
 ** \verbatim
 ** Original author: ajreynol
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
 ** \brief Rewrite Engine classes
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H

#include "context/cdlist_context_memory.h"
#include "context/cdqueue.h"
#include "theory/valuation.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "context/context_mm.h"

namespace CVC4 {
namespace theory {
namespace rewriterules {

class TheoryRewriteRules;

typedef size_t RewriteRuleId;
typedef size_t RuleInstId;

  enum Answer {ATRUE, AFALSE, ADONTKNOW};

  class RewriteRule{
  public:
    // constant
    Trigger trigger;
    std::vector<Node> guards;
    const Node equality;
    std::vector<Node> free_vars; /* free variable in the rule */
    std::vector<Node> inst_vars; /* corresponding vars in the triggers */
    /* After instantiating the body new match can appear (TNode
       because is a subterm of a body on the assicaited rewrite
       rule) */
    typedef std::vector<std::pair<TNode,RewriteRuleId> > BodyMatch;
    BodyMatch body_match;
    Trigger trigger_for_body_match; // used because we can be matching
                                    // trigger when we need new match.
                                    // So currently we use another
                                    // trigger for that.

    //context dependent
    typedef context::CDHashSet<Node, NodeHashFunction> CacheNode;
    CacheNode d_cache;

    RewriteRule(TheoryRewriteRules & re,
                Trigger & tr, Trigger & tr2, Node g, Node eq,
                std::vector<Node> & fv,std::vector<Node> & iv);
    bool noGuard()const;
    bool inCache(std::vector<Node> & subst)const;

    void toStream(std::ostream& out) const;
  };

  class RuleInst{
  public:
    /** The rule has at least one guard */
    const RewriteRuleId rule;

    /** The id of the Rule inst */
    RuleInstId id;

    /** the substitution */
    std::vector<Node> subst;

    /** Rule an instantiation with the given match */
    RuleInst(TheoryRewriteRules & re, const RewriteRuleId rule,
             std::vector<Node> & inst_subst);
    Node substNode(const TheoryRewriteRules & re, TNode r,
                   std::hash_map<TNode, TNode, TNodeHashFunction> cache =
                   std::hash_map<TNode, TNode, TNodeHashFunction>()
                   )const;
    size_t findGuard(TheoryRewriteRules & re, size_t start)const;
    void setId(const RuleInstId i);

    void toStream(std::ostream& out) const;
  };

/** A pair? */
  class Guarded {
  public:
    /** The backtracking is done somewhere else */
    size_t d_guard; /* the id of the guard */

    /** The shared instantiation data */
    RuleInstId inst;

    void nextGuard(TheoryRewriteRules & re)const;

    /** start indicate the first guard which is not true */
    Guarded(const RuleInstId ri, const size_t start);
    Guarded(const Guarded & g);
    /** Should be ssigned by a good garded after */
    Guarded();

    ~Guarded(){};
    void destroy(){};
  };

class TheoryRewriteRules : public Theory {
private:
  /** list of all rewrite rules */
  /* std::vector< Node > d_rules; */
  // typedef std::vector< std::pair<Node, Trigger > > Rules;
  typedef context::CDList< RewriteRule > Rules;
  Rules d_rules;
  typedef context::CDList< RuleInst > RuleInsts;
  RuleInsts d_ruleinsts;

  /** The GList* will not lead too memory leaks since that use
      ContextMemoryAllocator */
  typedef context::CDList< Guarded > GList;
  typedef context::CDHashMap<Node, GList *, NodeHashFunction> GuardedMap;
  GuardedMap d_guardeds;

  /* In order to not monopolize, the system slow down himself: If a
     guard stored in d_guardeds become true or false, it waits
     checkSlowdown(=10) checks before checking again if some guard take a
     value. At FULL_EFFORT regardless of d_checkLevel it check the
     guards
   */
  context::CDO<size_t> d_checkLevel;

  /** explanation */
  typedef context::CDHashMap<Node, RuleInstId , NodeHashFunction> ExplanationMap;
  ExplanationMap d_explanations;

  /** new instantiation */
  typedef context::CDQueue< RuleInst > QRuleInsts;
  QRuleInsts d_ruleinsts_to_add;

 public:
  /** true for predicate */
  Node d_true;

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryRewriteRules(context::Context* c,
               context::UserContext* u,
               OutputChannel& out,
                     Valuation valuation,
                     QuantifiersEngine* qe);
  ~TheoryRewriteRules(){}

  /** Usual function for theories */
  void check(Theory::Effort e);
  Node explain(TNode n);
  void notifyEq(TNode lhs, TNode rhs);
  std::string identify() const {
    return "THEORY_REWRITERULES";
  }

 private:
  void registerQuantifier( Node n );

 public:
  /* TODO modify when notification will be available */
  void notification( Node n, bool b);

  Trigger createTrigger( TNode n, std::vector<Node> & pattern )const;

  /** return if the guard (already substituted) is known true or false
      or unknown. In the last case it add the Guarded(rid,gid) to the watch
      list of this guard */
  Answer addWatchIfDontKnow(Node g, const RuleInstId rid, const size_t gid);

  /** An instantiation of a rule is fired (all guards true) we
      propagate the body. That can be done by theory propagation if
      possible or by lemmas.
   */
  void propagateRule(const RuleInst & r);

  /** access */
  const RewriteRule & get_rule(const RewriteRuleId r)const{return d_rules[r];};
  const RuleInst & get_inst(const RuleInstId r)const{return d_ruleinsts[r];};

  /** Auxillary functions */
private:
  /** A guard is verify, notify the Guarded */
  void notification(GList * const lpropa, bool b);
  /* If two guards becomes equals we should notify if one of them is
     already true */
  bool notifyIfKnown(const GList * const ltested, GList * const lpropa);
  Node substGuards(const RuleInst & inst,const RewriteRule & r,
                   Node last = Node::null());

  RewriteRule const makeRewriteRule(const Node r);
  void computeMatchBody ( RewriteRule & r,
                          const RewriteRuleId rid_begin);
  void addMatchRuleTrigger(const RewriteRuleId rid,
                           const RewriteRule & r,
                           InstMatch & im, bool delay = true);


};/* class TheoryRewriteRules */

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H */

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

#ifndef __CVC4__REWRITE_ENGINE_H
#define __CVC4__REWRITE_ENGINE_H

#include "context/cdlist.h"
#include "theory/valuation.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include <memory>

namespace CVC4 {
namespace theory {
namespace quantifiers {

typedef size_t RewriteRuleId;
typedef size_t RuleInstId;

  enum Answer {ATRUE, AFALSE, ADONTKNOW};

  class RewriteRule{
  public:
    Trigger trigger;
    std::vector<Node> guards;
    const Node equality;
    std::vector<Node> & free_vars; /* free variable in the rule */
    std::vector<Node> & inst_vars; /* corresponding vars in the triggers */

    RewriteRule(RewriteEngine & re,
                Trigger & tr, Node g, Node eq,
                std::vector<Node> & fv,std::vector<Node> & iv);
    bool noGuard()const;
  };

  class RuleInst{
  public:
    /** The rule has at least one guard */
    const RewriteRuleId rule;

    /** The id of the Rule inst */
    const RuleInstId id;

    /** the substitution */
    std::vector<Node> subst;

    /** the start used guarded created */
    size_t start;

    /** Rule an instantiation with the given match */
    RuleInst(RewriteEngine & re, const RewriteRuleId rule,
             InstMatch & im, const RuleInstId i);
    Node substNode(const RewriteEngine & re, TNode r)const;
    size_t findGuard(RewriteEngine & re, size_t start)const;
    bool startedTrue(const RewriteEngine & re)const;
  };

/** A pair? */
  class Guarded {
  public:
    /** The backtracking is done somewhere else */
    size_t d_guard; /* the id of the guard */

    /** The shared instantiation data */
    RuleInstId inst;

    void nextGuard(RewriteEngine & re)const;

    /** start indicate the first guard which is not true */
    Guarded(const RuleInstId ri, const size_t start);
    Guarded(const Guarded & g);
    /** Should be ssigned by a good garded after */
    Guarded();

    ~Guarded(){};
    void destroy(){};
  };

  class RewriteEngine : public QuantifiersModule
{
private:
  TheoryQuantifiers* d_th;
  /** list of all rewrite rules */
  /* std::vector< Node > d_rules; */
  // typedef std::vector< std::pair<Node, Trigger > > Rules;
  typedef context::CDList< RewriteRule > Rules;
  Rules d_rules;
  typedef context::CDList< RuleInst > RuleInsts;
  RuleInsts d_ruleinsts;

  /** The GList* will not lead too memory leaks since that use
      ContextMemoryAllocator */
  typedef context::CDList<Guarded, context::ContextMemoryAllocator<Guarded> > GList;
  typedef context::CDMap<Node, GList*, NodeHashFunction> GuardedMap;
  GuardedMap d_guardeds;

  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;


  /** explanation */
  typedef context::CDMap<Node, RuleInstId , NodeHashFunction> ExplanationMap;
  ExplanationMap d_explanations;

 public:
  /** true for predicate */
  Node d_true;

  /** Access for some Tools */
  QuantifiersEngine * qe;
  uf::TheoryUF* uf;

  RewriteEngine(context::Context* c, TheoryQuantifiers* th );
  ~RewriteEngine(){}

  /** Usual function for theories */
  void check( Theory::Effort e );
  void registerQuantifier( Node n );
  void assertNode( Node n );
  Node explain(TNode n);
  void notifyEq(TNode lhs, TNode rhs);

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

  /** bad friend can be added directly in RewriteRule */
  std::vector<Node> & d_vars(TNode r){return qe->d_vars[r];};
  std::vector<Node> & d_inst_constants(TNode r)
    {return qe->d_inst_constants[r];};

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
  Node substGuards(const RuleInst & inst,const RewriteRule & r);

}; /* Class RewriteEngine */
}
}
}

#endif

/*********************                                                        */
/*! \file quantifiers_engine.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters, bobot
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory instantiator, Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS_ENGINE_H
#define __CVC4__THEORY__QUANTIFIERS_ENGINE_H

#include "theory/theory.h"
#include "util/hash.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/rewriterules/rr_inst_match.h"
#include "theory/quantifiers/quant_util.h"

#include "util/statistics_registry.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {

class TheoryEngine;

namespace theory {

class QuantifiersEngine;

class QuantifiersModule {
protected:
  QuantifiersEngine* d_quantEngine;
public:
  QuantifiersModule( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  virtual ~QuantifiersModule(){}
  //get quantifiers engine
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
  /* whether this module needs to check this round */
  virtual bool needsCheck( Theory::Effort e ) { return e>=Theory::EFFORT_LAST_CALL; }
  /* Call during quantifier engine's check */
  virtual void check( Theory::Effort e ) = 0;
  /* Called for new quantifiers */
  virtual void registerQuantifier( Node n ) = 0;
  virtual void assertNode( Node n ) = 0;
  virtual void propagate( Theory::Effort level ){}
  virtual Node getNextDecisionRequest() { return TNode::null(); }
  virtual Node explain(TNode n) = 0;
};/* class QuantifiersModule */

namespace quantifiers {
  class InstantiationEngine;
  class ModelEngine;
  class TermDb;
  class FirstOrderModel;
}/* CVC4::theory::quantifiers */

namespace inst {
  class TriggerTrie;
}/* CVC4::theory::inst */

class EfficientEMatcher;
class EqualityQueryQuantifiersEngine;

class QuantifiersEngine {
  friend class quantifiers::InstantiationEngine;
  friend class quantifiers::ModelEngine;
  friend class inst::InstMatch;
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** reference to theory engine object */
  TheoryEngine* d_te;
  /** vector of modules for quantifiers */
  std::vector< QuantifiersModule* > d_modules;
  /** instantiation engine */
  quantifiers::InstantiationEngine* d_inst_engine;
  /** model engine */
  quantifiers::ModelEngine* d_model_engine;
  /** equality query class */
  EqualityQueryQuantifiersEngine* d_eq_query;
  /** for computing relevance of quantifiers */
  QuantRelevance d_quant_rel;
  /** phase requirements for each quantifier for each instantiation literal */
  std::map< Node, QuantPhaseReq* > d_phase_reqs;
  /** efficient e-matcher */
  EfficientEMatcher* d_eem;
private:
  /** list of all quantifiers seen */
  std::vector< Node > d_quants;
  /** quantifiers that have been skolemized */
  std::map< Node, bool > d_skolemized;
  /** list of all lemmas produced */
  std::map< Node, bool > d_lemmas_produced;
  /** lemmas waiting */
  std::vector< Node > d_lemmas_waiting;
  /** has added lemma this round */
  bool d_hasAddedLemma;
  /** list of all instantiations produced for each quantifier */
  std::map< Node, inst::InstMatchTrie > d_inst_match_trie;
  /** term database */
  quantifiers::TermDb* d_term_db;
  /** all triggers will be stored in this trie */
  inst::TriggerTrie* d_tr_trie;
  /** extended model object */
  quantifiers::FirstOrderModel* d_model;
private:
  KEEP_STATISTIC(TimerStat, d_time, "theory::QuantifiersEngine::time");
public:
  QuantifiersEngine(context::Context* c, TheoryEngine* te);
  ~QuantifiersEngine();
  /** get instantiator for id */
  Instantiator* getInstantiator( theory::TheoryId id );
  /** get theory engine */
  TheoryEngine* getTheoryEngine() { return d_te; }
  /** get equality query object for the given type. The default is the
      generic one */
  EqualityQuery* getEqualityQuery();
  /** get instantiation engine */
  quantifiers::InstantiationEngine* getInstantiationEngine() { return d_inst_engine; }
  /** get model engine */
  quantifiers::ModelEngine* getModelEngine() { return d_model_engine; }
  /** get default sat context for quantifiers engine */
  context::Context* getSatContext();
  /** get default output channel for the quantifiers engine */
  OutputChannel& getOutputChannel();
  /** get default valuation for the quantifiers engine */
  Valuation& getValuation();
  /** get quantifier relevance */
  QuantRelevance* getQuantifierRelevance() { return &d_quant_rel; }
  /** get phase requirement information */
  QuantPhaseReq* getPhaseRequirements( Node f ) { return d_phase_reqs.find( f )==d_phase_reqs.end() ? NULL : d_phase_reqs[f]; }
  /** get phase requirement terms */
  void getPhaseReqTerms( Node f, std::vector< Node >& nodes );
  /** get efficient e-matching utility */
  EfficientEMatcher* getEfficientEMatcher() { return d_eem; }
public:
  /** check at level */
  void check( Theory::Effort e );
  /** register quantifier */
  void registerQuantifier( Node f );
  /** register quantifier */
  void registerPattern( std::vector<Node> & pattern);
  /** make an assertion */
  void assertFact( Node n );
  /** propagate */
  void propagate( Theory::Effort level );
  /** get next decision request */
  Node getNextDecisionRequest();
private:
  /** compute term vector */
  void computeTermVector( Node f, InstMatch& m, std::vector< Node >& vars, std::vector< Node >& terms );
  /** instantiate f with arguments terms */
  bool addInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms );
  /** set instantiation level attr */
  void setInstantiationLevelAttr( Node n, uint64_t level );
public:
  /** get instantiation */
  Node getInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms );
  /** get instantiation */
  Node getInstantiation( Node f, InstMatch& m );
  /** exist instantiation ? */
  bool existsInstantiation( Node f, InstMatch& m, bool modEq = true, bool modInst = false );
  /** add lemma lem */
  bool addLemma( Node lem );
  /** do instantiation specified by m */
  bool addInstantiation( Node f, InstMatch& m, bool modEq = true, bool modInst = false, bool mkRep = true );
  /** split on node n */
  bool addSplit( Node n, bool reqPhase = false, bool reqPhasePol = true );
  /** add split equality */
  bool addSplitEquality( Node n1, Node n2, bool reqPhase = false, bool reqPhasePol = true );
  /** has added lemma */
  bool hasAddedLemma() { return !d_lemmas_waiting.empty() || d_hasAddedLemma; }
  /** flush lemmas */
  void flushLemmas( OutputChannel* out );
  /** get number of waiting lemmas */
  int getNumLemmasWaiting() { return (int)d_lemmas_waiting.size(); }
public:
  /** get number of quantifiers */
  int getNumQuantifiers() { return (int)d_quants.size(); }
  /** get quantifier */
  Node getQuantifier( int i ) { return d_quants[i]; }
public:
  /** get model */
  quantifiers::FirstOrderModel* getModel() { return d_model; }
  /** get term database */
  quantifiers::TermDb* getTermDatabase() { return d_term_db; }
  /** get trigger database */
  inst::TriggerTrie* getTriggerDatabase() { return d_tr_trie; }
  /** add term to database */
  void addTermToDatabase( Node n, bool withinQuant = false );
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_num_quant;
    IntStat d_instantiation_rounds;
    IntStat d_instantiation_rounds_lc;
    IntStat d_instantiations;
    IntStat d_max_instantiation_level;
    IntStat d_splits;
    IntStat d_total_inst_var;
    IntStat d_total_inst_var_unspec;
    IntStat d_inst_unspec;
    IntStat d_inst_duplicate;
    IntStat d_lit_phase_req;
    IntStat d_lit_phase_nreq;
    IntStat d_triggers;
    IntStat d_simple_triggers;
    IntStat d_multi_triggers;
    IntStat d_multi_trigger_instantiations;
    IntStat d_term_in_termdb;
    IntStat d_num_mono_candidates;
    IntStat d_num_mono_candidates_new_term;
    IntStat d_num_multi_candidates;
    IntStat d_mono_candidates_cache_hit;
    IntStat d_mono_candidates_cache_miss;
    IntStat d_multi_candidates_cache_hit;
    IntStat d_multi_candidates_cache_miss;
    Statistics();
    ~Statistics();
  };/* class QuantifiersEngine::Statistics */
  Statistics d_statistics;
public:
  /** options */
  bool d_optInstCheckDuplicate;
  bool d_optInstMakeRepresentative;
  bool d_optInstAddSplits;
  bool d_optMatchIgnoreModelBasis;
  bool d_optInstLimitActive;
  int d_optInstLimit;

private:
  //notification class for equality engine
  class NotifyClass : public eq::EqualityEngineNotify {
    QuantifiersEngine& d_qe;
  public:
    NotifyClass(QuantifiersEngine& qe): d_qe(qe) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) { return true; }
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) { return true; }
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) { return true; }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {}
    void eqNotifyNewClass(TNode t) { d_qe.eqNotifyNewClass(t); }
    void eqNotifyPreMerge(TNode t1, TNode t2) { d_qe.eqNotifyPreMerge(t1, t2); }
    void eqNotifyPostMerge(TNode t1, TNode t2) { d_qe.eqNotifyPostMerge(t1, t2); }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { d_qe.eqNotifyDisequal(t1, t2, reason); }
  };/* class QuantifiersEngine::NotifyClass */
private:
  /** The notify class */
  NotifyClass d_notify;
  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;
public:
  void eqNotifyNewClass(TNode t);
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  eq::EqualityEngine* getEqualityEngine() { return &d_equalityEngine; }
};/* class QuantifiersEngine */



/** equality query object using theory engine */
class EqualityQueryQuantifiersEngine : public EqualityQuery
{
private:
  /** pointer to theory engine */
  QuantifiersEngine* d_qe;
  /** internal representatives */
  std::map< Node, Node > d_int_rep;
  /** rep score */
  std::map< Node, int > d_rep_score;
  /** reset count */
  int d_reset_count;
private:
  /** node contains */
  Node getInstance( Node n, std::vector< Node >& eqc );
  /** get score */
  int getRepScore( Node n );
public:
  EqualityQueryQuantifiersEngine( QuantifiersEngine* qe ) : d_qe( qe ), d_reset_count( 0 ){}
  ~EqualityQueryQuantifiersEngine(){}
  /** reset */
  void reset();
  /** general queries about equality */
  bool hasTerm( Node a );
  Node getRepresentative( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  eq::EqualityEngine* getEngine();
  void getEquivalenceClass( Node a, std::vector< Node >& eqc );
  /** getInternalRepresentative gets the current best representative in the equivalence class of a, based on some criteria.
      If cbqi is active, this will return a term in the equivalence class of "a" that does
      not contain instantiation constants, if such a term exists.
   */
  Node getInternalRepresentative( Node a );
}; /* EqualityQueryQuantifiersEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS_ENGINE_H */

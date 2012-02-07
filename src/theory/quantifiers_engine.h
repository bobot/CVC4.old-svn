/*********************                                                        */
/*! \file quantifiers_engine.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory instantiator, Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_ENGINE_H
#define __CVC4__QUANTIFIERS_ENGINE_H

#include "theory/theory.h"
#include "util/hash.h"
#include "theory/inst_match.h"

#include "util/stats.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {

class TheoryEngine;
class SmtEngine;

// attribute for "contains instantiation constants from"
struct InstConstantAttributeId {};
typedef expr::Attribute<InstConstantAttributeId, Node> InstConstantAttribute;

struct InstLevelAttributeId {};
typedef expr::Attribute<InstLevelAttributeId, uint64_t> InstLevelAttribute;

namespace theory {

class InstStrategyList;
class QuantifiersEngine;

class InstStrategy
{
public:
  enum Status {
    STATUS_UNFINISHED,
    STATUS_UNKNOWN,
    STATUS_SAT,
  };/* enum Effort */
protected:
  /** reference to the instantiation engine */
  QuantifiersEngine* d_quantEngine;
public:
  InstStrategy( QuantifiersEngine* ie ) : d_quantEngine( ie ){}
  virtual ~InstStrategy(){}

  /** reset instantiation */
  virtual void resetInstantiationRound(){}
  /** process method */
  virtual int process( Node f, int effort ){ return STATUS_UNKNOWN; }
  /** update status */
  static void updateStatus( int& currStatus, int addStatus ){
    if( addStatus==STATUS_UNFINISHED ){
      currStatus = STATUS_UNFINISHED;
    }else if( addStatus==STATUS_UNKNOWN ){
      if( currStatus==STATUS_SAT ){
        currStatus = STATUS_UNKNOWN;
      }
    }
  }
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }
};

class Instantiator{
  friend class QuantifiersEngine;
private:
  /** status */
  int d_status;
protected:
  /** reference to the instantiation engine */
  QuantifiersEngine* d_quantEngine;
  /** reference to the theory that it looks at */
  Theory* d_th;
  /** instantiation strategies */
  std::vector< InstStrategy* > d_instStrategies;
  /** instantiation strategies active */
  std::map< InstStrategy*, bool > d_instStrategyActive;
  /** has constraints from quantifier */
  std::map< Node, bool > d_hasConstraints;
  /** is instantiation strategy active */
  bool isActiveStrategy( InstStrategy* is ) { 
    return d_instStrategyActive.find( is )!=d_instStrategyActive.end() && d_instStrategyActive[is];
  }
  /** add inst strategy */
  void addInstStrategy( InstStrategy* is ){
    d_instStrategies.push_back( is );
    d_instStrategyActive[is] = true;
  }
public:
  /** reset instantiation strategies */
  virtual void resetInstantiationStrategies();
  /** reset instantiation round */
  virtual void resetInstantiationRound(){}
  /** set has constraints from quantifier f */
  void setHasConstraintsFrom( Node f );
  /** has constraints from */
  bool hasConstraintsFrom( Node f );
  /** is full owner of quantifier f? */
  bool isOwnerOf( Node f );
  /** process quantifier */
  virtual int process( Node f, int effort ) { return InstStrategy::STATUS_SAT; }
public:
  Instantiator(context::Context* c, QuantifiersEngine* qe, Theory* th);
  ~Instantiator();

  /** get corresponding theory for this instantiator */
  Theory* getTheory() { return d_th; }
  /** check function, assertion was asserted to theory */
  virtual void check( Node assertion ){}

  /** do instantiation method*/
  virtual void doInstantiation( int effort );
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }
  /** print debug information */
  virtual void debugPrint( const char* c ) {}
  /** get status */
  int getStatus() { return d_status; }
};/* class Instantiator */

class QuantifiersModule
{
public:
  QuantifiersModule(){}
  ~QuantifiersModule(){}

  virtual void check( Theory::Effort e ) = 0;
  virtual void registerQuantifier( Node n ) = 0;
  virtual void assertNode( Node n ) = 0;
};

namespace quantifiers{
  class InstantiationEngine;
  class RewriteEngine;
}

class QuantifiersEngine
{
  friend class quantifiers::InstantiationEngine;
  friend class quantifiers::RewriteEngine;
private:
  typedef context::CDMap< Node, bool, NodeHashFunction > BoolMap;
  /** reference to theory engine object */
  TheoryEngine* d_te;
  /** vector of modules for quantifiers */
  std::vector< QuantifiersModule* > d_modules;
  /** equality query class */
  EqualityQuery* d_eq_query;

  /** list of all quantifiers */
  std::vector< Node > d_quants;
  /** map from universal quantifiers to the list of variables */
  std::map< Node, std::vector< Node > > d_vars;
  /** map from universal quantifiers to the list of skolem constants */
  std::map< Node, std::vector< Node > > d_skolem_constants;
  /** map from universal quantifiers to their skolemized body */
  std::map< Node, Node > d_skolem_body;
  /** instantiation constants to universal quantifiers */
  std::map< Node, Node > d_inst_constants_map;
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** map from universal quantifiers to their counterexample body */
  std::map< Node, Node > d_counterexample_body;
  /** map from universal quantifiers to their counterexample literals */
  std::map< Node, Node > d_ce_lit;
  /** map from quantifiers to whether they are active */
  BoolMap d_active;
  /** lemmas produced */
  std::map< Node, bool > d_lemmas_produced;
  /** lemmas waiting */
  std::vector< Node > d_lemmas_waiting;
  /** phase requirements for instantiation literals */
  std::map< Node, bool > d_phase_reqs;
  /** whether a particular quantifier is clausal */
  std::map< Node, bool > d_clausal;
  /** free variable for instantiation constant */
  std::map< Node, Node > d_free_vars;
  /** owner of quantifiers */
  std::map< Node, Theory* > d_owner;
private:
  /** set instantiation level attr */
  void setInstantiationLevelAttr( Node n, uint64_t level );
  /** set instantiation constant attr */
  void setInstantiationConstantAttr( Node n, Node f );
public:
  QuantifiersEngine(context::Context* c, TheoryEngine* te);
  ~QuantifiersEngine();
  /** get instantiator for id */
  Instantiator* getInstantiator( int id );
  /** get theory engine */
  TheoryEngine* getTheoryEngine() { return d_te; }
  /** get equality query object */
  EqualityQuery* getEqualityQuery() { return d_eq_query; }
  /** set equality query object */
  void setEqualityQuery( EqualityQuery* eq ) { d_eq_query = eq; }
public:
  /** add module */
  void addModule( QuantifiersModule* qm ) { d_modules.push_back( qm ); }
  /** check at level */
  void check( Theory::Effort e );
  /** register quantifier */
  void registerQuantifier( Node f );
  /** assert (universal) quantifier */
  void assertNode( Node f );
public:
  /** add lemma lem */
  bool addLemma( Node lem );
  /** instantiate f with arguments terms */
  bool addInstantiation( Node f, std::vector< Node >& terms );
  /** do instantiation specified by m */
  bool addInstantiation( Node f, InstMatch* m, bool addSplits = false );
  /** split on node n */
  bool addSplit( Node n, bool reqPhase = false, bool reqPhasePol = true );
  /** add split equality */
  bool addSplitEquality( Node n1, Node n2, bool reqPhase = false, bool reqPhasePol = true );
  /** has added lemma */
  bool hasAddedLemma() { return !d_lemmas_waiting.empty(); }
  /** flush lemmas */
  void flushLemmas( OutputChannel* out );
public:
  /** get number of quantifiers */
  int getNumQuantifiers() { return (int)d_quants.size(); }
  /** get quantifier */
  Node getQuantifier( int i ) { return d_quants[i]; }
  /** get instantiation constants */
  void getInstantiationConstantsFor( Node f, std::vector< Node >& ics ) { 
    ics.insert( ics.begin(), d_inst_constants[f].begin(), d_inst_constants[f].end() ); 
  }
  /** get the i^th instantiation constant of f */
  Node getInstantiationConstant( Node f, int i ) { return d_inst_constants[f][i]; }
  /** get number of instantiation constants for f */
  int getNumInstantiationConstants( Node f ) { return (int)d_inst_constants[f].size(); }
public:
  /** get the ce body f[e/x] */
  Node getCounterexampleBody( Node f ) { return d_counterexample_body[ f ]; }
  /** get the corresponding counterexample literal for quantified formula node n */
  Node getCounterexampleLiteralFor( Node f ) { return d_ce_lit[ f ]; }
  /** get the skolemized body f[e/x] */
  Node getSkolemizedBody( Node f );
  /** set active */
  void setActive( Node n, bool val ) { d_active[n] = val; }
  /** get active */
  bool getActive( Node n ) { return d_active.find( n )!=d_active.end() && d_active[n]; }
  /** is phase required */
  bool isPhaseReq( Node lit ) { return d_phase_reqs.find( lit )!=d_phase_reqs.end(); }
  /** get phase requirement */
  bool getPhaseReq( Node lit ) { return d_phase_reqs.find( lit )==d_phase_reqs.end() ? false : d_phase_reqs[ lit ]; }
public:
  /** returns node n with bound vars of f replaced by instantiation constants of f */
  Node getSubstitutedNode( Node n, Node f );
  /** get free variable for instantiation constant */
  Node getFreeVariableForInstConstant( Node n );
public:
  /** has owner */
  bool hasOwner( Node f ) { return d_owner.find( f )!=d_owner.end(); }
  /** get owner */
  Theory* getOwner( Node f ) { return d_owner[f]; }
  /** set owner */
  void setOwner( Node f, Theory* t ) { d_owner[f] = t; }
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_instantiation_rounds;
    IntStat d_instantiations;
    IntStat d_max_instantiation_level;
    IntStat d_splits;
    IntStat d_total_inst_var;
    IntStat d_total_inst_var_unspec;
    IntStat d_inst_unspec;
    IntStat d_inst_duplicate;
    IntStat d_lit_phase_req;
    IntStat d_lit_phase_nreq;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};/* class QuantifiersEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

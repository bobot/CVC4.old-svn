/*********************                                                        */
/*! \file instantiation_engine.h
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

#ifndef __CVC4__INSTANTIATION_ENGINE_H
#define __CVC4__INSTANTIATION_ENGINE_H

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
class InstantiationEngine;

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
  InstantiationEngine* d_instEngine;
public:
  InstStrategy( InstantiationEngine* ie ) : d_instEngine( ie ){}
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
  friend class InstantiationEngine;
private:
  /** status */
  int d_status;
protected:
  /** reference to the instantiation engine */
  InstantiationEngine* d_instEngine;
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
  Instantiator(context::Context* c, InstantiationEngine* ie, Theory* th);
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

class InstantiatorDefault;
namespace uf {
  class InstantiatorTheoryUf;
}
namespace arith {
  class InstantiatorTheoryArith;
}

class InstantiationEngine
{
  friend class Instantiator;
  friend class ::CVC4::TheoryEngine;
  friend class uf::InstantiatorTheoryUf;
  friend class arith::InstantiatorTheoryArith;
  friend class QuantMatchGenerator;
private:
  typedef context::CDMap< Node, bool, NodeHashFunction > BoolMap;
  /** theory instantiator objects for each theory */
  theory::Instantiator* d_instTable[theory::THEORY_LAST];
  /** reference to theory engine object */
  TheoryEngine* d_te;
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
  /** is clausal */
  std::map< Node, bool > d_is_clausal;
  /** map from quantifiers to whether they are active */
  BoolMap d_active;
  /** lemmas produced */
  std::map< Node, bool > d_lemmas_produced;
  /** lemmas waiting */
  std::vector< Node > d_lemmas_waiting;
  /** status */
  int d_status;
  /** phase requirements for instantiation literals */
  std::map< Node, bool > d_phase_reqs;
  /** whether a particular quantifier is clausal */
  std::map< Node, bool > d_clausal;
  /** free variable for instantiation constant */
  std::map< Node, Node > d_free_vars;
  /** equality query class */
  EqualityQuery* d_eq_query;

  /** owner of quantifiers */
  std::map< Node, Theory* > d_owner;
  /** set instantiation level */
  void setInstantiationLevel( Node n, uint64_t level );
public:
  InstantiationEngine(context::Context* c, TheoryEngine* te);
  ~InstantiationEngine();
  
  theory::Instantiator* getInstantiator( Theory* t ) { return d_instTable[t->getId()]; }
  TheoryEngine* getTheoryEngine() { return d_te; }

  /** register quantifier */
  void registerQuantifier( Node f, OutputChannel* out, Valuation& valuation );
  /** register term, f is the quantifier it belongs to */
  void registerTerm( Node n, Node f, OutputChannel* out );
  /** compute phase requirements */
  void computePhaseReqs( Node n, bool polarity );
  /** do a round of instantiation */
  bool doInstantiationRound( OutputChannel* out );

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

  /** get the ce body f[e/x] */
  Node getCounterexampleBody( Node f ) { return d_counterexample_body[ f ]; }
  /** get the skolemized body f[e/x] */
  Node getSkolemizedBody( Node f );
  /** get the quantified variables for quantifier f */
  void getVariablesFor( Node f, std::vector< Node >& vars );
  /** get instantiation constants */
  void getInstantiationConstantsFor( Node f, std::vector< Node >& ics ) { 
    ics.insert( ics.begin(), d_inst_constants[f].begin(), d_inst_constants[f].end() ); 
  }
  /** get the i^th instantiation constant of f */
  Node getInstantiationConstant( Node f, int i ) { return d_inst_constants[f][i]; }
  /** get number of instantiation constants for f */
  int getNumInstantiationConstants( Node f ) { return (int)d_inst_constants[f].size(); }

  /** get the corresponding counterexample literal for quantified formula node n */
  Node getCounterexampleLiteralFor( Node f ) { return d_ce_lit[ f ]; }
  /** set active */
  void setActive( Node n, bool val ) { d_active[n] = val; }
  /** get active */
  bool getActive( Node n ) { return d_active[n]; }
  /** get status */
  int getStatus() { return d_status; }
  /** is phase required */
  bool isPhaseReq( Node lit ) { return d_phase_reqs.find( lit )!=d_phase_reqs.end(); }
  /** get phase requirement */
  bool getPhaseReq( Node lit ) { return d_phase_reqs.find( lit )==d_phase_reqs.end() ? false : d_phase_reqs[ lit ]; }
  /** has added lemma */
  bool hasAddedLemma() { return !d_lemmas_waiting.empty(); }

  /** get free variable for instantiation constant */
  Node getFreeVariableForInstConstant( Node n );
  /** get equality query object */
  EqualityQuery* getEqualityQuery() { return d_eq_query; }

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
  /** has instantiated */
  std::map< Node, bool > d_hasInstantiated;

};/* class InstantiationEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

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

class InstantiationEngine;

class Instantiator{
  friend class InstantiationEngine;
protected:
  /** status */
  int d_status;
  /** quant status */
  int d_quantStatus;
  /** reference to the instantiation engine */
  InstantiationEngine* d_instEngine;
  /** reference to the theory that it looks at */
  Theory* d_th;

  /** has constraints from quantifier */
  std::map< Node, bool > d_hasConstraints;
  /** process quantifier */
  virtual void process( Node f, int effort ) {}
public:
  enum Status {
    STATUS_UNFINISHED,
    STATUS_UNKNOWN,
    STATUS_SAT,
  };/* enum Effort */
public:
  Instantiator(context::Context* c, InstantiationEngine* ie, Theory* th);
  ~Instantiator();

  /** get corresponding theory for this instantiator */
  Theory* getTheory() { return d_th; }
  /** check function, assertion was asserted to theory */
  virtual void check( Node assertion ){}

  /** reset instantiation */
  virtual void resetInstantiationRound() { d_status = STATUS_UNFINISHED; }
  /** do instantiation method*/
  virtual void doInstantiation( int effort );
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }
  /** print debug information */
  virtual void debugPrint( const char* c ) {}

  /** get status */
  int getStatus() { return d_status; }
  /** update status */
  static void updateStatus( int& currStatus, int addStatus );
  /** set has constraints from quantifier f */
  void setHasConstraintsFrom( Node f );
  /** has constraints from */
  bool hasConstraintsFrom( Node f );
  /** is full owner of quantifier f? */
  bool isOwnerOf( Node f );
};/* class Instantiator */


/** 
This class provides a simple way of matching pattern terms with ground terms, without considering equality 
*/
class TermMatchEngine 
{
private:
  /** reference to the instantiation engine */
  InstantiationEngine* d_instEngine;
  /** process match */
  void processMatch( Node pat, Node g );
  //patterns vs. ground terms, their matches
  std::map< Node, bool > d_patterns;
  std::map< Node, bool > d_ground_terms;
  std::map< Node, std::map< Node, InstMatchGenerator* > > d_matches;
public:
  TermMatchEngine(){}
  TermMatchEngine( InstantiationEngine* ie ){}
  ~TermMatchEngine(){}
  /** register that we wish to consider all subterms of n */
  void registerTerm( Node n );
  /** get a match generator for producing unified matches for each (pattern) node in nodes */
  InstMatchGenerator* makeMatchGenerator( std::vector< Node >& nodes );
};


/** 
QuantMatchGenerator:  This class encapsulates all information needed for producing matches 
for a particular quantifier.  Can have the following uses for QuantMatchGenerator qmg:

For user-provided patterns do this:

int index = qmg.addUserPattern( pat ); //where pat.getKind()==INST_PATTERN
qmg.resetInstantiationRound();
while( qmg.getNextMatch( index ) ){
  InstMatch* m = qmg.getCurrent( index );
  //...
}

For automated trigger generation do this:

qmg.resetInstantiationRound();
qmg.initializePatternTerms( ... ); //can be either default or explicitly provided
while( qmg.getNextMatch() ){
  InstMatch* m = qmg.getCurrent();
  //...
}

*/
class QuantMatchGenerator 
{
private:
  //a collect of nodes representing a trigger
  class Trigger {
  private:
    /** computation of variable contains */
    static std::map< Node, std::vector< Node > > d_var_contains;
    static void computeVarContains( Node n ) { computeVarContains2( n, n ); }
    static void computeVarContains2( Node n, Node parent );
    std::vector< Node > d_nodes;
    std::map< Node, bool > d_vars;
  public:
    bool addNode( Node n );
    int getNumNodes() { return (int)d_nodes.size(); }
    Node getNode( int i ) { return d_nodes[i]; }
    void clear() { 
      d_nodes.clear();
      d_vars.clear();
    }
    bool isComplete( Node f ){ return d_vars.size()==f[0].getNumChildren(); }
    void debugPrint( const char* c );
  };
  /** reference to the instantiation engine */
  InstantiationEngine* d_instEngine;
  /** quantifier we are producing matches for */
  Node d_f;
  /** explicitly provided patterns */
  std::vector< InstMatchGenerator* > d_user_gen;

  /** a (set of) match generators produced by automated trigger generation */
  std::vector< InstMatchGenerator* > d_match_gen;
  int d_index;
  /** functions for producing the generators */
  bool hasCurrentGenerator( bool allowMakeNext = true );
  InstMatchGenerator* getNextGenerator();
  InstMatchGenerator* getCurrentGenerator() { return d_match_gen[d_index]; }
  /** collection of pattern terms */
  std::vector< Node > d_patTerms;
  void addPatTerm( Node n );
  void collectPatTerms( Node n );
  void decomposePatTerm( Node n );
  /** map from pattern terms to the inst match generator for them */
  std::map< Node, InstMatchGenerator* > d_img_map;
  /** current trigger information */
  Trigger d_currTrigger;
  /** whether to produce (another) trigger */
  bool d_produceTrigger;
public:
  QuantMatchGenerator( InstantiationEngine* ie, Node f ) : 
    d_instEngine( ie ), d_f( f ), d_index( 0 ), d_produceTrigger( true ){}
  ~QuantMatchGenerator(){}
  /** this must be called before initialization/getting any matches */
  void resetInstantiationRound();
public:
  /** add pattern */
  int addUserPattern( Node pat );
  /** get num patterns */
  int getNumUserPatterns() { return (int)d_user_gen.size(); }
public:
  /** initialize pattern terms */
  void initializePatternTerms();
  void initializePatternTerms( std::vector< Node >& patTerms );
  /** get number of triggers currently produced */
  int getNumTriggersProduced() { return d_index; }
public:
  /** clear matches (reproduce the matches) */
  void clearMatches( int pat = -1 );
  /** reset this generator (start the iterator from the beginning) */
  void reset( int pat = -1 );
  /** get current match */
  InstMatch* getCurrent( int pat = -1 );
  /** get next match */
  bool getNextMatch( int pat = -1, int triggerThresh = -1 );
};

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
  friend class InstantiatorDefault;
  friend class uf::InstantiatorTheoryUf;
  friend class arith::InstantiatorTheoryArith;
  friend class InstMatch;
  friend class TermMatchEngine;
  friend class QuantMatchGenerator;
private:
  typedef context::CDMap< Node, bool, NodeHashFunction > BoolMap;

  /** current output */
  OutputChannel* d_curr_out;
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
  std::map< Node, Node > d_counterexamples;
  /** is clausal */
  std::map< Node, bool > d_is_clausal;
  /** map from quantifiers to whether they are active */
  BoolMap d_active;
  /** map from instantiation constants to whether they are active */
  BoolMap d_ic_active;
  /** lemmas produced */
  std::map< Node, bool > d_lemmas_produced;
  /** status */
  int d_status;
  /** whether a lemma has been added */
  bool d_addedLemma;
  /** phase requirements for instantiation literals */
  std::map< Node, bool > d_phase_reqs;
  /** whether a particular quantifier is clausal */
  std::map< Node, bool > d_clausal;
  /** term match engine */
  TermMatchEngine d_tme;
  /** quantifier match generators */
  std::map< Node, QuantMatchGenerator* > d_qmg;

  /** owner of quantifiers */
  std::map< Node, Theory* > d_owner;
  /** instantiation queue */
  std::map< Node, std::map< Instantiator*, InstMatchGroup > > d_instQueue;
  /** add partial instantiation specified by m */
  bool addPartialInstantiation( InstMatch& m, Instantiator* i );
  /** process partial instantiations */
  void processPartialInstantiations();
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
  bool addInstantiation( InstMatch* m, bool addSplits = false );
  /** split on node n */
  bool addSplit( Node n, bool reqPhase = false, bool reqPhasePol = true );
  /** add split equality */
  bool addSplitEquality( Node n1, Node n2, bool reqPhase = false, bool reqPhasePol = true );

  /** get the ce body f[e/x] */
  Node getCounterexampleBody( Node f );// { return d_counterexample_body[ f ]; }
  /** get the skolemized body f[e/x] */
  Node getSkolemizedBody( Node f );
  /** get the quantified variables for quantifier f */
  void getVariablesFor( Node f, std::vector< Node >& vars );

  /** get the corresponding counterexample literal for quantified formula node n */
  Node getCounterexampleLiteralFor( Node f );// { return d_counterexamples[n]; }
  /** set active */
  void setActive( Node n, bool val ) { d_active[n] = val; }
  /** get active */
  bool getActive( Node n ) { return d_active[n]; }
  /** get status */
  int getStatus() { return d_status; }
  /** has added lemma */
  bool hasAddedLemma() { return d_addedLemma; }

  class Statistics {
  public:
    IntStat d_instantiation_rounds;
    IntStat d_instantiations;
    IntStat d_max_instantiation_level;
    IntStat d_splits;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;

};/* class InstantiationEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

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
  virtual void resetInstantiation() { d_status = STATUS_UNFINISHED; }
  /** do instantiation method*/
  virtual void doInstantiation( int effort );
  /** process quantifier */
  virtual void process( Node f, int effort ) {}
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

class TermMatchEngine 
{
private:
  void processMatch( Node pat, Node g );
public:
  TermMatchEngine(){}
  ~TermMatchEngine(){}

  //patterns vs. ground terms, their matches
  std::map< Node, bool > d_patterns;
  std::map< Node, bool > d_ground_terms;
  std::map< Node, std::map< Node, InstMatchGenerator* > > d_matches;
  void registerTerm( Node n );

  InstMatchGenerator* makeMultiPattern( std::vector< Node >& nodes );
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
  /** instantiation constants to universal quantifiers */
  std::map< Node, Node > d_inst_constants_map;
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** map from universal quantifiers to their counterexample literals */
  std::map< Node, Node > d_counterexamples;
  /** map from universal quantifiers to their counterexample body */
  std::map< Node, Node > d_counterexample_body;
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
  /** term match engine */
  TermMatchEngine d_tme;

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

  /** get the ce body ~f[e/x] */
  Node getCounterexampleBody( Node f );
  /** get the skolem constants for quantifier f */
  void getSkolemConstantsFor( Node f, std::vector< Node >& scs );
  /** get the quantified variables for quantifier f */
  void getVariablesFor( Node f, std::vector< Node >& vars );
  /** do a round of instantiation */
  bool doInstantiation( OutputChannel* out );

  /** get the corresponding counterexample literal for quantified formula node n */
  Node getCounterexampleLiteralFor( Node n );
  /** set corresponding counterexample literal for quantified formula node n */
  void setCounterexampleLiteralFor( Node n, Node l );
  /** mark literals as dependent */
  void registerLiterals( Node n, Node f, OutputChannel* out, bool polarity = false, bool reqPol = false );
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

  void registerTerm( Node n ) { d_tme.registerTerm( n ); }

};/* class InstantiationEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

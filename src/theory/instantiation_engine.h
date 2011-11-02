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

class InstMatch
{
public:
  std::map< Node, Node > d_map;
  std::vector< Node > d_vars;
  std::vector< Node > d_match;
  bool d_computeVec;
  std::map< Node, Node > d_splits;

  InstMatch(){}
  InstMatch( Node f, InstantiationEngine* ie );
  InstMatch( InstMatch* m );

  /** fill all unfilled values with m */
  virtual bool add( InstMatch& m );
  /** if compatible, fill all unfilled values with m and return true 
      return false otherwise */
  virtual bool merge( InstMatch& m, bool allowSplit = false );
  /** -1 : keep this, 1 : keep m, 0 : keep both */
  virtual int checkSubsume( InstMatch& m );
  /** return if d_maps are equivalent */
  virtual bool isEqual( InstMatch& m );
  /** debug print method */
  virtual void debugPrint( const char* c );
  /** set the match of v to m */
  void setMatch( Node v, Node m ){
    d_map[v] = m;
    d_computeVec = true;
  }
  /** mbase is used if no value given in d_map */
  bool isComplete( InstMatch* mbase = NULL );
  /** compute d_match */
  void computeTermVec();
  /** make substitution for Node */
  Node substitute( Node n ){
    computeTermVec();
    return n.substitute( d_vars.begin(), d_vars.end(), d_match.begin(), d_match.end() ); 
  }
  /** get associated quantifier */
  Node getQuantifier() { return d_vars[0].getAttribute(InstConstantAttribute()); }
  /** add split */
  void addSplit( Node n1, Node n2 );
};

class InstMatchGroup
{
public:
  InstMatchGroup(){}
  InstMatchGroup( InstMatchGroup* mg ){
    add( *mg );
  }
  InstMatchGroup( std::vector< InstMatchGroup* >& mgg ){
    for( int i=0; i<(int)mgg.size(); i++ ){
      add( *mgg[i] );
    }
  }
  ~InstMatchGroup(){}
  std::vector< InstMatch > d_matches;

  bool merge( InstMatchGroup& mg );
  void add( InstMatchGroup& mg );
  void combine( InstMatchGroup& mg );
  void addComplete( InstMatchGroup& mg, InstMatch* mbase = NULL );
  bool contains( InstMatch& m );
  void removeRedundant();
  void removeDuplicate();
  bool empty() { return d_matches.empty(); }
  unsigned int getNumMatches() { return d_matches.size(); }
  InstMatch* getMatch( int i ) { return &d_matches[i]; }
  void clear(){ d_matches.clear(); }
  void debugPrint( const char* c );
};

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
  
  /** owner of quantifiers */
  std::map< Node, Theory* > d_owner;
  /** instantiation queue */
  std::map< Node, std::map< Instantiator*, InstMatchGroup > > d_instQueue;
  /** add partial instantiation specified by m */
  bool addPartialInstantiation( InstMatch& m, Instantiator* i );
  /** process partial instantiations */
  void processPartialInstantiations();
  /** set instantiation level */
  void setInstantiationLevel( Node n, int level );
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
  bool addInstantiation( InstMatch* m );
  /** split on node n */
  bool addSplit( Node n );

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
  void registerLiterals( Node n, Node f, OutputChannel* out );
  /** set active */
  void setActive( Node n, bool val ) { d_active[n] = val; }
  /** get active */
  bool getActive( Node n ) { return d_active[n]; }
  /** get status */
  int getStatus() { return d_status; }
  /** has added lemma */
  bool hasAddedLemma() { return d_addedLemma; }

  //class Statistics {
  //public:
  //  IntStat d_instantiation_rounds;
  //  IntStat d_instantiations;
  //  IntStat d_splits;
  //  Statistics();
  //  ~Statistics();
  //};
  //Statistics d_statistics;
};/* class InstantiationEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

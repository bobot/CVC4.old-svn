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

namespace theory {

class InstantiationEngine;
class PartialInstMatch;

class InstMatch
{
public:
  std::map< Node, Node > d_map;
  std::vector< Node > d_vars;
  std::vector< Node > d_match;
  bool d_computeVec;

  InstMatch(){}
  InstMatch( Node f, InstantiationEngine* ie );
  InstMatch( InstMatch* m );
  virtual PartialInstMatch* asPartialInstMatch() { return NULL; }

  /** fill all unfilled values with m */
  virtual bool add( InstMatch& m );
  /** if compatible, fill all unfilled values with m and return true 
      return false otherwise */
  virtual bool merge( InstMatch& m );
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
  /** partial merge */
  void partialMerge( InstMatch& m, std::map< Node, Node >& splits );
};

class InstMatchGroup
{
public:
  InstMatchGroup(){
    d_is_set = false;
  }
  InstMatchGroup( InstMatchGroup* mg ){
    d_is_set = true;
    for( int i=0; i<(int)mg->getNumMatches(); i++ ){
      InstMatch m( mg->getMatch( i ) );
      d_matches.push_back( m );
    }
  }
  ~InstMatchGroup(){}
  std::vector< InstMatch > d_matches;
  bool d_is_set;

  bool merge( InstMatchGroup& mg );
  void add( InstMatchGroup& mg );
  void combine( InstMatchGroup& mg );
  void addComplete( InstMatchGroup& mg, InstMatch* mbase = NULL );
  void removeRedundant();
  void removeDuplicate();
  bool empty() { return d_matches.empty(); }
  unsigned int getNumMatches() { return d_matches.size(); }
  InstMatch* getMatch( int i ) { return &d_matches[i]; }
  void clear(){ d_matches.clear(); }
  void reset(){
    d_is_set = false;
    clear();
  }
  void debugPrint( const char* c );
};

class Instantiator{
  friend class InstantiationEngine;
protected:
  /** status */
  int d_status;
  /** reference to the instantiation engine */
  InstantiationEngine* d_instEngine;
public:
  enum Status {
    STATUS_UNFINISHED,
    STATUS_UNKNOWN,
    STATUS_SAT,
  };/* enum Effort */
public:
  Instantiator(context::Context* c, InstantiationEngine* ie);
  ~Instantiator();

  /** get corresponding theory for this instantiator */
  virtual Theory* getTheory() = 0;
  /** check function, assertion is asserted to theory */
  virtual void check( Node assertion ){}

  /** reset instantiation */
  virtual void resetInstantiation() { d_status = STATUS_UNFINISHED; }
  /** prepare instantiation method
    * post condition: set d_inst_matches and d_lemmas fields */
  virtual bool doInstantiation( int effort ){ return false; }

  /** get status */
  int getStatus() { return d_status; }
  /** update status */
  static void updateStatus( int& currStatus, int addStatus );
};/* class Instantiator */

class InstantiatorDefault;
namespace uf {
  class InstantiatorTheoryUf;
}

class InstantiationEngine
{
  friend class ::CVC4::TheoryEngine;
  friend class InstantiatorDefault;
  friend class uf::InstantiatorTheoryUf;
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
  /** map from quantifiers to their counterexample equivalents */
  std::map< Node, Node > d_quant_to_ceq;
  /** stores whether a quantifier is a subquantifier of another */
  std::map< Node, Node > d_subquant;
  /** map from quantifiers to whether they are active */
  BoolMap d_active;
  /** lemmas produced */
  std::map< Node, bool > d_lemmas_produced;
  /** status */
  int d_status;
  /** whether a lemma has been added */
  bool d_addedLemma;

  void associateNestedQuantifiers( Node n, Node cen );
public:
  InstantiationEngine(context::Context* c, TheoryEngine* te);
  ~InstantiationEngine();
  
  theory::Instantiator* getInstantiator( Theory* t ) { return d_instTable[t->getId()]; }
  TheoryEngine* getTheoryEngine() { return d_te; }

  bool addInstantiation( Node f, std::vector< Node >& terms );
  bool addInstantiation( InstMatch* m );
  bool addLemma( Node f );
  bool addSplit( Node f );

  /** get the instantiation constants for quantifier f, and ce body ~f[e/x] */
  void getInstantiationConstantsFor( Node f, std::vector< Node >& ics, Node& cebody );
  /** get the skolem constants for quantifier f */
  void getSkolemConstantsFor( Node f, std::vector< Node >& scs );
  /** get the quantified variables for quantifier f */
  void getVariablesFor( Node f, std::vector< Node >& vars );
  /** do a round of instantiation */
  bool doInstantiation( OutputChannel* out );

  /** get the corresponding counterexample literal for quantified formula node n */
  Node getCounterexampleLiteralFor( Node n );
  /** get the corresponding countexample equivalent for quantified formula, 
      where n is a nested quantifier */
  Node getCounterexampleQuantifier( Node n ) { return d_quant_to_ceq[n]; }
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
};/* class InstantiationEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

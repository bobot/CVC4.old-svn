/*********************                                                        */
/*! \file inst_match.h
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
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_MATCH_H
#define __CVC4__INST_MATCH_H

#include "theory/theory.h"
#include "util/hash.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
namespace uf{
  class InstantiatorTheoryUf;
}

class EqualityQuery
{
public:
  EqualityQuery(){}
  ~EqualityQuery(){}
  /** general queries about equality */
  virtual bool areEqual( Node a, Node b ) = 0;
  virtual bool areDisequal( Node a, Node b ) = 0;
  /** other functions */
  virtual void getEIndLitCandidates( Node t, Node s, Node f, bool isEq, std::vector< Node >& litMatches ){}
};

class InstMatch
{
public:
    /* map from variable to ground terms */
  std::map< Node, Node > d_map;
  std::map< Node, Node > d_splits;

  InstMatch(){}
  InstMatch( InstMatch* m );

  /** set the match of v to m */
  void setMatch( Node v, Node m );
  /** fill all unfilled values with m */
  bool add( InstMatch& m );
  /** if compatible, fill all unfilled values with m and return true 
      return false otherwise */
  bool merge( EqualityQuery* q, InstMatch& m, bool allowSplit = false );
  /** -1 : keep this, 1 : keep m, 0 : keep both */
  //int checkSubsume( InstMatch& m );
  /** return if d_maps are equivalent */
  bool isEqual( InstMatch& m );
  /** debug print method */
  void debugPrint( const char* c );
  /** mbase is used if no value given in d_map */
  bool isComplete( Node f ) { return d_map.size()==f[0].getNumChildren(); }
  /** compute d_match */
  void computeTermVec( QuantifiersEngine* ie, std::vector< Node >& vars, std::vector< Node >& match );
  /** add split */
  void addSplit( Node n1, Node n2 );
  /** clear */
  void clear(){
    d_map.clear();
    d_splits.clear();
  }
};

/**
Inst Match generator class: This class incrementally builds matches.
*/
class InstMatchGenerator 
{ 
protected:
  /** img count */
  static int d_imgCount;
  /** all iterators (for memory management purposes) */
  static std::map< Node, std::vector< InstMatchGenerator* > > d_iter[3];
  /** constructor */
  InstMatchGenerator( int op, Node eq );
  /** mk generator */
  static InstMatchGenerator* mkInstMatchGenerator( int op, Node eq );
//public:
//  static void resetInstantiationRoundAll( uf::InstantiatorTheoryUf* itu );
public:
  /** add instantiation match to vector, return true if not redundant */
  bool addInstMatch( InstMatch& m );
  /** calculate (add) more children */
  bool calculateChildren( EqualityQuery* q );
  /** calculate the next match */
  bool calculateNextMatch( EqualityQuery* q );
public:
  /** destructor */
  ~InstMatchGenerator(){}
  /** operation
      If d_eq is non-null,
        0: find match inducing (dis)equality d_eq, modulo equiv classes
        1: find match that unifies the LHS/RHS of the equality d_eq
        2: find match inducing term d_eq to equal any ground term
      If d_eq is null,
        0: union all matches produced in d_children
        1: compute merges of matches produced in d_children
  */
  int d_operation;
  /** term we are matching (if applicable) */
  Node d_eq;
  /** children generators, valid if getMaster()==this */
  std::vector< InstMatchGenerator* > d_children;
protected:
  /** map from terms to the children they represent */
  std::map< Node, InstMatchGenerator* > d_lit_children_map;
  std::map< InstMatchGenerator*, bool > d_children_valid;
  /** is child valid */
  bool isChildValid( int i ) { return d_children_valid.find( d_children[i] )==d_children_valid.end() || d_children_valid[ d_children[i] ]; }
  /** matches produced, valid if getMaster()==this */
  std::vector< InstMatch > d_mg;
  /** the index currently processing (ranges over getMaster()->d_mg) */
  int d_mg_i;
public:
  /** get num current matches */
  int getNumCurrentMatches();
  /** get current match */
  InstMatch* getMatch( int i );
public:
  /** partial matches: for i>0, d_partial[i] is merged match produced for d_children[0]...[i-1], 
      valid if d_operation==1 */
  std::vector< InstMatch > d_partial;
  /** is valid */
  bool d_can_produce_matches;
  /** index of the current child considering, valid if d_operation==0 */
  int d_index;
public:
  /** reset */
  void resetInstantiationRound( EqualityQuery* q );
  /** reset */
  void reset();
  /** get current match */
  InstMatch* getCurrent();
  /** get next match */
  bool getNextMatch( EqualityQuery* q );
public:
  /** the master for this iterator (the one calculating matches) */
  InstMatchGenerator* getMaster() { return d_eq==Node::null() ? this : d_iter[d_operation][d_eq][0]; }
  /** whether this generator takes union of children's matches */
  bool isCombine() { return d_operation!=1; }
public:
  //default
  static InstMatchGenerator* mkInstMatchGenerator( bool isCombine );
  // find matches for t ~ s, mod equality
  static InstMatchGenerator* mkInstMatchGeneratorModEq( Node t, Node s, bool isEq );
  // find matches for t = s
  static InstMatchGenerator* mkInstMatchGenerator( Node t, Node s );
  //find any match for t
  static InstMatchGenerator* mkInstMatchGeneratorAny( Node t );
  //add any match pair
  static void addAnyMatchPair( Node t, Node g );
};




//a collect of nodes representing a trigger
class Trigger {
private:
  /** computation of variable contains */
  static std::map< Node, std::vector< Node > > d_var_contains;
  static void computeVarContains( Node n ) { computeVarContains2( n, n ); }
  static void computeVarContains2( Node n, Node parent );
  QuantifiersEngine* d_quantEngine;
  Node d_f;
  InstMatchGenerator* d_mg;
  Trigger* d_next;
  InstMatchGenerator* mkMatchGenerator( QuantifiersEngine* ie, Node f, std::vector< Node >& nodes );
  InstMatchGenerator* mkMatchGenerator( QuantifiersEngine* ie, Node f, Node n );
  /** is valid */
  bool d_valid;
public:
  std::map< Node, bool > d_vars;
  std::vector< Node > d_nodes;
  std::vector< Node > d_candidates;
  bool addNode( Node n );
public:
  /* ie     : quantifier engine;
     f      : forall something ....
     nodes  : multi-trigger
     keepAll: don't remove unneeded patterns;
*/
  Trigger( QuantifiersEngine* ie, Node f, std::vector< Node >& nodes, bool keepAll = true );
  Trigger( QuantifiersEngine* ie, Node f, std::vector< Node >& candidates, Trigger* prev );
  ~Trigger(){}

  bool isComplete( Node f ){ return d_vars.size()==f[0].getNumChildren(); }
  void debugPrint( const char* c );

  Trigger* getNextTrigger();
  InstMatchGenerator* getGenerator() { return d_mg; }
public:
  /** reset */
  void resetInstantiationRound();
  /** add instantiation */
  bool addInstantiation(  InstMatch& baseMatch, bool addSplits = false, int triggerThresh = 0 );
public:
  /** get current match */
  InstMatch* getCurrent();
  /** get next match
      if true getCurrent can return the next match
   */
  bool getNextMatch();
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

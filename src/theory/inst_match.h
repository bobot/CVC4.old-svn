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
  void computeTermVec( InstantiationEngine* ie );
  /** get associated quantifier */
  Node getQuantifier();
  /** add split */
  void addSplit( Node n1, Node n2 );
};

namespace uf{
  class InstantiatorTheoryUf;
}


/**
Inst Match generator class: This class incrementally builds matches.
*/
class InstMatchGenerator 
{
public:
  static uf::InstantiatorTheoryUf* d_itu;
  /** all iterators (for memory management purposes) */
  static std::map< Node, std::map< Node, std::vector< InstMatchGenerator* > > > d_iter[4];
  /** how many iterators have been assigned (for memory management purposes) */
  static std::map< Node, std::map< Node, int > > d_assigned[4];
  /** maximum number of splits allowed for conditional unification */
  static int d_splitThreshold;
  static bool d_useSplitThreshold;
  static uint64_t d_instLevelThreshold;
  static bool d_useInstLevelThreshold;
  /** reset all */
  static void resetAssigned();
  static void indent( const char* c, int ind );
protected:
  /** queries to d_itu */
  static bool areEqual( Node a, Node b );
  static bool areDisequal( Node a, Node b );
  static Node getRepresentative( Node a );
  static Node getInternalRepresentative( Node a );
  /** has d_children been set */
  bool d_children_set;
  /** has d_mg been set */
  bool d_mg_set;
public:
  /** terms we are matching (if applicable) */
  Node d_t;
  Node d_s;
protected:
  /** d_operation = 0 : d_t = d_s mod equality
      d_operation = 1 : d_t != d_s mod equality
      d_operation = 2 : d_t = d_s, merge arguments 
      d_operation = 3 : match d_t with any available term */
  int d_operation;
  /** partial matches produced for children 0...n */
  std::vector< InstMatch > d_partial;
  /** index of child currently processing */
  int d_index;
  /** depth in the tree */
  int d_depth;
  /** splits required for this iterator (e.g. ground argument mismatches) */
  std::map< Node, Node > d_splits;
  /** add split */
  void addSplit( Node n1, Node n2 );
  /** the master for this iterator (the one calculating matches) */
  InstMatchGenerator* getMaster() { return d_t==Node::null() ? this : d_iter[d_operation][d_t][d_s][0]; }
  /** clear this iterator (make fresh) */
  void clear();
  /** whether to accept a match */
  bool acceptMatch( InstMatch* m );
protected:
  /** calculate the children vector */
  void calcChildren();
  /** calculate children trivial cases */
  void calcChildrenTriv();
  /** calculate the next match */
  bool calcNextMatch();
  /** add instantiation match to vector, return true if not redundant */
  bool addInstMatch( InstMatch& m );
  // find matches for t ~ s
  InstMatchGenerator( Node t, Node s, int op );
  // mkUiterator
  static InstMatchGenerator* mkInstMatchGenerator( Node t, Node s, int op );
public:
  ~InstMatchGenerator(){}

  /** matches produced */
  std::vector< InstMatch > d_mg;
  /** the index currently processing (ranges over d_mg) */
  int d_mg_i;
  /** children iterators */
  std::vector< InstMatchGenerator* > d_children;

  /** clear the matches for this iterator */
  void clearMatches();
  /** contains no matches? */
  bool empty() { return getMaster()->d_mg_set && getMaster()->d_mg.empty(); }
  /** get current match */
  InstMatch* getCurrent() { 
    if( d_mg_i>=0 && d_mg_i<(int)getMaster()->d_mg.size() ){
      return &getMaster()->d_mg[ d_mg_i ]; 
    }else{
      return NULL;
    }
  }
  /** get next match */
  bool getNextMatch();
  /** reset this iterator */
  void reset() { d_mg_i = -1; }
  /** debug print */
  void debugPrint( const char* c, int ind, bool printChildren = true );
  /** is this uiterator performing a combine operation (not a merge) */
  bool isCombine() { return d_operation<2 || d_operation==3; }
  /** has splits */
  bool hasSplits() { return !d_splits.empty(); }
  /** get splits */
  void getSplits( std::vector< std::pair< Node, Node > >& splits ){
    splits.insert( splits.end(), getMaster()->d_splits.begin(), getMaster()->d_splits.end() );
  }
  /** get instantiation level */
  int getInstantiationLevel();

  //default
  static InstMatchGenerator* mkInstMatchGenerator( bool isComb = false );
  // find matches for t ~ s
  static InstMatchGenerator* mkCombineInstMatchGenerator( Node t, Node s, bool isEq );
  // find matches that unify t and s
  static InstMatchGenerator* mkMergeInstMatchGenerator( Node t, Node s );
  //find any match for t
  static InstMatchGenerator* mkAnyMatchInstMatchGenerator( Node t );
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
  /** reference to the instantiation engine */
  InstantiationEngine* d_instEngine;
  /** quantifier we are producing matches for */
  Node d_f;
  /** explicitly provided patterns */
  std::vector< InstMatchGenerator* > d_user_gen;
private:
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
    bool addNode( Node n, bool force = false );
    int getNumNodes() { return (int)d_nodes.size(); }
    Node getNode( int i ) { return d_nodes[i]; }
    void clear() { 
      d_nodes.clear();
      d_vars.clear();
    }
    bool isComplete( Node f ){ return d_vars.size()==f[0].getNumChildren(); }
    void debugPrint( const char* c );
  };
  /** current trigger information */
  Trigger d_currTrigger;
  /** whether to produce (another) trigger */
  bool d_produceTrigger;
public:
  /** the base match for the quantifier (solve instantiation constants) */
  InstMatch d_baseMatch;
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
public:
  /** add instantiations */
  bool addInstantiation( int pat = -1, int triggerThresh = -1, bool addSplits = true );
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

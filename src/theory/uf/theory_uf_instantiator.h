/*********************                                                        */
/*! \file theory_uf_instantiator.h
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
 ** \brief Theory uf instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_INSTANTIATOR_H
#define __CVC4__THEORY_UF_INSTANTIATOR_H

#include "theory/instantiation_engine.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdlist.h"
#include "context/cdlist_context_memory.h"

namespace CVC4 {
namespace theory {
namespace uf {

//class SubTermNode
//{
//private:
//  typedef context::CDList<SubTermNode* > GmnList;
//  typedef context::CDList<Node > ObList;
//  GmnList d_parents;
//  ObList d_obligations;
//  Node d_node;
//  Node d_match;
//public:
//  SubTermNode( context::Context* c, Node n );
//  ~SubTermNode(){}
//
//  void addParent( SubTermNode* g );
//  int getNumParents() { return d_parents.size(); }
//  SubTermNode* getParent( int i ) { return d_parents[i]; }
//
//  void addObligation( Node n );
//  int getNumObligations() { return d_obligations.size(); }
//  Node getObligation( int i ) { return d_obligations[i]; }
//
//  Node getNode() { return d_node; }
//
//  void setMatch( Node n ) { d_match = n; }
//  Node getMatch() { return d_match; }
//};

/**
Unify Iterator class:
This class incrementally builds unifiers that induce d_t ~ d_s.
*/
class UIterator 
{
public:
  static InstantiatorTheoryUf* d_itu;
  /** all iterators (for memory management purposes) */
  static std::map< Node, std::map< Node, std::vector< UIterator* > > > d_iter[3];
  /** how many iterators have been assigned (for memory management purposes) */
  static std::map< Node, std::map< Node, int > > d_assigned[3];
  /** maximum number of splits allowed for conditional unification */
  static int d_splitThreshold;
  /** reset all */
  static void resetAssigned();
  static void indent( const char* c, int ind );
protected:
  /** queries to d_itu */
  static bool areEqual( Node a, Node b );
  static bool areDisequal( Node a, Node b );
  static Node getRepresentative( Node a );
  /** has d_children been set */
  bool d_children_set;
  /** has d_mg been set */
  bool d_mg_set;
public:
  /** terms we are matching */
  Node d_t;
  Node d_s;
protected:
  /** d_operation = 0 : d_t = d_s mod equality
      d_operation = 1 : d_t != d_s mod equality
      d_operation = 2 : d_t = d_s, merge arguments */
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
  UIterator* getMaster() { return d_t==Node::null() ? this : d_iter[d_operation][d_t][d_s][0]; }
  /** clear this iterator (make fresh) */
  void clear();
protected:
  /** calculate the children vector */
  void calcChildren();
  /** calculate the next match */
  bool calcNextMatch();
  /** add instantiation match to vector, return true if not redundant */
  bool addInstMatch( InstMatch& m );
  //default
  UIterator( int op = 2 );
  // find matches for t ~ s
  UIterator( Node t, Node s, int op, Node f );
public:
  ~UIterator(){}

  /** matches produced */
  InstMatchGroup d_mg;
  /** the index currently processing (ranges over d_mg.d_matches) */
  int d_mg_i;
  /** children iterators */
  std::vector< UIterator* > d_children;

  /** clear the matches for this iterator */
  void clearMatches();
  /** contains no matches? */
  bool empty() { return getMaster()->d_mg_set && getMaster()->d_mg.d_matches.empty(); }
  /** get current match */
  InstMatch* getCurrent() { 
    if( d_mg_i>=0 && d_mg_i<(int)getMaster()->d_mg.d_matches.size() ){
      return &getMaster()->d_mg.d_matches[ d_mg_i ]; 
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
  bool isCombine() { return d_operation<2; }
  /** has splits */
  bool hasSplits() { return !d_splits.empty(); }
  /** get splits */
  void getSplits( std::vector< std::pair< Node, Node > >& splits ){
    splits.insert( splits.end(), getMaster()->d_splits.begin(), getMaster()->d_splits.end() );
  }
  /** determine issues for why no matches were produced */
  double collectUnmerged( std::map< UIterator*, UIterator* >& index, std::vector< UIterator* >& unmerged,
                          std::vector< UIterator* >& cover );

  //default
  static UIterator* mkUIterator( bool isComb = false );
  // find matches for t ~ s
  static UIterator* mkCombineUIterator( Node t, Node s, bool isEq, Node f );
  //merge uiterator
  static UIterator* mkMergeUIterator( Node t, Node s, Node f );
};

//class UIteratorCmd
//{
//public:
//  static InstantiatorTheoryUf* d_itu;
//private:
//  std::vector< UIterator* > d_curr;
//  int d_cmd;
//public:
//  UIteratorCmd(){}
//  ~UIteratorCmd(){}
//
//  void resolveGroundArgumentMismatches( UIterator* it );
//};


class InstantiatorTheoryUf : public Instantiator{
  friend class UIterator;
protected:
  typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
  typedef context::CDMap<Node, NodeList*, NodeHashFunction> NodeLists;
  //typedef context::CDMap<Node, SubTermNode*, NodeHashFunction > SubTermMap;

  NodeLists d_obligations;
  BoolMap d_ob_pol;
  //std::map< Node, int > d_choice_counter;
  //int d_numChoices;

  //SubTermMap d_subterms;
  //IntMap d_subterm_size;
  //void buildSubTerms( Node n );
  //SubTermNode* getSubTerm( Node n );

  /** all terms in the current context */
  BoolMap d_terms_full;
  /** terms in the current context that have an equality or disequality with another term */
  BoolMap d_terms;
  /** map from (representative) nodes to list of representative nodes they are disequal from */
  NodeList d_disequality;
  /** representative map */
  std::map< Node, Node > d_reps;
  /** used equivalance classes */
  std::map< Node, std::vector< Node > > d_emap;
  /** disequality list */
  std::map< Node, std::vector< Node > > d_dmap;
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  void debugPrint( const char* c );
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryUf() {}
  /** check method */
  void check( Node assertion );
  /** reset instantiation */
  void resetInstantiation();
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryUf"); }
private:
  /** assert terms are equal */
  void assertEqual( Node a, Node b );
  /** register terms */
  void registerTerm( Node n, bool isTop = true );

  /** calculate matches for quantifier f at effort */
  std::map< Node, InstMatch > d_baseMatch;
  std::map< Node, UIterator* > d_mergeIter;
  void process( Node f, int effort );
  //std::map< Node, bool > d_matchable;
  //std::map< Node, bool > d_unmatched;

  /** find best match to any term */
  std::map< Node, std::vector< Node > > d_matches;
  std::map< Node, std::vector< Node > > d_anyMatches;
  void calculateMatches( Node f, Node t );
  /** calculate sets possible matches to induce t ~ s */
  std::map< Node, std::map< Node, std::vector< Node > > > d_litMatchCandidates[2];
  void calculateEIndLitCandidates( Node t, Node s, Node f, bool isEq );
  /** calculate whether two terms are equality-dependent */
  std::map< Node, std::map< Node, bool > > d_eq_dep;
  void calculateEqDep( Node i, Node c, Node f );

  /** add split equality */
  bool addSplitEquality( Node n1, Node n2, bool reqPhase = false, bool reqPhasePol = true );

};/* class InstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

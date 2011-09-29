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

class InstantiatorTheoryUf : public Instantiator{
protected:
  typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
  typedef context::CDMap<Node, NodeList*, NodeHashFunction> NodeLists;
  //typedef context::CDMap<Node, SubTermNode*, NodeHashFunction > SubTermMap;

  NodeLists d_obligations;
  //std::map< Node, int > d_choice_counter;
  //int d_numChoices;

  //SubTermMap d_subterms;
  //IntMap d_subterm_size;
  //void buildSubTerms( Node n );
  //SubTermNode* getSubTerm( Node n );

  BoolMap d_terms;
  BoolMap d_terms_full;
  /** map from (representative) nodes to list of representative nodes they are disequal from */
  NodeList d_disequality;
  /** map from patterns to nodes that they have ematched against */
  //NodeLists d_eind_done;
  /** quantifier status */
  int d_quantStatus;

  ///** used eq classes */
  std::map< Node, Node > d_reps;
  std::map< Node, std::vector< Node > > d_emap;
  std::map< Node, std::vector< Node > > d_dmap;
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  void debugPrint( const char* c );
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryUf() {}

  void check( Node assertion );
  void assertEqual( Node a, Node b );
  void resetInstantiation();
  bool doInstantiation( int effort );
private:
  void registerTerm( Node n, bool isTop = true );

  /** calculate matches for quantifier f at effort */
  std::map< Node, InstMatch > d_baseMatch;
  void process( Node f, int effort );
  /** determine why t did not match with g */
  bool resolveLitMatch( Node t, Node g, Node f, bool isEq );
  bool resolveMatchPair( Node t, Node mt, Node s, Node ms, Node f );
  bool resolveMatch( Node t, Node g, Node f );
  /** determine why inst match groups did not merge */
  bool resolveMerge( std::vector< InstMatchGroup* >& matches, Node f );
  /** resolve counterexamples */
  bool resolveModel( Node f, Node t );
  /** calculate unifiers that induce lit */
  std::map< Node, std::map< Node, InstMatchGroup > > d_litMatches[2];
  std::map< Node, std::map< Node, std::vector< Node > > > d_litMatchCandidates[2];
  void calculateEIndLit( Node t, Node s, Node f, bool isEq );
  /** find best match to any term */
  std::map< Node, std::vector< Node > > d_matches;
  std::map< Node, std::vector< Node > > d_anyMatches;
  void calculateMatches( Node f, Node t, bool any = false );

  /** match terms i and c */
  std::map< Node, std::map< Node, InstMatchGroup > > d_eind;
  std::map< Node, std::map< Node, bool > > d_eq_amb;
  void calculateEInd( Node i, Node c, Node f );
  void calculateEqAmb( Node i, Node c, Node f );

  ///** get number of equal arguments */
  //std::map< Node, std::map< Node, int > > d_numEqArg;
  //int getNumNeqArgs( Node i, Node c );

  /** add split equality */
  bool addSplitEquality( Node n1, Node n2 );

};/* class InstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

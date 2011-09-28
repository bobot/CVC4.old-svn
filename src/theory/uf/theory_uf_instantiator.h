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

  /** reference to the theory that it looks at */
  Theory* d_th;
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

  Theory* getTheory();
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
  void resolveMatch( Node t, Node g, Node f );
  /** determine why inst match groups did not merge */
  void resolveMerge( std::vector< InstMatchGroup* >& matches, Node f );
  /** resolve counterexamples */
  void resolveModel( Node f, Node t );
  /** calculate unifiers that induce lit */
  std::map< Node, InstMatchGroup > d_litMatches;
  void calculateEIndLit( Node lit, Node f );
  /** find best match */
  std::map< Node, std::map< Node, Node > > d_bestLitMatch[2];
  void findBestLiteralMatch( Node f, Node t, Node s, bool isEq, bool rhsPat = false );
  /** find best match to any term */
  std::map< Node, Node > d_bestMatch;
  std::map< Node, Node > d_anyMatch;
  void findBestMatch( Node f, Node t, bool any = false );
  bool isBetterMatch( Node t, Node t1, Node t2 );

  /** match terms i and c */
  std::map< Node, std::map< Node, InstMatchGroup > > d_eind;
  std::map< Node, std::map< Node, bool > > d_does_eind;
  std::map< Node, std::map< Node, bool > > d_eq_amb;
  void calculateEInd( Node i, Node c, Node f );
  void calculateEqAmb( Node i, Node c, Node f );
  /** match modulo equivalence class c */
  std::map< Node, std::map< Node, InstMatchGroup > > d_eind_mod;
  void calculateEIndMod( Node i, Node c, Node f ); 

  /** get number of equal arguments */
  std::map< Node, std::map< Node, int > > d_numEqArg;
  int getNumNeqArgs( Node i, Node c );

  /** add split equality */
  bool addSplitEquality( Node n1, Node n2 );

};/* class InstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

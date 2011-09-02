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

  //AJR-hack
  //Node getConcreteTerm( Node rep );

  /** reference to the theory that it looks at */
  Theory* d_th;
  //EMatchMap d_ematch;
  //EMatchListMap d_ematch_list;
  BoolMap d_inst_terms;
  BoolMap d_concrete_terms;
  BoolMap d_active_ic;
  /** map from (representative) nodes to list of nodes in their eq class */
  NodeLists d_equivalence_class;
  BoolMap d_is_rep;
  /** map from (representative) nodes to list of representative nodes they are disequal from */
  NodeLists d_disequality;
  /** map from patterns to nodes that they have ematched against */
  NodeLists d_ematch_done;

  ///** used eq classes */
  std::map< Node, std::vector< Node > > d_emap;
  std::map< Node, std::vector< Node > > d_dmap;
  ////std::map< Node, Node > d_eq_find;
  void refreshMaps();
  //bool decideEqual( Node a, Node b );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  void debugPrint();
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryUf() {}

  Theory* getTheory();
  void check( Node assertion );
  void assertEqual( Node a, Node b );
  void resetInstantiation();
  bool prepareInstantiation( Effort e );
private:
  void registerTerm( Node n );
  void initializeEqClass( Node t );
  void initializeDisequalityList( Node t );

  bool hasInstantiationConstantsFrom( Node i, Node f );
  void calculateMatches( Node f, Effort e );

  std::map< Node, std::map< Node, InstMatchGroup* > > d_ematch;
  std::map< Node, std::map< Node, bool > > d_does_ematch;
  std::map< Node, std::map< Node, bool > > d_eq_amb;
  std::map< Node, std::map< Node, InstMatchGroup* > > d_ematch_mod;
  std::map< Node, std::map< Node, bool > > d_did_ematch_mod;
  void doEMatching( Node i, Node c, Node f,  bool moduloEq = false );
  void getPartialMatches( Node i, Node c, Node f, InstMatchGroup* mg );
  void partialMerge( InstMatchGroup* m1, InstMatchGroup* m2, InstMatchGroup* prod );
  bool isIntersectionConsistent( InstMatch* m1, InstMatch* m2 );
  void addEMatch( InstMatchGroup* mg, Node i, Node c, Node f, bool partialMatch = false );
  void addEMatch( InstMatchGroup* mg, Node i, Node f, bool partialMatch = false );
  void addEqualityEMatch( InstMatchGroup* mg, Node i, Node f, bool partialMatch = false );

  void filterInconsistent( InstMatchGroup* mg );
  bool isConsistent( InstMatch* m );

  //void setEmatchDone( Node i, Node c );
  //bool isEmatchDone( Node i, Node c );

  //std::map< Node, std::map< Node, bool > > d_generalizes;
  //bool isGeneralization( Node i1, Node i2 );
};/* class InstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

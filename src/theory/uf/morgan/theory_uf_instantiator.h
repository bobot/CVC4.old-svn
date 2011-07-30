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

namespace CVC4 {
namespace theory {
namespace uf {
namespace morgan {

class TheoryUfMorgan;

///** represents a prefix (also called inverted path tree?) */
//class EMatchTreeNode
//{
//public:
//  typedef context::CDList<int, context::ContextMemoryAllocator<int> > IndexList;
//  typedef context::CDMap<Node, IndexList*, NodeHashFunction > IndexMap;
//  typedef context::CDMap<Node, EMatchTreeNode*, NodeHashFunction > ChildMap;
//public:
//  EMatchTreeNode( context::Context* c, EMatchTreeNode* p = NULL );
//  ~EMatchTreeNode(){}
//
//  EMatchTreeNode* d_parent;
//  /** for (n,i) node n has this as node with prefix at argument i */
//  IndexMap d_nodes;
//  /** children nodes */
//  ChildMap d_children;
//
//  void debugPrint( int ind = 0 );
//};


class InstantiatorTheoryUf : public Instantiatior{
protected:
  //typedef context::CDMap<Node, EMatchTreeNode*, NodeHashFunction > EMatchMap;
  //typedef context::CDList<EMatchTreeNode*, context::ContextMemoryAllocator<EMatchTreeNode*> > EMatchList;
  //typedef context::CDMap<Node, EMatchList*, NodeHashFunction > EMatchListMap;
  typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
  typedef context::CDMap<Node, NodeList*, NodeHashFunction> NodeLists;

  //AJR-hack
  Node getConcreteTerm( Node rep );

  //typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  /** reference to the theory that it looks at */
  Theory* d_th;
  //EMatchMap d_ematch;
  //EMatchListMap d_ematch_list;
  BoolMap d_inst_terms;
  BoolMap d_concrete_terms;
  BoolMap d_active_ic;
  /** map from (representative) nodes to list of nodes in their eq class */
  NodeLists d_equivalence_class;
  /** map from (representative) nodes to list of representative nodes they are disequal from */
  NodeLists d_disequality;

  /** used eq classes */
  std::map< Node, std::vector< Node > > d_emap;
  std::map< Node, std::vector< Node > > d_dmap;
  //std::map< Node, Node > d_eq_find;
  void refreshMaps();
  //bool decideEqual( Node a, Node b );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node find( Node a );
  void debugPrint();
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryUf() {}

  Theory* getTheory();
  void check( Node assertion );
  void assertEqual( Node a, Node b );
  void assertDisequal( Node a, Node b );
  bool prepareInstantiation();
private:
  void registerTerm( Node n );
  void setInstTerms( Node n );
  void setConcreteTerms( Node n );
  //void buildEMatchTree( Node n, std::vector< EMatchTreeNode* >& active );
  void initializeEqClass( Node t );
  void initializeDisequalityList( Node t );
  int getNumSharedDisequalities( Node a, Node b );
  bool eqClassContainsInstConstantsFromFormula( Node c, Node f );

  void calculateBestMatch( Node f );
  //map from pairs of non-equality independent nodes to the # of arguments they match on
  std::map< Node, std::map< Node, int > > d_equalArgs;
  std::map< Node, std::map< Node, bool > > d_eq_independent;
  void getNumEqualArgs( Node i, Node c );
  void addToGraphMatchScore( Node i,
                             std::map< Node, int >& gmatchScore,
                             std::map< Node, std::vector< Node > >& contradict,
                             std::map< Node, std::vector< Node > >& support,
                             std::map< Node, std::vector< Node > >& support_terms );
  void addToGraphMatchScore( Node i, Node c,
                             std::map< Node, int >& gmatchScore,
                             std::map< Node, std::vector< Node > >& contradict,
                             std::map< Node, std::vector< Node > >& support,
                             std::map< Node, std::vector< Node > >& support_terms );
  void removeFromGraphMatchScore( Node eq,
                                  std::map< Node, int >& gmatchScore,
                                  std::map< Node, std::vector< Node > >& contradict,
                                  std::map< Node, std::vector< Node > >& support,
                                  std::map< Node, std::vector< Node > >& support_terms );
  void doEMatchMerge( std::vector< Node >& eqs, std::vector< std::map< Node, Node > >& ematches,
                      std::vector< Node >& terms, std::map< Node, bool >& terms_ematched );


  std::map< Node, std::map< Node, std::vector< std::map< Node, Node > > > > d_ematch;
  std::map< Node, std::map< Node, std::vector< std::map< Node, Node > > > > d_ematch_mod;
  std::map< Node, std::map< Node, bool > > d_eq_independent_em;
  void doEMatching( Node i, Node c, Node f,  bool moduloEq = false );
  void removeRedundant( std::vector< std::map< Node, Node > >& matches );
  int checkSubsume( std::map< Node, Node >& m1, std::map< Node, Node >& m2 );
  void unify( std::vector< std::map< Node, Node > >& target,
              std::vector< std::map< Node, Node > >& matches );
  bool unify( std::map< Node, Node >& target, std::map< Node, Node >& matches );
  int numMatches( std::vector< std::map< Node, Node > >& target,
                  std::vector< std::map< Node, Node > >& matches );

  Node d_best;
  std::map< Node, Node > d_best_subs;
  double d_heuristic;
};/* class InstantiatorTheoryUf */


//class EMatchState 
//{
//private:
//  std::vector< Node > termsToMatch;
//  std::vector< Node > termsMatched;
//  std::vector< std::map< Node, Node > > matches;   
//  std::map< Node, int > ematches;
//  std::map< Node, std::vector< Node > > contradict;  //map from ematches to other ematches that they contradict
//  std::map< Node, std::vector< Node > > support;  //map from ematches to other ematches that they support
//public:
//  EMatchState(){}
//  ~EMatchState(){}
//
//  void addTerm( Node n );
//};

}
}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

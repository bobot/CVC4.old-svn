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

  //typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  /** reference to the theory that it looks at */
  Theory* d_th;
  //EMatchMap d_ematch;
  //EMatchListMap d_ematch_list;
  BoolMap d_inst_terms;
  BoolMap d_concrete_terms;
  BoolMap d_active_ic;
  /** map from terms to the instantiation constants they contain */
  std::map< Node, std::vector< Node > > d_term_ics;
  bool isSolved( Node n );
  /** current best */
  Node d_best;
  Node d_best_eq;
  int d_best_heuristic[10];
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryUf() {}

  Theory* getTheory();
  void check( Node assertion );
  bool prepareInstantiation();
private:
  void assertEqual( Node a, Node b );
  void assertDisequal( Node a, Node b );
  void registerTerm( Node n );
  void collectInstConstants( Node n, std::vector< Node >& ics );
  void setConcreteTerms( Node n );
  //void buildEMatchTree( Node n, std::vector< EMatchTreeNode* >& active );
  void processAmbiguity( Node c, Node i, bool eq, bool diseq, int depth = 0 );

  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
};/* class InstantiatorTheoryUf */

}
}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

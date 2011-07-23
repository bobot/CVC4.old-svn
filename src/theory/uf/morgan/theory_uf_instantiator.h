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

/** represents a prefix */
class EMatchTreeNode
{
public:
  typedef context::CDList<int, context::ContextMemoryAllocator<int> > IndexList;
  typedef context::CDMap<Node, IndexList*, NodeHashFunction > IndexMap;
  typedef context::CDMap<Node, EMatchTreeNode*, NodeHashFunction > ChildMap;
public:
  EMatchTreeNode( context::Context* c, EMatchTreeNode* p = NULL );
  ~EMatchTreeNode(){}

  EMatchTreeNode* d_parent;
  /** for (n,i) node n has this as node with prefix at argument i */
  IndexMap d_nodes;
  /** children nodes */
  ChildMap d_children;

  void debugPrint( int ind = 0 );
};


class TheoryUfInstantiatior : public TheoryInstantiatior{
protected:
  typedef context::CDMap<Node, EMatchTreeNode*, NodeHashFunction > EMatchMap;
  typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;

  //typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  /** reference to the theory that it looks at */
  Theory* d_th;
  /** equivalence classes for active instantiation constants */
  EMatchMap d_ematch_tree;
  BoolMap d_registered;
public:
  TheoryUfInstantiatior(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th);
  ~TheoryUfInstantiatior() {}

  Theory* getTheory();
  void check( Node assertion );
  bool prepareInstantiation();
private:
  void assertEqual( Node a, Node b );
  void assertDisequal( Node a, Node b );
  void registerTerm( Node n );
  void buildEMatchTree( Node n, std::vector< EMatchTreeNode* >& active );
};/* class TheoryUfInstantiatior */

}
}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

/*********************                                                        */
/*! \file theory_uf_instantiator.cpp
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
 ** \brief Implementation of theory uf instantiator class
 **/

#include "theory/uf/morgan/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/uf/morgan/theory_uf_morgan.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::uf::morgan;

EMatchTreeNode::EMatchTreeNode( context::Context* c, EMatchTreeNode* p ) : 
d_parent( p ),
d_nodes( c ),
d_children( c ){

}

void EMatchTreeNode::debugPrint( int ind )
{
  for( IndexMap::iterator it = d_nodes.begin(); it!=d_nodes.end(); ++it ){
    for( int i=0; i<ind; i++ ) { Debug("quant-uf") << " "; }
    Debug("quant-uf") << (*it).first << ": ";
    IndexList* il = (*it).second;
    for( IndexList::const_iterator it2 = il->begin(); it2!=il->end(); ++it2 ){
      Debug("quant-uf") << (*it2) << " ";
    }
    Debug("quant-uf") << std::endl;
  }
  for( ChildMap::const_iterator it = d_children.begin(); it!=d_children.end(); ++it ){
    for( int i=0; i<ind; i++ ) { Debug("quant-uf") << " "; }
    Debug("quant-uf") << (*it).first << ": " << std::endl;
    (*it).second->debugPrint( ind+1 );
    Debug("quant-uf") << "." << std::endl;
  }
}

TheoryUfInstantiatior::TheoryUfInstantiatior(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
TheoryInstantiatior( c, ie ),
d_th(th),
d_ematch_tree( c ),
d_registered( c ){
  
  
}

Theory* TheoryUfInstantiatior::getTheory() { 
  return d_th; 
}

void TheoryUfInstantiatior::check( Node assertion )
{
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  Debug("quant-uf") << "TheoryUfInstantiatior::check: " << assertion << std::endl;
  switch(assertion.getKind()) {
  case kind::EQUAL:
  case kind::IFF:
    assertEqual(assertion[0], assertion[1]);
    break;
  case kind::APPLY_UF:
    { // assert it's a predicate
      Assert(assertion.getOperator().getType().getRangeType().isBoolean());
      assertEqual(assertion, t->d_trueNode);
    }
    break;
  case kind::NOT:
    if(assertion[0].getKind() == kind::EQUAL ||
       assertion[0].getKind() == kind::IFF) {
      assertDisequal(assertion[0][0], assertion[0][1]);
    } else {
      // negation of a predicate
      Assert(assertion[0].getKind() == kind::APPLY_UF);
      // assert it's a predicate
      Assert(assertion[0].getOperator().getType().getRangeType().isBoolean());
      assertEqual(assertion[0], t->d_falseNode);
    }
    break;
  default:
    Unhandled(assertion.getKind());
  }
}

void TheoryUfInstantiatior::assertEqual( Node a, Node b )
{
  if( b.getKind()==INST_CONSTANT){
    Node t = a;
    a = b;
    b = t;
  }
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  registerTerm( a );
  registerTerm( b );
}

void TheoryUfInstantiatior::assertDisequal( Node a, Node b )
{
  if( b.getKind()==INST_CONSTANT){
    Node t = a;
    a = b;
    b = t;
  }
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  registerTerm( a );
  registerTerm( b );
}

void TheoryUfInstantiatior::registerTerm( Node n )
{
  if( d_registered.find( n )==d_registered.end() ){
    std::vector< EMatchTreeNode* > active;
    buildEMatchTree( n, active );
  }
}

void TheoryUfInstantiatior::buildEMatchTree( Node n, std::vector< EMatchTreeNode* >& active )
{
  if( n.getKind()==INST_CONSTANT ){
    if( d_ematch_tree.find( n )==d_ematch_tree.end() ){
      d_ematch_tree[n] = new EMatchTreeNode( d_th->getContext() );
    }
    active.push_back( d_ematch_tree[n] );
  }else if( n.hasAttribute(InstantitionConstantAttribute()) ){
    Assert( n.getKind()==APPLY_UF );
    Node op = n.getOperator();
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      //build e-match tree for the child
      std::vector< EMatchTreeNode* > cactive;
      buildEMatchTree( n[i], cactive );

      //for each e-match tree that we are extending
      for( int j=0; j<(int)cactive.size(); j++ ){
        //this node at argument i is dependent upon cactive[j]
        if( d_registered.find( n )==d_registered.end() ){
          //add argument index
          EMatchTreeNode::IndexList* nodes;
          EMatchTreeNode::IndexMap::iterator n_i = cactive[j]->d_nodes.find(op);
          if( n_i==cactive[j]->d_nodes.end() ){
            nodes = new(d_th->getContext()->getCMM()) EMatchTreeNode::IndexList(true, d_th->getContext(), false,
                                                      ContextMemoryAllocator<int>(d_th->getContext()->getCMM()));
            cactive[j]->d_nodes.insertDataFromContextMemory(n, nodes);
          }else{
            nodes = (*n_i).second;
          }
          nodes->push_back( i );
          //add child node
          if( cactive[j]->d_children.find( op )==cactive[j]->d_children.end() ){
            cactive[j]->d_children[op] = new EMatchTreeNode( d_th->getContext(), cactive[j] );
          }
        }
        EMatchTreeNode* emtn = cactive[j]->d_children[op];
        //add it to active if not already done so
        if( std::find( active.begin(), active.end(), emtn )==active.end() ){
          active.push_back( emtn );
        }
      }
    }
    d_registered[n] = true;
  }
}

bool TheoryUfInstantiatior::prepareInstantiation()
{
  Debug("quant-uf") << "Search for instantiation for UF:" << std::endl;
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;

  for( EMatchMap::const_iterator it = d_ematch_tree.begin(); it!=d_ematch_tree.end(); ++it ){
    Debug("quant-uf") << (*it).first << ": " << std::endl;
    (*it).second->debugPrint( 1 );
  }


  //find all instantiation constants that are solved


  //we're done if some node is instantiation-ready


  //otherwise, add possible splitting lemma


  return false;
}

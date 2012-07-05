/*********************                                                        */
/*! \file model.cpp
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
 ** \brief Implementation of model class
 **/

#include "theory/model.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

void RepSet::clear(){
  d_type_reps.clear();
  d_tmap.clear();
}

void RepSet::add( Node n ){
  TypeNode t = n.getType();
  d_tmap[ n ] = (int)d_type_reps[t].size();
  d_type_reps[t].push_back( n );
}

void RepSet::set( TypeNode t, std::vector< Node >& reps ){
  for( size_t i=0; i<reps.size(); i++ ){
    d_tmap[ reps[i] ] = i;
  }
  d_type_reps[t].insert( d_type_reps[t].begin(), reps.begin(), reps.end() );
}

void RepSet::debugPrint( const char* c, QuantifiersEngine* qe ){
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    Debug( c ) << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      Debug( c ) << "   " << i << ": " << it->second[i] << std::endl;
      Debug( c ) << "         eq_class( " << it->second[i] << " ) : ";
      ((uf::InstantiatorTheoryUf*)qe->getInstantiator( THEORY_UF ))->outputEqClass( c, it->second[i] );
      Debug( c ) << std::endl;
    }
  }
}

Model::Model( context::Context* c ) :
d_equalityEngine( c, "Model" ){

}

void Model::clear(){
  //reset
  d_ra.clear();
  d_op_terms.clear();
}

void Model::initialize(){
  //populate term database, store representatives
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    d_ra.add( eqc );
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ){
      if( (*eqc_i).hasOperator() ){
        d_op_terms[ (*eqc_i).getOperator() ].push_back( *eqc_i );
      }
      if( (*eqc_i).getMetaKind()==kind::metakind::CONSTANT ){
        d_constants[ eqc ] = *eqc_i;
      }
      ++eqc_i;
    }
    if( d_constants[ eqc ].isNull() ){
      //DO_THIS: ensure constant is in the equivalence class of eqc
      d_constants[ eqc ] = eqc;  //temporary
    }
    ++eqcs_i;
  }
}

/** add equality */
void Model::assertEquality( Node a, Node b, bool polarity ){
  d_equalityEngine.assertEquality( a.eqNode(b), polarity, Node::null() );
}

/** add predicate */
void Model::assertPredicate( Node a, bool polarity ){
  d_equalityEngine.assertPredicate( a, polarity, Node::null() );
}

/** add equality engine */
void Model::assertEqualityEngine( eq::EqualityEngine* ee ){
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predPolarity = false;
    if( eqc.getType()==NodeManager::currentNM()->booleanType() ){
      predicate = true;
      predPolarity = ee->areEqual( eqc, NodeManager::currentNM()->mkConst( true ) );
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, ee );
    while( !eqc_i.isFinished() ){
      if( predicate ){
        assertPredicate( *eqc_i, predPolarity );
      }else{
        assertEquality( *eqc_i, eqc, true );
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
}

//for debugging
void Model::printRepresentative( const char* c, QuantifiersEngine* qe, Node r ){
  Assert( !r.isNull() );
  if( r.isNull() ){
    Debug( c ) << "null";
  }else if( r.getType()==NodeManager::currentNM()->booleanType() ){
    if( qe->getEqualityQuery()->areEqual( r, NodeManager::currentNM()->mkConst( true ) ) ){
      Debug( c ) << "true";
    }else{
      Debug( c ) << "false";
    }
  }else{
    Debug( c ) << qe->getEqualityQuery()->getRepresentative( r );
  }
}

Node DefaultModel::getValue( TNode n ){
  if( d_equalityEngine.hasTerm( n ) ){
    return d_constants[ d_equalityEngine.getRepresentative( n ) ];
  }else{
    TypeNode t = n.getType();
    if( d_ra.hasType( t ) ){
      return getValue( d_ra.d_type_reps[t][0] );
    }else{
      return n;
    }
  }
}

Model* DefaultModelBuilder::getModel(){
  d_model.clear();
  d_te->collectModelInfo( &d_model );
  d_model.initialize();
  return &d_model;
}
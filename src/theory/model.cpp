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

void RepSet::debugPrint( const char* c ){
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    Debug( c ) << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      Debug( c ) << "   " << i << ": " << it->second[i] << std::endl;
      //Debug( c ) << "         eq_class( " << it->second[i] << " ) : ";
      //((uf::InstantiatorTheoryUf*)qe->getInstantiator( THEORY_UF ))->outputEqClass( c, it->second[i] );
      //Debug( c ) << std::endl;
    }
  }
}

Model::Model( TheoryEngine* te, std::string name ) :
d_te( te ),
d_equalityEngine( te->getSatContext(), name ){
  d_useConstantReps = true;
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

void Model::initialize(){
  //reset
  d_reps.clear();
  d_ra.clear();
  //collect model info from the theory engine
  d_te->collectModelInfo( this );
  //populate term database, store representatives
  std::vector< Node > unresolvedReps;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    Node rep;
    if( !d_useConstantReps ){
      rep = eqc;
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ){
      //model-specific add term
      addTerm( *eqc_i );
      //if constant, use this as representative
      if( d_useConstantReps && (*eqc_i).getMetaKind()==kind::metakind::CONSTANT ){
        rep = *eqc_i;
      }
      ++eqc_i;
    }
    //store representative in representative set
    if( !rep.isNull() ){
      d_reps[ eqc ] = rep;
      d_ra.add( rep );
    }else{
      unresolvedReps.push_back( eqc );
    }
    ++eqcs_i;
  }
  if( d_useConstantReps ){
    //now, create constants for all unresolved equivalence classes
    for( size_t i = 0; i<unresolvedReps.size(); i++ ){
      Node n = unresolvedReps[i];
      TypeNode tn = n.getType();
      Node rep = getArbitraryValue( tn, d_ra.d_type_reps[tn] );
      d_reps[ n ] = rep;
      d_ra.add( rep );
    }
  }
  //do model-specific initialization
  processInitialize();
}

Node Model::getValue( TNode n ){
  //must be using constant representatives option
  Assert( d_useConstantReps );
  kind::MetaKind metakind = n.getMetaKind();

  // special case: prop engine handles boolean vars
  if(metakind == kind::metakind::VARIABLE && n.getType().isBoolean()) {
    return d_te->getPropEngine()->getValue( n );
  }

  // special case: value of a constant == itself
  if(metakind == kind::metakind::CONSTANT) {
    return n;
  }

  // see if the theory has a built-in interpretation
  Theory* th = d_te->theoryOf( n );
  if( th->hasInterpretedValue( n ) ){
    std::vector< Node > children;
    if( n.hasOperator() ){
      children.push_back( n.getOperator() );
    }
    //first, evaluate the children
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      children.push_back( getValue( n ) );
    }
    //interpretation is the rewritten form
    Node nn = NodeManager::currentNM()->mkNode( n.getKind(), children );
    return Rewriter::rewrite( nn );
  }

  //case for equality
  if( n.getKind()==EQUAL ){
    Node n1 = getValue( n[0] );
    Node n2 = getValue( n[1] );
    return NodeManager::currentNM()->mkConst( n1==n2 );
  }

  // see if the value is explicitly set in the model
  if( d_equalityEngine.hasTerm( n ) ){
    return getRepresentative( n );
  }

  //otherwise, get the interpreted value in the model
  return getInterpretedValue( n );
}

Node Model::getArbitraryValue( TypeNode tn, std::vector< Node >& exclude ){
  if( tn==NodeManager::currentNM()->booleanType() ){
    if( exclude.empty() ){
      return d_false;
    }else if( exclude.size()==1 ){
      return NodeManager::currentNM()->mkConst( areEqual( exclude[0], d_false ) );
    }
  }else if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
    int val = 0;
    do{
      Node r = NodeManager::currentNM()->mkConst( Rational(val) );
      if( std::find( exclude.begin(), exclude.end(), r )==exclude.end() ){
        return r;
      }
      val++;
    }while( true );
  }else if( d_ra.d_type_reps.find( tn )!=d_ra.d_type_reps.end() ){
    //finite domain, find an arbitrary element
    for( size_t i=0; i<d_ra.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_ra.d_type_reps[tn][i] )==exclude.end() ){
        return d_ra.d_type_reps[tn][i];
      }
    }
    //otherwise must make a constant DO_THIS
  }
  return Node::null();
}

/** assert equality */
void Model::assertEquality( Node a, Node b, bool polarity ){
  d_equalityEngine.assertEquality( a.eqNode(b), polarity, Node::null() );
}

/** assert predicate */
void Model::assertPredicate( Node a, bool polarity ){
  d_equalityEngine.assertPredicate( a, polarity, Node::null() );
}

/** assert equality engine */
void Model::assertEqualityEngine( eq::EqualityEngine* ee ){
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predPolarity = false;
    if( eqc.getType()==NodeManager::currentNM()->booleanType() ){
      predicate = true;
      predPolarity = ee->areEqual( eqc, d_true );
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

bool Model::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

Node Model::getRepresentative( Node a ){
  return d_reps[ d_equalityEngine.getRepresentative( a ) ];
}

bool Model::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool Model::areDisequal( Node a, Node b ){
  if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

//for debugging
void Model::printRepresentative( const char* c, Node r ){
  Assert( !r.isNull() );
  if( r.isNull() ){
    Debug( c ) << "null";
  }else if( r.getType()==NodeManager::currentNM()->booleanType() ){
    if( areEqual( r, NodeManager::currentNM()->mkConst( true ) ) ){
      Debug( c ) << "true";
    }else{
      Debug( c ) << "false";
    }
  }else{
    Debug( c ) << getRepresentative( r );
  }
}

DefaultModel::DefaultModel( TheoryEngine* te, std::string name ) : Model( te, name ){

}

Node DefaultModel::getInterpretedValue( TNode n ){
  TypeNode t = n.getType();
  std::vector< Node > v_emp;
  Node n2 = getArbitraryValue( t, v_emp );
  if( !n2.isNull() ){
    return getRepresentative( n2 );
  }else{
    return n;
  }
}

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

void RepSet::toStream(std::ostream& out){
#if 0
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    out << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      out << "   " << i << ": " << it->second[i] << std::endl;
    }
  }
#else
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    if( !it->first.isFunction() && !it->first.isPredicate() ){
      out << "(" << it->first << " " << it->second.size() << " (";
      for( int i=0; i<(int)it->second.size(); i++ ){
        if( i>0 ){ out << " "; }
        out << it->second[i];
      }
      out << "))" << std::endl;
    }
  }
#endif
}

TheoryModel::TheoryModel( context::Context* c, std::string name ) :
d_equalityEngine( c, name ){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

bool TheoryModel::hasInterpretedValue( Node n ) {
  return false;
}

Node TheoryModel::getValue( TNode n ){
  Debug("model") << "TheoryModel::getValue " << n << std::endl;

  kind::MetaKind metakind = n.getMetaKind();

  //// special case: prop engine handles boolean vars
  //if(metakind == kind::metakind::VARIABLE && n.getType().isBoolean()) {
  //  Debug("model") << "-> Propositional variable." << std::endl;
  //  return d_te->getPropEngine()->getValue( n );
  //}

  // special case: value of a constant == itself
  if(metakind == kind::metakind::CONSTANT) {
    Debug("model") << "-> Constant." << std::endl;
    return n;
  }

  // see if the model has an interpretation for this node
  if( hasInterpretedValue( n ) ){
    Debug("model") << "-> Model-interpreted term." << std::endl;
    //otherwise, get the interpreted value in the model
    return getInterpretedValue( n );
  }

  // see if the value is explicitly set in the model
  if( d_equalityEngine.hasTerm( n ) ){
    Debug("model") << "-> Defined term." << std::endl;
    return getRepresentative( n );
  }else{
    Debug("model") << "-> Theory-interpreted term." << std::endl;
    Node nn;
    if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      if( metakind == kind::metakind::PARAMETERIZED ){
        Debug("model-debug") << "get operator: " << n.getOperator() << std::endl;
        children.push_back( n.getOperator() );
      }
      //evaluate the children
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        Node val = getValue( n[i] );
        Debug("model-debug") << i << " : " << n[i] << " -> " << val << std::endl;
        Assert( !val.isNull() );
        children.push_back( val );
      }
      Debug("model-debug") << "Done eval children" << std::endl;
      //interpretation is the rewritten form
      nn = NodeManager::currentNM()->mkNode( n.getKind(), children );
    }else{
      nn = n;
    }
    Debug("model-debug") << "Interpreted symbol value: " << nn << std::endl;
    return Rewriter::rewrite( nn );
  }

  ////case for equality
  //if( n.getKind()==EQUAL ){
  //  Debug("model") << "-> Equality." << std::endl;
  //  Node n1 = getValue( n[0] );
  //  Node n2 = getValue( n[1] );
  //  return NodeManager::currentNM()->mkConst( n1==n2 );
  //}
}

Node TheoryModel::getDomainValue( TypeNode tn, std::vector< Node >& exclude ){
  if( d_ra.d_type_reps.find( tn )!=d_ra.d_type_reps.end() ){
    //try to find a pre-existing arbitrary element
    for( size_t i=0; i<d_ra.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_ra.d_type_reps[tn][i] )==exclude.end() ){
        return d_ra.d_type_reps[tn][i];
      }
    }
  }
  return Node::null();
}

Node TheoryModel::getNewDomainValue( TypeNode tn, bool mkConst ){
  if( tn==NodeManager::currentNM()->booleanType() ){
    if( d_ra.d_type_reps[tn].empty() ){
      return d_false;
    }else if( d_ra.d_type_reps[tn].size()==1 ){
      return NodeManager::currentNM()->mkConst( areEqual( d_ra.d_type_reps[tn][0], d_false ) );
    }else{
      return Node::null();
    }
  }else if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
    int val = 0;
    do{
      Node r = NodeManager::currentNM()->mkConst( Rational(val) );
      if( std::find( d_ra.d_type_reps[tn].begin(), d_ra.d_type_reps[tn].end(), r )==d_ra.d_type_reps[tn].end() &&
          !d_equalityEngine.hasTerm( r ) ){
        return r;
      }
      val++;
    }while( true );
  }else{
    //otherwise must make a variable  FIXME: how to make constants for other sorts?
    //return NodeManager::currentNM()->mkVar( tn );
    return Node::null();
  }
}

/** assert equality */
void TheoryModel::assertEquality( Node a, Node b, bool polarity ){
  d_equalityEngine.assertEquality( a.eqNode(b), polarity, Node::null() );
}

/** assert predicate */
void TheoryModel::assertPredicate( Node a, bool polarity ){
  if( a.getKind()==EQUAL ){
    assertEquality( a[0], a[1], polarity );
  }else{
    d_equalityEngine.assertPredicate( a, polarity, Node::null() );
  }
}

/** assert equality engine */
void TheoryModel::assertEqualityEngine( eq::EqualityEngine* ee ){
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predPolarity = false;
    if( eqc.getType()==NodeManager::currentNM()->booleanType() ){
      predicate = true;
      predPolarity = ee->areEqual( eqc, d_true );
      //FIXME: do we guarentee that all boolean equivalence classes contain either d_true or d_false?
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

bool TheoryModel::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

Node TheoryModel::getRepresentative( Node a ){
  if( d_equalityEngine.hasTerm( a ) ){
    return d_reps[ d_equalityEngine.getRepresentative( a ) ];
  }else{
    return a;
  }
}

bool TheoryModel::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryModel::areDisequal( Node a, Node b ){
  if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

//for debugging
void TheoryModel::printRepresentativeDebug( const char* c, Node r ){
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

void TheoryModel::printRepresentative( std::ostream& out, Node r ){
  Assert( !r.isNull() );
  if( r.isNull() ){
    out << "null";
  }else if( r.getType()==NodeManager::currentNM()->booleanType() ){
    if( areEqual( r, NodeManager::currentNM()->mkConst( true ) ) ){
      out  << "true";
    }else{
      out  << "false";
    }
  }else{
    out << getRepresentative( r );
  }
}

void TheoryModel::toStream(std::ostream& out){

}

DefaultModel::DefaultModel( context::Context* c, std::string name ) : TheoryModel( c, name ){

}

Node DefaultModel::getInterpretedValue( TNode n ){
  TypeNode type = n.getType();
  if( type.isFunction() || type.isPredicate() ){
    //DO_THIS?
    return n;
  }else{
    std::vector< Node > v_emp;
    Node n2 = getDomainValue( type, v_emp );
    if( !n2.isNull() ){
      return n2;
    }else{
      n2 = getNewDomainValue( type, true );
      if( !n2.isNull() ){
        return n2;
      }else{
        return n;
      }
    }
  }
}

void DefaultModel::toStream(std::ostream& out){
  //print everything in equality engine
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    Node rep = getRepresentative( eqc );
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ){
      if( (*eqc_i).getMetaKind()!=kind::metakind::CONSTANT ){
        out << "(" << (*eqc_i) << " " << rep << ")" << std::endl;
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
}

void IncompleteModel::toStream(std::ostream& out){

}

TheoryEngineModelBuilder::TheoryEngineModelBuilder( TheoryEngine* te ) : d_te( te ){
  d_useConstantReps = true;
}

void TheoryEngineModelBuilder::buildModel( Model* m ){
  TheoryModel* tm = (TheoryModel*)m;
  //reset representative information
  tm->d_reps.clear();
  tm->d_ra.clear();
  Debug( "model-builder" ) << "TheoryEngineModelBuilder: Collect model info..." << std::endl;
  //collect model info from the theory engine
  d_te->collectModelInfo( tm );
    Debug( "model-builder" ) << "TheoryEngineModelBuilder: Build representatives..." << std::endl;
  //populate term database, store representatives
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &tm->d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    Node rep;
    if( !d_useConstantReps ){
      rep = eqc;
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &tm->d_equalityEngine );
    while( !eqc_i.isFinished() ){
      //model-specific add term
      tm->addTerm( *eqc_i );
      //if constant, use this as representative
      if( d_useConstantReps && (*eqc_i).getMetaKind()==kind::metakind::CONSTANT ){
        rep = *eqc_i;
      }
      ++eqc_i;
    }
    //store representative in representative set
    if( !rep.isNull() ){
      tm->d_reps[ eqc ] = rep;
      tm->d_ra.add( rep );
    }else{
      d_unresolvedReps.push_back( eqc );
    }
    ++eqcs_i;
  }
  Debug( "model-builder" ) << "TheoryEngineModelBuilder: Complete model..." << std::endl;
  //do model-specific initialization
  processBuildModel( tm );
}

void TheoryEngineModelBuilder::processBuildModel( TheoryModel* m ){
  //now, create constants for all unresolved equivalence classes
  for( size_t i = 0; i<d_unresolvedReps.size(); i++ ){
    Node n = d_unresolvedReps[i];
    TypeNode tn = n.getType();
    Node rep = m->getNewDomainValue( tn, true );
    if( !rep.isNull() ){
      m->assertEquality( n, rep, true );
      m->d_reps[ n ] = rep;
      m->d_ra.add( rep );
    }else{
      m->d_reps[ n ] = n;
      m->d_ra.add( n );
    }
  }
  d_unresolvedReps.clear();
}
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
#include "theory/type_enumerator.h"
#include "smt/model_format_mode.h"
#include "smt/options.h"
#include "theory/uf/theory_uf_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

TheoryModel::TheoryModel( context::Context* c, std::string name ) :
d_equalityEngine( c, name ){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
  // The kinds we are treating as function application in congruence
  //d_equalityEngine.addFunctionKind(kind::APPLY_UF);
  //d_equalityEngine.addFunctionKind(kind::SELECT);
  //d_equalityEngine.addFunctionKind(kind::STORE);
  //d_equalityEngine.addFunctionKind(kind::APPLY_CONSTRUCTOR);
  //d_equalityEngine.addFunctionKind(kind::APPLY_SELECTOR);
  //d_equalityEngine.addFunctionKind(kind::APPLY_TESTER);
}

void TheoryModel::reset(){
  d_reps.clear();
  d_rep_set.clear();
}

void TheoryModel::addDefineFunction( Node n ){
  d_define_funcs.push_back( n );
  d_defines.push_back( 0 );
}

void TheoryModel::addDefineType( TypeNode tn ){
  d_define_types.push_back( tn );
  d_defines.push_back( 1 );
}

void TheoryModel::addDefineDatatypes( std::vector< TypeNode >& dts ){
  std::vector< TypeNode > dts_copy;
  dts_copy.insert( dts_copy.begin(), dts.begin(), dts.end() );
  d_define_datatypes.push_back( dts_copy );
  d_defines.push_back( 2 );
}

void TheoryModel::toStreamFunction( Node n, std::ostream& out ){
  TypeNode tn = n.getType();
  out << "(define-fun " << n << " (";
  if( tn.isFunction() || tn.isPredicate() ){
    for( size_t i=0; i<tn.getNumChildren()-1; i++ ){
      if( i>0 ) out << " ";
      out << "($x" << (i+1) << " " << tn[i] << ")";
    }
    out << ") " << tn.getRangeType();
  }else{
    out << ") " << tn;
  }
  out << " ";
  out << getValue( n );
  out << ")" << std::endl;
}

/*
  bool printedModel = false;
  if( tn.isFunction() ){
    if( options::modelFormatMode()==MODEL_FORMAT_MODE_TABLE ){
      //specialized table format for functions
      RepSetIterator riter( &d_rep_set );
      riter.setFunctionDomain( n );
      while( !riter.isFinished() ){
        std::vector< Node > children;
        children.push_back( n );
        for( int i=0; i<riter.getNumTerms(); i++ ){
          children.push_back( riter.getTerm( i ) );
        }
        Node nn = NodeManager::currentNM()->mkNode( APPLY_UF, children );
        Node val = getValue( nn );
        out << val << " ";
        riter.increment();
      }
      printedModel = true;
    }
  }
*/

void TheoryModel::toStreamType( TypeNode tn, std::ostream& out ){
  if( tn.isSort() ){
    if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() ){
      out << "; cardinality of " << tn << " is " << d_rep_set.d_type_reps[tn].size() << std::endl;
    }
  }
  out << "(declare-sort " << tn << " " << tn.getNumChildren() << ")" << std::endl;
  if( tn.isSort() ){
    if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() ){
      for( size_t i=0; i<d_rep_set.d_type_reps[tn].size(); i++ ){
        if( d_rep_set.d_type_reps[tn][i].getMetaKind()==metakind::VARIABLE ){
          out << "(declare-fun " << d_rep_set.d_type_reps[tn][i] << " () " << tn << ")" << std::endl;
        }else{
          out << "; rep: " << d_rep_set.d_type_reps[tn][i] << std::endl;
        }
      }
    }
  }
}

void TheoryModel::toStreamDatatypes( std::vector< TypeNode >& dts, std::ostream& out ){
  //DatatypeDeclarationCommand ddc(
  out << "(declare-datatypes () (";
  if( dts.size()>1 ) out << std::endl;
  for( size_t i=0; i<dts.size(); i++ ){
    if( dts.size()>1 ) out << "   ";
    const Datatype& dt = ((DatatypeType)dts[i].toType()).getDatatype();
    out << "(" << dt.getName() << " ";
    for(Datatype::const_iterator ctor = dt.begin(), ctor_end = dt.end(); ctor != ctor_end; ++ctor){
      if( ctor!=dt.begin() ) out << " ";
      out << "(" << ctor->getName();
      for(DatatypeConstructor::const_iterator arg = ctor->begin(), arg_end = ctor->end(); arg != arg_end; ++arg){
        out << " (" << arg->getSelector() << " " << static_cast<SelectorType>(arg->getType()).getRangeType() << ")";
      }
      out << ")";
    }
    out << ")";
    if( dts.size()>1 ) out << std::endl;
  }
  out << "))" << std::endl;
}

void TheoryModel::toStream( std::ostream& out ){
  /*//for debugging
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    Debug("get-model-debug") << eqc << " : " << eqc.getType() << " : " << std::endl;
    out << "   ";
    //add terms to model
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ){
      out << (*eqc_i) << " ";
      ++eqc_i;
    }
    out << std::endl;
    ++eqcs_i;
  }
  */
  int funcIndex = 0;
  int typeIndex = 0;
  int dtIndex = 0;
  for( size_t i=0; i<d_defines.size(); i++ ){
    if( d_defines[i]==0 ){
      TypeNode tn = d_define_funcs[funcIndex].getType();
      //do not print if it has already been printed as a representative
      if( !tn.isSort() || !d_rep_set.hasType( tn ) || d_rep_set.getIndexFor( d_define_funcs[funcIndex] )==-1 ){
        toStreamFunction( d_define_funcs[funcIndex], out );
      }
      funcIndex++;
    }else if( d_defines[i]==1 ){
      toStreamType( d_define_types[typeIndex], out );
      typeIndex++;
    }else if( d_defines[i]==2 ){
      toStreamDatatypes( d_define_datatypes[dtIndex], out );
      dtIndex++;
    }
  }
}

Node TheoryModel::getValue( TNode n ){
  Debug("model") << "TheoryModel::getValue " << n << std::endl;

  //// special case: prop engine handles boolean vars
  //if(metakind == kind::metakind::VARIABLE && n.getType().isBoolean()) {
  //  Debug("model") << "-> Propositional variable." << std::endl;
  //  return d_te->getPropEngine()->getValue( n );
  //}

  // special case: value of a constant == itself
  if( n.isConst() ) {
    Debug("model") << "-> Constant." << std::endl;
    return n;
  }

  Node nn;
  if( n.getNumChildren()>0 ){
    std::vector< Node > children;
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
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
    nn = NodeManager::currentNM()->mkNode( n.getKind(), children );
  }else{
    nn = n;
  }
  //interpretation is the rewritten form
  nn = Rewriter::rewrite( nn );

  // special case: value of a constant == itself
  if( nn.isConst() ) {
    Debug("model") << "-> Theory-interpreted term." << std::endl;
    return nn;
  }else{
    Debug("model") << "-> Model-interpreted term." << std::endl;
    //otherwise, get the interpreted value in the model
    return getInterpretedValue( nn );
  }
}

Node TheoryModel::getDomainValue( TypeNode tn, std::vector< Node >& exclude ){
  if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() ){
    //try to find a pre-existing arbitrary element
    for( size_t i=0; i<d_rep_set.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_rep_set.d_type_reps[tn][i] )==exclude.end() ){
        return d_rep_set.d_type_reps[tn][i];
      }
    }
  }
  return Node::null();
}

//FIXME: use the theory enumerator to generate constants here
Node TheoryModel::getNewDomainValue( TypeNode tn ){
#if 1
  if( tn==NodeManager::currentNM()->booleanType() ){
    if( d_rep_set.d_type_reps[tn].empty() ){
      return d_false;
    }else if( d_rep_set.d_type_reps[tn].size()==1 ){
      return NodeManager::currentNM()->mkConst( areEqual( d_rep_set.d_type_reps[tn][0], d_false ) );
    }else{
      return Node::null();
    }
  }else if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
    int val = 0;
    do{
      Node r = NodeManager::currentNM()->mkConst( Rational(val) );
      if( std::find( d_rep_set.d_type_reps[tn].begin(), d_rep_set.d_type_reps[tn].end(), r )==d_rep_set.d_type_reps[tn].end() &&
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
#else
  if( tn.isSort() ){
    return Node::null();
  }else{
    TypeEnumerator te(tn);
    while( !te.isFinished() ){
      Node r = *te;
      if(Debug.isOn("getNewDomainValue")) {
        Debug("getNewDomainValue") << "getNewDomainValue( " << tn << ")" << endl;
        Debug("getNewDomainValue") << "+ TypeEnumerator gave: " << r << endl;
        Debug("getNewDomainValue") << "+ d_type_reps are:";
        for(vector<Node>::const_iterator i = d_rep_set.d_type_reps[tn].begin();
            i != d_rep_set.d_type_reps[tn].end();
            ++i) {
          Debug("getNewDomainValue") << " " << *i;
        }
        Debug("getNewDomainValue") << endl;
      }
      if( std::find(d_rep_set.d_type_reps[tn].begin(), d_rep_set.d_type_reps[tn].end(), r) ==d_rep_set.d_type_reps[tn].end() ) {
        Debug("getNewDomainValue") << "+ it's new, so returning " << r << endl;
        return r;
      }
      ++te;
    }
    return Node::null();
  }
#endif
}

/** assert equality */
void TheoryModel::assertEquality( Node a, Node b, bool polarity ){
  d_equalityEngine.assertEquality( a.eqNode(b), polarity, Node::null() );
}

/** assert predicate */
void TheoryModel::assertPredicate( Node a, bool polarity ){
  if( a.getKind()==EQUAL ){
    d_equalityEngine.assertEquality( a, polarity, Node::null() );
  }else{
    d_equalityEngine.assertPredicate( a, polarity, Node::null() );
  }
}

/** assert equality engine */
void TheoryModel::assertEqualityEngine( const eq::EqualityEngine* ee ){
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predPolarity = false;
    if( eqc.getType().isBoolean() ){
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

void TheoryModel::assertRepresentative( Node n ){
  Trace("model-builder-reps") << "Assert rep : " << n << std::endl;
  d_reps[ n ] = n;
}

bool TheoryModel::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

Node TheoryModel::getRepresentative( Node a ){
  if( d_equalityEngine.hasTerm( a ) ){
    Node r = d_equalityEngine.getRepresentative( a );
    if( d_reps.find( r )!=d_reps.end() ){
      return d_reps[ r ];
    }else{
      return r;
    }
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
  if( r.isNull() ){
    Debug( c ) << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
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
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      out  << "true";
    }else{
      out  << "false";
    }
  }else{
    out << getRepresentative( r );
  }
}

DefaultModel::DefaultModel( context::Context* c, std::string name, bool enableFuncModels ) :
TheoryModel( c, name ), d_enableFuncModels( enableFuncModels ){

}

void DefaultModel::addTerm( Node n ){
  //must collect UF terms
  if( d_enableFuncModels && n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( std::find( d_uf_terms[ op ].begin(), d_uf_terms[ op ].end(), n )==d_uf_terms[ op ].end() ){
      d_uf_terms[ op ].push_back( n );
    }
  }
}

void DefaultModel::reset(){
  d_uf_terms.clear();
  d_uf_models.clear();
  TheoryModel::reset();
}

Node DefaultModel::getInterpretedValue( TNode n ){
  TypeNode type = n.getType();
  if( type.isFunction() || type.isPredicate() ){
    //for function models
    if( d_enableFuncModels ){
      if( d_uf_models.find( n )==d_uf_models.end() ){
        uf::UfModelTree ufmt( n );
        Node default_v;
        for( size_t i=0; i<d_uf_terms[n].size(); i++ ){
          Node un = d_uf_terms[n][i];
          Node v = getRepresentative( un );
          ufmt.setValue( this, un, v );
          default_v = v;
        }
        if( default_v.isNull() ){
          default_v = getInterpretedValue( NodeManager::currentNM()->mkVar( type.getRangeType() ) );
        }
        ufmt.setDefaultValue( this, default_v );
        ufmt.simplify();
        Node fn = ufmt.getFunctionValue();
        d_uf_models[n] = uf::UfModelTree::toIte( type, fn, "$x" );
      }
      return d_uf_models[n];
    }else{
      return n;
    }
  }else{
    //first, see if the representative is defined
    if( d_equalityEngine.hasTerm( n ) ){
      n = d_equalityEngine.getRepresentative( n );
      //this check is required since d_equalityEngine.hasTerm( n )
      // does not ensure that n is in an equivalence class in d_equalityEngine
      if( d_reps.find( n )!=d_reps.end() ){
        return d_reps[n];
      }
    }
    //second, try to choose an existing term as value
    std::vector< Node > v_emp;
    Node n2 = getDomainValue( type, v_emp );
    if( !n2.isNull() ){
      return n2;
    }else{
      //otherwise, choose new value
      n2 = getNewDomainValue( type );
      if( !n2.isNull() ){
        return n2;
      }else{
        //otherwise, just return itself (this usually should not happen)
        return n;
      }
    }
  }
}

TheoryEngineModelBuilder::TheoryEngineModelBuilder( TheoryEngine* te ) : d_te( te ){

}

void TheoryEngineModelBuilder::buildModel( Model* m, bool fullModel ){
  TheoryModel* tm = (TheoryModel*)m;
  //reset representative information
  tm->reset();
  //collect model info from the theory engine
  Trace("model-builder") << "TheoryEngineModelBuilder: Collect model info..." << std::endl;
  d_te->collectModelInfo( tm, fullModel );
  Trace("model-builder") << "Collect representatives..." << std::endl;
  //store asserted representative map
  std::map< Node, Node > assertedReps;
  //process all terms in the equality engine, store representatives
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &tm->d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    if( assertedReps.find( eqc )!=assertedReps.end() ){
      Trace("model-warn") << "Duplicate equivalence class!!!! " << eqc << std::endl;
    }else{
      TypeNode eqct = eqc.getType();
      Node const_rep;
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &tm->d_equalityEngine );
      while( !eqc_i.isFinished() ){
        Node n = *eqc_i;
        //if this node was specified as a representative
        if( tm->d_reps.find( n )!=tm->d_reps.end() ){
          Assert( !tm->d_reps[n].isNull() );
          //if not already specified
          if( assertedReps.find( eqc )==assertedReps.end() ){
            Trace("model-builder") << "Rep( " << eqc << " ) = " << tm->d_reps[n] << std::endl;
            assertedReps[ eqc ] = tm->d_reps[n];
          }else{
            if( n!=assertedReps[eqc] ){   //FIXME : this should be an assertion, EqClassIterator should not give duplicates
              //duplicate representative specified
              Trace("model-warn") << "Duplicate representative specified for equivalence class " << eqc << ": " << std::endl;
              Trace("model-warn") << "      " << assertedReps[eqc] << ", " << n << std::endl;
              Trace("model-warn") << "  Type : " << n.getType() << std::endl;
            }
          }
        }else if( n.isConst() ){
          //if this is constant, we will use it as representative (if none other specified)
          const_rep = n;
        }
        //model-specific processing of the term
        tm->addTerm( n );
        ++eqc_i;
      }
      //if a representative was not specified
      if( assertedReps.find( eqc )==assertedReps.end() ){
        if( !const_rep.isNull() ){
          //use the constant representative
          assertedReps[ eqc ] = const_rep;
        }else{
          if( fullModel ){
            //assertion failure?
            Trace("model-warn") << "No representative specified for equivalence class " << eqc << std::endl;
            Trace("model-warn") << "  Type : " << eqc.getType() << std::endl;
          }
          //assertedReps[ eqc ] = chooseRepresentative( tm, eqc, fullModel );
          assertedReps[ eqc ] = eqc;
        }
      }
    }
    ++eqcs_i;
  }
  Trace("model-builder") << "Normalize representatives..." << std::endl;
  //now, normalize all representatives
  // this will make every leaf of asserted representatives into a representative
  std::map< Node, bool > normalized;
  for( std::map< Node, Node >::iterator it = assertedReps.begin(); it != assertedReps.end(); ++it ){
    std::map< Node, bool > normalizing;
    normalizeRepresentative( tm, it->first, assertedReps, normalized, normalizing );
  }
  Trace("model-builder") << "Copy representatives to model..." << std::endl;
  //assertedReps has the actual representatives we will use, now copy back to model
  tm->d_reps.clear();
  for( std::map< Node, Node >::iterator it = assertedReps.begin(); it != assertedReps.end(); ++it ){
    tm->d_reps[ it->first ] = it->second;
    tm->d_rep_set.add( it->second );
  }

  //model-specific initialization
  processBuildModel( tm, fullModel );
}

Node TheoryEngineModelBuilder::chooseRepresentative( TheoryModel* m, Node eqc, bool fullModel ){
  //try to get a new domain value
  Node rep = m->getNewDomainValue( eqc.getType() );
  if( !rep.isNull() ){
    return rep;
  }else{
    //if we can't get new domain value, just return eqc itself (this typically should not happen)
    //FIXME: Assertion failure here?
    return eqc;
  }
}

Node TheoryEngineModelBuilder::normalizeRepresentative( TheoryModel* m, Node r, std::map< Node, Node >& reps,
                                                        std::map< Node, bool >& normalized,
                                                        std::map< Node, bool >& normalizing ){
  Trace("temb-normalize") << r << std::endl;
  if( normalized.find( r )!=normalized.end() ){
    //Message() << " -> already normalized, return " << reps[r] << std::endl;
    return reps[r];
  }else if( normalizing.find( r )!=normalizing.end() && normalizing[r] ){
    //TODO: this case is only temporary to handle things like when store( A, e, i ) is given
    //       as a representative for array A.
    //Message() << " -> currently normalizing, give up : " << r << std::endl;
    return r;
  }else if( reps.find( r )!=reps.end() ){
    normalizing[ r ] = true;
    Node retNode = normalizeNode( m, reps[r], reps, normalized, normalizing );
    normalizing[ r ] = false;
    //Message() << " --> returned " << retNode << " for " << r << std::endl;
    normalized[ r ] = true;
    reps[ r ] = retNode;
    return retNode;
  }else if( m->d_equalityEngine.hasTerm( r ) ){
    normalizing[ r ] = true;
    //return the normalized representative from the model
    r = m->d_equalityEngine.getRepresentative( r );
    //Message() << " -> it is the representative " << r << std::endl;
    Node retNode = normalizeRepresentative( m, r, reps, normalized, normalizing );
    normalizing[ r ] = false;
    return retNode;
  }else{
    if( !r.isConst() ){
      Trace("model-warn") << "Normalizing representative, unknown term: " << r << std::endl;
      Trace("model-warn") << "  Type : " << r.getType() << std::endl;
      Trace("model-warn") << "  Kind : " << r.getKind() << std::endl;
      normalizing[ r ] = true;
      r = normalizeNode( m, r, reps, normalized, normalizing );
      normalizing[ r ] = false;
    }
    //Message() << " -> unknown, return " << r << std::endl;
    return r;
  }
}

Node TheoryEngineModelBuilder::normalizeNode( TheoryModel* m, Node r, std::map< Node, Node >& reps,
                                              std::map< Node, bool >& normalized,
                                              std::map< Node, bool >& normalizing ){
  if( r.getNumChildren()>0 ){
    //Message() << " ---> normalize " << r << " " << r.getNumChildren() << " " << r.getKind() << std::endl;
    //non-leaf case: construct representative from children
    std::vector< Node > children;
    if( r.getMetaKind() == kind::metakind::PARAMETERIZED ){
      children.push_back( r.getOperator() );
    }
    for( size_t i=0; i<r.getNumChildren(); i++ ){
      Node ri = normalizeRepresentative( m, r[i], reps, normalized, normalizing );
      children.push_back( ri );
    }
    Node retNode = NodeManager::currentNM()->mkNode( r.getKind(), children );
    retNode = Rewriter::rewrite( retNode );
    if( retNode!=r ){
      //assure that it is made equal in the model
      m->assertEquality( r, retNode, true );
    }
    return retNode;
  }else{
    return r;
  }
}
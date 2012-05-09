/*********************                                                        */
/*! \file model_engine.cpp
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
 ** \brief Implementation of model engine class
 **/


#include "theory/quantifiers/model_engine.h"

#include "theory/theory_engine.h"
#include "theory/uf/equality_engine_impl.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
//
//ModelTree::ModelTree( TermArgTrie* tat ){
//  for( std::map< Node, TermArgTrie >::iterator it = tat->d_data.begin(); it != tat->d_data.end(); ++it ){
//    d_data[ it->first ] = ModelTree( &(it->second) );
//  }
//}
//
//ModelTree::ModelTree( TermArgTrie* tat_t, TermArgTrie* tat_f ){
//  
//}

void ModelTree::setValue2( QuantifiersEngine* qe, Node n, Node v, int argIndex ){
  if( argIndex==n.getNumChildren() || isEmpty() ){
    if( d_value!=v && !d_value.isNull() ){
      debugPrint("fmf-temp");
    }
    Assert( d_value==v || d_value.isNull() );
    d_value = v;
    d_explicit.push_back( n );
  }else if( !d_value.isNull() ){
    //a leaf: test whether the value is compatible
    if( d_value==v ){
      d_explicit.push_back( n );
    }else{
      //value is no longer uniform
      d_value = Node::null();
      //now, add n to current
      setValue2( qe, n, v, argIndex );
      //also add those stored explicitly
      for( int i=0; i<(int)d_explicit.size(); i++ ){
        setValue2( qe, d_explicit[i], v, argIndex );
      }
      d_explicit.clear();
    }
  }else{
    //take r = null when argument is a pattern
    Node r;
    if( !n[ argIndex ].hasAttribute(InstConstantAttribute()) ){
      r = qe->getEqualityQuery()->getRepresentative( n[ argIndex ] );
    }
    d_data[ r ].setValue2( qe, n, v, argIndex+1 );
  }
}

Node ModelTree::getValue2( QuantifiersEngine* qe, Node n, int& depIndex, int argIndex ){
  if( d_value.isNull() ){
    for( int i=0; i<2; i++ ){
      Node r;
      if( i==0 ){
        r = qe->getEqualityQuery()->getRepresentative( n[ argIndex ] );
      }
      std::map< Node, ModelTree >::iterator it = d_data.find( r );
      if( it!=d_data.end() ){
        Node v = it->second.getValue2( qe, n, depIndex, argIndex+1 );
        if( !v.isNull() ){
          return v;
        }
      }
    }
    return Node::null();
  }else{
    depIndex = argIndex;
    return d_value;
  }
}

void indent( const char* c, int ind ){
  for( int i=0; i<ind; i++ ){
    Debug( c ) << " ";
  }
}
void ModelTree::debugPrint( const char* c, int ind, int arg ){

  if( d_value.isNull() ){
    for( std::map< Node, ModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( !it->first.isNull() ){
        indent( c, ind );
        Debug( c ) << "if x_" << arg << " == " << it->first << std::endl;
        it->second.debugPrint( c, ind+1, arg+1 );
      }
    }
    if( d_data.find( Node::null() )!=d_data.end() ){
      d_data[ Node::null() ].debugPrint( c, ind, arg+1 );
    }
  }else{
    indent( c, ind );
    Debug( c ) << "return " << d_value << " { ";
    for( int i=0; i<(int)d_explicit.size(); i++ ){
      Debug( c ) << d_explicit[i] << " ";
    }
    Debug( c ) << "}" << std::endl;
  }
}

RepAlphabet::RepAlphabet( RepAlphabet& ra, QuantifiersEngine* qe ){
  //translate to current representatives
  for( std::map< TypeNode, std::vector< Node > >::iterator it = ra.d_type_reps.begin(); it != ra.d_type_reps.end(); ++it ){
    std::vector< Node > reps;
    for( int i=0; i<(int)it->second.size(); i++ ){
      //reps.push_back( ie->getEqualityQuery()->getRepresentative( it->second[i] ) );
      reps.push_back( it->second[i] );
    }
    set( it->first, reps );
  }
}

void RepAlphabet::set( TypeNode t, std::vector< Node >& reps ){
  d_type_reps[t].insert( d_type_reps[t].begin(), reps.begin(), reps.end() );
  for( int i=0; i<(int)reps.size(); i++ ){
    d_tmap[ reps[i] ] = i;
  }
}

void RepAlphabet::debugPrint( const char* c ){
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    Debug( c ) << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      Debug( c ) << "   " << i << ": " << it->second[i] << std::endl;
    }
  }
}

RepAlphabetIterator::RepAlphabetIterator( QuantifiersEngine* qe, Node f, ModelEngine* model ) : d_f( f ), d_model( model ){
  d_index.resize( f[0].getNumChildren(), 0 );
  d_model->validate( this );
}

void RepAlphabetIterator::increment( QuantifiersEngine* qe ){
  Assert( !isFinished() );
  int counter = 0;
  //increment d_index
  while( d_index[counter]==(int)(d_model->getReps()->d_type_reps[d_f[0][counter].getType()].size()-1) ){
    d_index[counter] = 0;
    counter++;
    if( counter==(int)d_index.size() ){
      d_index.clear();
      return;
    }
  }
  d_index[counter]++;
  d_model->validate( this );

}

bool RepAlphabetIterator::isFinished(){
  return d_index.empty();
}

void RepAlphabetIterator::getMatch( QuantifiersEngine* ie, InstMatch& m ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    m.d_map[ ie->getInstantiationConstant( d_f, i ) ] = getTerm( i );
  }
}

Node RepAlphabetIterator::getTerm( int i ){
  TypeNode tn = d_f[0][i].getType();
  Assert( d_model->getReps()->d_type_reps.find( tn )!=d_model->getReps()->d_type_reps.end() );
  return d_model->getReps()->d_type_reps[tn][d_index[i]];
}

void RepAlphabetIterator::calculateTerms( QuantifiersEngine* qe ){
  d_terms.clear();
  d_ic.clear();
  for( int i=0; i<qe->getNumInstantiationConstants( d_f ); i++ ){
    d_terms.push_back( getTerm( i ) );
    d_ic.push_back( qe->getInstantiationConstant( d_f, i ) );
  }
}

PredModel::PredModel( Node op, QuantifiersEngine* qe ) : d_op( op ), d_qe( qe ){
  //look at ground assertions
  for( int i=0; i<(int)d_qe->getTermDatabase()->d_op_map[ d_op ].size(); i++ ){
    Node n = d_qe->getTermDatabase()->d_op_map[ d_op ][i];
    if( !n.getAttribute(NoMatchAttribute()) ){
      Node v = d_qe->getEqualityQuery()->getRepresentative( n );
      //std::cout << "Set value " << n << " = " << v << std::endl;
      d_tree.setValue( qe, n, v );
    }
  }
}

void PredModel::addRequirement( Node f, Node p, bool phase ){
  d_reqs[ phase ? 1 : 0 ][ f ].push_back( p );
}

void PredModel::debugPrint( const char* c ){
  Debug( c ) << "Predicate " << d_op << std::endl;
  Debug( c ) << "   Type: " << d_op.getType() << std::endl;
  Debug( c ) << "   Phase reqs:" << std::endl;
  for( int i=0; i<2; i++ ){
    for( std::map< Node, std::vector< Node > >::iterator it = d_reqs[i].begin(); it != d_reqs[i].end(); ++it ){
      Debug( c ) << "      " << it->first << std::endl;
      for( int j=0; j<(int)it->second.size(); j++ ){
        Debug( c ) << "         " << it->second[j] << " -> " << (i==1) << std::endl;
      }
    }
  }
  Node trueNode = NodeManager::currentNM()->mkConst<bool>( true );
  Debug( c ) << std::endl;
  Debug( c ) << "   Ground asserts:" << std::endl;
  for( int i=0; i<(int)d_qe->getTermDatabase()->d_op_map[ d_op ].size(); i++ ){
    Node n = d_qe->getTermDatabase()->d_op_map[ d_op ][i];
    Debug( c ) << "      " << n << " -> ";
    Debug( c ) << d_qe->getEqualityQuery()->areEqual( n, trueNode ) << std::endl;
  }
  Debug( c ) << "   Model:" << std::endl;
  d_tree.debugPrint( c, 6 );
  Debug( c ) << std::endl;
}

FunctionModel::FunctionModel( Node op, QuantifiersEngine* qe ) : d_op( op ), d_qe( qe ){
  //look at ground assertions
  for( int i=0; i<(int)d_qe->getTermDatabase()->d_op_map[ d_op ].size(); i++ ){
    Node n = d_qe->getTermDatabase()->d_op_map[ d_op ][i];
    if( !n.getAttribute(NoMatchAttribute()) ){
      Node v = d_qe->getEqualityQuery()->getRepresentative( n );
      d_tree.setValue( qe, n, v );
    }
  }
}

void FunctionModel::addRequirement( Node f, Node t, Node te, bool phase ){
  d_reqs[ phase ? 1 : 0 ][ f ][ t ].push_back( te );
}

void FunctionModel::debugPrint( const char* c ){
  Debug( c ) << "Function " << d_op << std::endl;
  Debug( c ) << "   Type: " << d_op.getType() << std::endl;
  Debug( c ) << "   Phase reqs:" << std::endl;
  for( int i=0; i<2; i++ ){
    for( std::map< Node, std::map< Node, std::vector< Node > > >::iterator it = d_reqs[i].begin(); it != d_reqs[i].end(); ++it ){
      Debug( c ) << "      " << "For " << it->first << ":" << std::endl;
      for( std::map< Node, std::vector< Node > >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        for( int j=0; j<(int)it2->second.size(); j++ ){
          Debug( c ) << "         " << it2->first << ( i==1 ? "==" : "!=" ) << it2->second[j] << std::endl;
        }
      }
    }
  }
  Debug( c ) << "   Ground asserts:" << std::endl;
  for( int i=0; i<(int)d_qe->getTermDatabase()->d_op_map[ d_op ].size(); i++ ){
    Node n = d_qe->getTermDatabase()->d_op_map[ d_op ][i];
    Node r = d_qe->getEqualityQuery()->getRepresentative( n );
    Debug( c ) << "      " << n << " = ";
    Debug( c ) << r << std::endl;
  }
  Debug( c ) << "   Model:" << std::endl;
  d_tree.debugPrint( c, 6 );
  Debug( c ) << std::endl;
}

ModelEngine::ModelEngine( TheoryQuantifiers* th ){
  d_th = th;
  d_quantEngine = th->getQuantifiersEngine();
  d_ss = ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->getTheory( THEORY_UF ))->getStrongSolver();
}

void ModelEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_LAST_CALL ){
    //build the model
    buildModel();
    //try exhaustive instantiation
    int addedLemmas = 0;
    for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getAssertedQuantifier( i );
      Debug("inst-fmf-debug") << "Add matches for " << f << "..." << std::endl;
      RepAlphabetIterator riter( d_quantEngine, f, this );
      while( !riter.isFinished() ){
        InstMatch m;
        riter.getMatch( d_quantEngine, m );
        riter.increment( d_quantEngine );
        Debug("inst-fmf-debug") << "Try to add match " << std::endl;
        m.debugPrint("inst-fmf-debug");
        if( d_quantEngine->addInstantiation( f, m ) ){
          addedLemmas++;
        }
      }
      Debug("inst-fmf-debug") << "finished." << std::endl;
    }
    d_quantEngine->flushLemmas( &d_th->getOutputChannel() );
    //if( addedLemmas==0 ){
    //  std::cout << "Completed with no instantiations." << std::endl;
    //}
  }
}

void ModelEngine::registerQuantifier( Node f ){

}

void ModelEngine::assertNode( Node f ){

}

void ModelEngine::buildModel(){
  buildRepresentatives();

  ////now analyze quantifiers
  //d_pred_model.clear();
  //d_func_model.clear();
  //for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
  //  Node f = d_quantEngine->getAssertedQuantifier( i );
  //  Debug("fmf-model-req") << "Phase requirements for " << f << ": " << std::endl;
  //  for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
  //       it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
  //    Node n = it->first;
  //    Debug("fmf-model-req") << "   " << n << " -> " << it->second << std::endl;
  //    if( n.getKind()==APPLY_UF ){
  //      processPredicate( f, n, it->second );
  //    }else if( n.getKind()==EQUAL ){
  //      processEquality( f, n, it->second );
  //    }
  //  }
  //}
  //Debug("fmf-model") << "Done." << std::endl;
  //debugPrint("fmf-model-complete");
  ////try to complete model? TODO
  //exit( 0 );

}

void ModelEngine::buildRepresentatives(){
  d_ra.clear();
  Debug("inst-fmf") << "Setting up model find, initialize representatives." << std::endl;
  //std::cout << "Instantiation Round" << std::endl;
  //collect all representatives for all types and store as representative alphabet
  for( int i=0; i<d_ss->getNumCardinalityTypes(); i++ ){
    TypeNode tn = d_ss->getCardinalityType( i );
    std::vector< Node > reps;
    d_ss->getRepresentatives( tn, reps );

    //DO_THIS: prefer previously used reps

    if( (int)reps.size()!=d_ss->getCardinality( tn ) ){
      std::cout << "InstStrategyFinteModelFind::processResetInstantiationRound: Bad representatives for type." << std::endl;
      std::cout << "   " << tn << " has cardinality " << d_ss->getCardinality( tn );
      std::cout << " but only " << (int)reps.size() << " were given." << std::endl;
      exit( 27 );
    }else{
      //std::cout << "   " << tn << " -> " << reps.size() << std::endl;

      Debug("inst-fmf") << "Representatives (" << reps.size() << ") for type " << tn << " (c=" << d_ss->getCardinality( tn ) << "): ";
      for( int i=0; i<(int)reps.size(); i++ ){
        Debug("inst-fmf") << reps[i] << " ";
      }
      Debug("inst-fmf") << std::endl;
      for( int i=0; i<(int)reps.size(); i++ ){
        Debug("inst-fmf-eqc") << "   ";
        ((uf::InstantiatorTheoryUf*)d_quantEngine->getInstantiator( THEORY_UF ))->outputEqClass( "inst-fmf-eqc", reps[i] );
        Debug("inst-fmf-eqc") << std::endl;
      }
      //set them in the alphabet
      d_ra.set( tn, reps );
    }
  }
  Debug("inst-fmf") << std::endl;
}

//this function will probably be removed
void ModelEngine::validate( RepAlphabetIterator* rai ){
  ////see if instantiation is already true in current model
  //int eVal;
  //do{
  //  //calculate represenative terms we are currently considering
  //  rai->calculateTerms( d_quantEngine );
  //  //if eVal is not -1, then the instantiation is already true in the model,
  //  // and eVal is the highest index in rai which we can safely iterate
  //  eVal = evaluate( rai, d_quantEngine->getCounterexampleBody( rai->d_f ), true );
  //  if( eVal!=-1 ){
  //    for( int i=0; i<eVal; i++ ){
  //      rai->d_index[i] = 0;
  //    }
  //    rai->d_index[eVal]++;
  //  }
  //}while( eVal!=-1 );
}

////if evaluate( rai, n, phaseReq ) = eVal,
//// if eVal = -1
////   then the instantiation specified by rai cannot be proven to be equal to phaseReq
//// otherwise,
////   the instantiations {rai->d_index[0]...rai->d_index[eVal], * .... *} are equal to phaseReq in the current model
//int ModelEngine::evaluate( RepAlphabetIterator* rai, Node n, bool phaseReq, std::vector< Node >& modelExt ){
//  EqualityQuery* q = d_quantEngine->getEqualityQuery();
//  if( n.getKind()==NOT ){
//    return evaluate( rai, n, !phaseReq, modelExt );
//  }else if( n.getKind()==AND || n.getKind()==OR || n.getKind()==IMPLIES ){
//    bool followPhase = ( n.getKind()==AND && !phaseReq ) || ( n.getKind()!=AND && phaseReq );
//    int newVal = followPhase ? -1 : (int)rai->d_index.size();
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      bool newPhaseReq = ( ( n.getKind()==IMPLIES && i==0 ) ? !phaseReq : phaseReq );
//      std::vector< Node > newModelExt;
//      int eVal = evaluate( rai, n[i], newPhaseReq, newModelExt );
//      bool replaceVal, returnVal;
//      if( followPhase ){
//        returnVal = eVal==(int)rai->d_index.size();
//        replaceVal = eVal>newVal;
//      }else{
//        returnVal = eVal==-1;
//        replaceVal = eVal<newVal;
//      }
//      if( replaceVal ){
//        modelExt.clear();
//        modelExt.insert( modelExt.begin(), newModelExt.begin(), newModelExt.end() );
//        newVal = eVal;
//      }
//      if( returnVal ){
//        return eVal;
//      }
//    }
//    return newVal;
//  }else if( n.getKind()==IFF || n.getKind()==XOR ){
//    bool equalPhase = ( n.getKind()==IFF && phaseReq ) || ( n.getKind()==XOR && !phaseReq );
//    int newVal = -1;
//    for( int p=0; p<2; p++ ){
//      int eVal[2];
//      bool success = true;
//      for( int i=0; i<2; i++ ){
//        bool newPhaseReq = equalPhase ? p==0 : p==i;
//        eVal[i] = evaluate( rai, n[i], newPhaseReq );
//        if( eVal[i]<=newVal ){
//          success = false;
//          break;
//        }
//      }
//      if( success ){
//        newVal = ( eVal[0]>eVal[1] ? eVal[1] : eVal[0] );
//      }
//    }
//    return newVal;
//  }else if( n.getKind()==ITE ){
//    int newVal = -1;
//    for( int p=0; p<2; p++ ){
//      int eVal = evaluate( rai, n[0], p==0 );
//      if( eVal>newVal ){
//        int eValC = evaluate( rai, n[p+1], phaseReq );
//        if( eValC>newVal ){
//          newVal = ( eVal>eValC ? eValC : eVal );
//        }
//      }
//    }
//    return newVal;
//  }else if( n.getKind()==EQUAL || n.getKind()==APPLY_UF ){
//    return evaluateLiteral( rai, n, phaseReq );
//  }
//  return -1;
//}
//
//int ModelEngine::evaluateLiteral( RepAlphabetIterator* rai, Node lit, bool phaseReq, std::vector< Node >& modelExt ){
//  Node s_lit = lit;
//  if( lit.hasAttribute(InstConstantAttribute()) ){
//    s_lit = lit.substitute( rai->d_ic.begin(), rai->d_ic.end(), rai->d_terms.begin(), rai->d_terms.end() );
//  }
//  bool success = false;
//  EqualityQuery* q = d_quantEngine->getEqualityQuery();
//  if( s_lit.getKind()==APPLY_UF ){
//    if( q->areEqual( s_lit, NodeManager::currentNM()->mkConst( phaseReq ) ) ){
//      success = true;
//    }else{
//      //look at complete model? TODO
//    }
//  }else if( s_lit.getKind()==EQUAL ){
//    if( phaseReq && q->areEqual( s_lit[0], s_lit[1] ) ){
//      success = true;
//    }else if( !phaseReq && q->areDisequal( s_lit[0], s_lit[1] ) ){
//      success = true;
//    }else{
//      //look at complete model? TODO
//    }
//  }
//  if( success ){
//    std::vector< Node > fv;
//    if( lit.hasAttribute(InstConstantAttribute()) ){
//      Trigger::getVarContainsNode( rai->d_f, lit, fv );
//    }
//    int minIndex = (int)rai->d_index.size();
//    for( int i=0; i<(int)fv.size(); i++ ){
//      int index = fv[i].getAttribute(InstVarNumAttribute());
//      if( index==0 ){
//        return 0;
//      }else if( index<minIndex ){
//        minIndex = index;
//      }
//    }
//    //try to generalize?  TODO
//    return minIndex;
//  }else{
//    return -1;
//  }
//}


void ModelEngine::processPredicate( Node f, Node p, bool phase ){
  Node op = p.getOperator();
  if( d_pred_model.find( op )==d_pred_model.end() ){
    d_pred_model[ op ] = PredModel( op, d_quantEngine );
  }
  d_pred_model[ op ].addRequirement( f, p, phase );
}

void ModelEngine::processEquality( Node f, Node eq, bool phase ){
  if( eq[0].getKind()==APPLY_UF && eq[0].hasAttribute(InstConstantAttribute()) ){
    Node op = eq[0].getOperator();
    if( d_func_model.find( op )==d_func_model.end() ){
      d_func_model[ op ] = FunctionModel( op, d_quantEngine );
    }
    d_func_model[ op ].addRequirement( f, eq[0], eq[1], phase );
  }
  if( eq[1].getKind()==APPLY_UF && eq[1].hasAttribute(InstConstantAttribute()) ){
    Node op = eq[1].getOperator();
    if( d_func_model.find( op )==d_func_model.end() ){
      d_func_model[ op ] = FunctionModel( op, d_quantEngine );
    }
    d_func_model[ op ].addRequirement( f, eq[1], eq[0], phase );
  }
}

void ModelEngine::debugPrint( const char* c ){
  Debug( c ) << "Representatives: " << std::endl;
  d_ra.debugPrint( c );
  Debug( c ) << "Predicates: " << std::endl;
  for( std::map< Node, PredModel >::iterator it = d_pred_model.begin(); it != d_pred_model.end(); ++it ){
    it->second.debugPrint( c );
    Debug( c ) << std::endl;
  }
  Debug( c ) << "Functions: " << std::endl;
  for( std::map< Node, FunctionModel >::iterator it = d_func_model.begin(); it != d_func_model.end(); ++it ){
    it->second.debugPrint( c );
    Debug( c ) << std::endl;
  }
}
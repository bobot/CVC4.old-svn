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

}

void PredModel::addRequirement( Node f, Node p, bool phase ){
  d_reqs[ phase ? 1 : 0 ][ f ].push_back( p );
}

void PredModel::debugPrint( const char* c ){
  Debug( c ) << "Predicate " << d_op << std::endl;
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
}

FunctionModel::FunctionModel( Node op, QuantifiersEngine* qe ) : d_op( op ), d_qe( qe ){
  //look at ground assertions
}

void FunctionModel::addRequirement( Node f, Node t, Node te, bool phase ){
  d_reqs[ phase ? 1 : 0 ][ f ][ t ].push_back( te );
}

void FunctionModel::debugPrint( const char* c ){
  Debug( c ) << "Function " << d_op << std::endl;
  Debug( c ) << "   Phase reqs:" << std::endl;
  for( int i=0; i<2; i++ ){
    for( std::map< Node, std::map< Node, std::vector< Node > > >::iterator it = d_reqs[i].begin(); it != d_reqs[i].end(); ++it ){
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

#if 0
  //now analyze quantifiers
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    Debug("fmf-model-req") << "Phase requirements for " << f << ": " << std::endl;
    for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
         it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
      Node n = it->first;
      Debug("fmf-model-req") << "   " << n << " -> " << it->second << std::endl;
      if( n.getKind()==APPLY_UF ){
        processPredicate( f, n, it->second );
      }else if( n.getKind()==EQUAL ){
        processEquality( f, n, it->second );
      }
    }
  }
  Debug("fmf-model") << "Done." << std::endl;
  debugPrint("fmf-model-complete");
#endif
  //try to complete model? TODO
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
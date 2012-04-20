/*********************                                                        */
/*! \file fmf_model.cpp
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
 ** \brief Implementation of fmf model
 **/

#include "theory/uf/inst_strategy_model_find.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_instantiator.h"

#include "theory/theory_engine.h"
#include "theory/uf/equality_engine_impl.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

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

FmfModel::FmfModel( QuantifiersEngine* qe, StrongSolverTheoryUf* ss ) : d_quantEngine( qe ), d_ss( ss ){

}

void FmfModel::buildModel(){
  buildRepresentatives();
  //now analyze quantifiers
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    Debug("fmf-model-req") << "Phase requirements for " << f << ": " << std::endl;
    for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin(); 
         it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
      Node n = it->first;
      Debug("fmf-model-req") << "   " << n << " -> " << it->second << std::endl;
    }
    for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs_equality[f].begin(); 
          it != d_quantEngine->d_phase_reqs_equality[f].end(); ++it ){
      Node n = it->first;
      Node t = d_quantEngine->d_phase_reqs_equality_term[f][n];
      Debug("fmf-model-req") << "   " << n << ( it->second ? " == " : " != " ) << t << std::endl;
      if( n.getKind()==INST_CONSTANT ){
        t = d_quantEngine->getEqualityQuery()->getRepresentative( t );
        if( it->second ){
        
        }else{
          int tValue = d_ra.getIndexFor( t );
          if( tValue!=-1 ){
            int index = (int)n.getAttribute(InstVarNumAttribute());
            Debug("fmf-model") << "*** Restrict ( " << index << " -> " << tValue << " )" << std::endl;
          }
        }
      }else if( Trigger::isSimpleTrigger( n ) ){
        t = d_quantEngine->getEqualityQuery()->getRepresentative( t );
        Node op = n.getOperator();
      }
    }
  }
  Debug("fmf-model") << "Done." << std::endl;
}

void FmfModel::buildRepresentatives(){
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

int FmfModel::acceptCurrent( RepAlphabetIterator* rai ){
  return -1;
}

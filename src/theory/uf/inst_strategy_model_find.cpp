/*********************                                                        */
/*! \file inst_strategy_model_find.cpp
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
 ** \brief Implementation of inst strategy model find
 **/

#include "theory/uf/inst_strategy_model_find.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine_impl.h"
#include "theory/uf/theory_uf_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;


RepAlphabet::RepAlphabet( RepAlphabet& ra, QuantifiersEngine* ie ){
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

bool RepAlphabet::didInstantiation( RepAlphabetIterator& riter ){
#if 1
  for( int i=0; i<(int)riter.getNumTerms(); i++ ){
    Node n = riter.getTerm( i );
    TypeNode tn = n.getType();
    if( std::find( d_type_reps[tn].begin(), d_type_reps[tn].end(), n )==d_type_reps[tn].end() ){
      return false;
    }
  }
  //std::cout << "Already did instantiation " << std::endl;
  //for( int i=0; i<(int)riter.getNumTerms(); i++ ){
  //  std::cout << "   " <<  riter.getTerm( i ) << std::endl;
  //}
  return true;
#else
  return false;
#endif
}

void RepAlphabetIterator::increment(){
  Assert( !isFinished() );
  int counter = 0;
  while( d_index[counter]==(int)(d_ra->d_type_reps[d_f[0][counter].getType()].size()-1) ){
    d_index[counter] = 0;
    counter++;
    if( counter==(int)d_index.size() ){
      d_index.clear();
      return;
    }
  }
  d_index[counter]++;
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
  Assert( d_ra->d_type_reps.find( tn )!=d_ra->d_type_reps.end() );
  return d_ra->d_type_reps[tn][d_index[i]];
}

InstStrategyFinteModelFind::InstStrategyFinteModelFind( context::Context* c, InstantiatorTheoryUf* ith, StrongSolverTheoryUf* ss, QuantifiersEngine* ie ) :
    InstStrategy( ie ), d_ith( ith ), d_ss( ss ){

}

bool InstStrategyFinteModelFind::didInstantiation( Node f, RepAlphabetIterator& riter  ){
  for( int i=0; i<(int)d_inst_group_temp.size(); i++ ){
    if( std::find( d_inst_nodes[i].begin(), d_inst_nodes[i].end(), f )!=d_inst_nodes[i].end() &&
        d_inst_group_temp[i].didInstantiation( riter ) ){
      return true;
    }
  }
  return false;
}

void InstStrategyFinteModelFind::processResetInstantiationRound( Theory::Effort effort ){
  if( effort==Theory::EFFORT_LAST_CALL ){
    //translate all previous rep alphabets
    d_inst_group_temp.clear();
    for( int i=0; i<(int)d_inst_group.size(); i++ ){
      d_inst_group_temp.push_back( RepAlphabet( d_inst_group[i], d_quantEngine ) );
    }

    Debug("inst-fmf") << "Setting up model find, initialize representatives." << std::endl;
    RepAlphabet ra;
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
        Debug("inst-fmf") << "Representatives (" << reps.size() << ") for type " << tn << " (c=" << d_ss->getCardinality( tn ) << "): ";
        for( int i=0; i<(int)reps.size(); i++ ){
          Debug("inst-fmf") << reps[i] << " ";
        }
        Debug("inst-fmf") << std::endl;
        for( int i=0; i<(int)reps.size(); i++ ){
          Debug("inst-fmf-eqc") << "   ";
          d_ith->outputEqClass( "inst-fmf-eqc", reps[i] );
          Debug("inst-fmf-eqc") << std::endl;
        }
        //set them in the alphabet
        ra.set( tn, reps );
      }
    }
    d_inst_group.push_back( ra );
    d_inst_nodes.push_back( std::vector< Node >() );
  }
}

int InstStrategyFinteModelFind::process( Node f, Theory::Effort effort, int e, int limitInst ){
  if( effort==Theory::EFFORT_LAST_CALL ){
    Debug("inst-fmf-debug") << "Add matches for " << f << "..." << std::endl;
    RepAlphabetIterator riter( f, &d_inst_group.back() );
    d_inst_nodes.back().push_back( f );
    bool addedLemma = false;
    while( !riter.isFinished() ){
      while( !riter.isFinished() && didInstantiation( f, riter ) ){
        riter.increment();
      }
      //if successful, add instantiation
      if( !riter.isFinished() ){
        InstMatch m;
        riter.getMatch( d_quantEngine, m );
        riter.increment();
        Debug("inst-fmf-debug") << "Try to add match " << std::endl;
        m.debugPrint("inst-fmf-debug");
        if( d_quantEngine->addInstantiation( f, m ) ){
          addedLemma = true;
        }
      }
    }
    Debug("inst-fmf-debug") << "finished." << std::endl;
    if( !addedLemma ){
      return STATUS_SAT;
    }
  }
  return STATUS_UNKNOWN;
}

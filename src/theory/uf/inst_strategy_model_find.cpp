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
#include "theory/uf/theory_uf_instantiator.h"

#include "theory/theory_engine.h"
#include "theory/uf/equality_engine_impl.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

RepAlphabetIterator::RepAlphabetIterator( QuantifiersEngine* qe, Node f, FmfModel* model ) : d_f( f ), d_model( model ){
  d_index.resize( f[0].getNumChildren(), 0 );
}

void RepAlphabetIterator::increment( QuantifiersEngine* qe ){
  Assert( !isFinished() );
  int counter = 0;
  do{
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
    //check if this is an acceptable instantiation to try
    counter = d_model->acceptCurrent( this );
    //if not, try next value for d_index[counter]
    if( counter!=-1 ){
      for( int i=0; i<counter; i++ ){
        d_index[i] = 0;
      }
    }
  }while( counter!=-1 );
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

InstStrategyFiniteModelFind::InstStrategyFiniteModelFind( context::Context* c, InstantiatorTheoryUf* ith, StrongSolverTheoryUf* ss, QuantifiersEngine* qe ) : InstStrategy( qe ), d_ith( ith ), d_ss( ss ){
  d_fmf_model = new FmfModel( qe, ss );
}

void InstStrategyFiniteModelFind::processResetInstantiationRound( Theory::Effort effort ){
  if( effort==Theory::EFFORT_LAST_CALL ){
    //build the model
    d_fmf_model->buildModel();
  }
}

int InstStrategyFiniteModelFind::process( Node f, Theory::Effort effort, int e, int limitInst ){
  if( effort==Theory::EFFORT_LAST_CALL ){
    Debug("inst-fmf-debug") << "Add matches for " << f << "..." << std::endl;
    RepAlphabetIterator riter( d_quantEngine, f, d_fmf_model );
    int addedLemmas = 0;
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
    if( addedLemmas==0 ){
      return STATUS_SAT;
    }
  }
  return STATUS_UNKNOWN;
}

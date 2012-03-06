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


void InstStrategyFinteModelFind::RepAlphabet::set( TypeNode t, std::vector< Node >& reps ){
  d_type_reps[t].insert( d_type_reps[t].begin(), reps.begin(), reps.end() );
  for( int i=0; i<(int)reps.size(); i++ ){
    d_indicies[ reps[i] ] = i;
  }
}

bool InstStrategyFinteModelFind::PartialInstSet::didCurrentInstantiation( PartialInstSet* pi ){
  bool retVal = true;
  for( int i=0; i<(int)pi->d_index.size(); i++ ){
    Node n = pi->getTerm( i );
    //must translate into alphabet
    if( d_ra->d_indicies.find( n )!=d_ra->d_indicies.end() ){
      if( !isFinished() ){   //if only did partial
        if( d_ra->d_indicies[n]<d_index[i] ){   //lexigraphic order
          retVal = true;
        }else if( d_ra->d_indicies[n]>d_index[i] ){
          retVal = false;
        }
      }
    }else{
      return false;
    }
  }
  return retVal;
}

void InstStrategyFinteModelFind::PartialInstSet::increment(){
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

bool InstStrategyFinteModelFind::PartialInstSet::isFinished(){
  return d_index.empty();
}

void InstStrategyFinteModelFind::PartialInstSet::getMatch( QuantifiersEngine* ie, InstMatch& m ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    m.d_map[ ie->getInstantiationConstant( d_f, i ) ] = getTerm( i );
  }
}

Node InstStrategyFinteModelFind::PartialInstSet::getTerm( int i ){
  return d_ra->d_type_reps[d_f[0][i].getType()][d_index[i]];
}

InstStrategyFinteModelFind::InstStrategyFinteModelFind( context::Context* c, InstantiatorTheoryUf* ith, StrongSolverTheoryUf* ss, QuantifiersEngine* ie ) : 
    InstStrategy( ie ), d_ith( ith ), d_ss( ss ), d_curr_ra( NULL ), d_finding_model( c, false ){

}

bool InstStrategyFinteModelFind::didCurrentInstantiation( PartialInstSet* pi ){
  Node f = pi->d_f;
  for( int i=0; i<(int)d_inst_group[f].size(); i++ ){
    if( d_inst_group[f][i]->didCurrentInstantiation( pi ) ){
      return true;
    }
  }
  return false;
}

void InstStrategyFinteModelFind::processResetInstantiationRound( Theory::Effort effort ){
  if( effort=Theory::LAST_CALL ){
    if( !d_finding_model.get() ){
      Debug("inst-fmf") << "Setting up model find, initialize representatives." << std::endl;
      d_curr_ra = new RepAlphabet;
      //collect all representatives for all types and store as representative alphabet
      for( int i=0; i<d_ss->getNumCardinalityTypes(); i++ ){
        TypeNode tn = d_ss->getCardinalityType( i );
        std::vector< Node > reps;
        d_ss->getRepresentatives( tn, reps );

        //DO_THIS: prefer previously used reps

        Debug("inst-fmf") << "Representatives (" << reps.size() << ") for type " << tn << ": ";
        for( int i=0; i<(int)reps.size(); i++ ){
          Debug("inst-fmf") << reps[i] << " ";
        }
        Debug("inst-fmf") << std::endl;

        d_curr_ra->d_type_reps[tn].insert( d_curr_ra->d_type_reps[tn].begin(), reps.begin(), reps.end() );
      }
      //make the partial instantiation objects
      for( int i=0; i<(int)d_quantEngine->getNumQuantifiers(); i++ ){
        Node f = d_quantEngine->getQuantifier( i );
        d_inst_group[f].push_back( new PartialInstSet( d_curr_ra, f ) );
      }
      //set that we are trying to see if the model is consistent with quantifiers
      d_finding_model.set( true );
    }
  }
}

int InstStrategyFinteModelFind::process( Node f, Theory::Effort effort, int e, int limitInst ){
  if( effort=Theory::LAST_CALL ){
    PartialInstSet* pi = d_inst_group[f].back();
    bool addedLemma = false;
    while( !addedLemma && !pi->isFinished() ){
      Debug("inst-fmf-debug") << "Try to add match for " << f << "..." << std::endl;
      //do next instantiation
      while( !pi->isFinished() && didCurrentInstantiation( pi ) ){
        Debug("inst-fmf-debug") << "Already did instantiation." << std::endl;
        pi->increment();
      }
      //if successful, add instantiation 
      if( !pi->isFinished() ){
        InstMatch m;
        pi->getMatch( d_quantEngine, m );
        pi->increment();
        Debug("inst-fmf-debug") << "Try to add match " << std::endl;
        m.debugPrint("inst-fmf-debug");
        if( d_quantEngine->addInstantiation( f, &m ) ){
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

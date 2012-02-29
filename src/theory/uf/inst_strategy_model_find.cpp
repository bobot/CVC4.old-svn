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

InstStrategyFinteModelFind::InstStrategyFinteModelFind( context::Context* c, InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
    InstStrategy( ie ), d_th( th ), d_curr_ra( NULL ), d_finding_model( c, false ){

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

void InstStrategyFinteModelFind::resetInstantiationRound(){
  if( !d_finding_model.get() ){
    d_curr_ra = new RepAlphabet;
    d_finding_model.set( true );
  }
}

int InstStrategyFinteModelFind::process( Node f, int effort ){
  if( effort<1 ){
    return STATUS_UNFINISHED;
  }else if( effort==1 ){
    StrongSolverTheoryUf* ss = ((TheoryUF*)d_th)->getStrongSolver();
    if( d_inst_group[f].empty() || d_inst_group[f].back()->d_ra!=d_curr_ra ){
      for( int i=0; i<d_quantEngine->getNumInstantiationConstants( f ); i++ ){
        TypeNode tn = d_quantEngine->getInstantiationConstant( f, i ).getType();
        if( d_curr_ra->d_type_reps.find( tn )==d_curr_ra->d_type_reps.end() ){
          std::vector< Node > reps;
          ss->getRepresentatives( tn, reps );
          //DO_THIS: prefer previously used reps
          d_curr_ra->d_type_reps[tn].insert( d_curr_ra->d_type_reps[tn].begin(), reps.begin(), reps.end() );
        }
      }
      d_inst_group[f].push_back( new PartialInstSet( d_curr_ra, f ) );
    }
    PartialInstSet* pi = d_inst_group[f].back();
    bool addedLemma = false;
    while( !addedLemma && !pi->isFinished() ){
      //do next instantiation
      while( !pi->isFinished() && didCurrentInstantiation( pi ) ){
        pi->increment();
      }
      //if successful, add instantiation 
      if( !pi->isFinished() ){
        InstMatch m;
        pi->getMatch( d_quantEngine, m );
        pi->increment();
        if( d_quantEngine->addInstantiation( f, &m ) ){
          addedLemma = true;
        }
      }
    }
    if( !addedLemma ){
      return STATUS_SAT;
    }
  }
  return STATUS_UNKNOWN;
}

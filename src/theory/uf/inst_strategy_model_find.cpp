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

#include "theory/theory_engine.h"
#include "theory/uf/equality_engine_impl.h"

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
  for( int i=0; i<(int)riter.getNumTerms(); i++ ){
    Node n = riter.getTerm( i );
    TypeNode tn = n.getType();
    if( std::find( d_type_reps[tn].begin(), d_type_reps[tn].end(), n )==d_type_reps[tn].end() ){
      return false;
    }
  }
  return true;
}

void RepAlphabet::debugPrint( const char* c ){
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    Debug( c ) << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      Debug( c ) << "   " << i << ": " << it->second[i] << std::endl;
    }
  }
}

void RAIFilter::RestrictionTrie::addRestriction2( std::vector< RAIFilter::RestrictionTrie::InstValue >& restriction, int index ){
  if( index==(int)restriction.size() ){
    d_active = true;
  }else{
    int ic_index = restriction[index].first;
    int ic_value = restriction[index].second;
    d_data[ ic_index ][ ic_value ].addRestriction2( restriction, index+1 );
  }
}

int RAIFilter::RestrictionTrie::accept2( std::vector< int >& index, int checkIndex ){
  if( d_active || checkIndex==-1 ){
    //either we have found that index is disallowed, or have failed
    return checkIndex;
  }else{
    //see if the current value in index[checkIndex] is restricted according to this trie
    int index1 = -1;
    if( d_data.find( checkIndex )!=d_data.end() ){
      std::map< int, RestrictionTrie >::iterator it = d_data[checkIndex].find( index[checkIndex] );
      if( it!=d_data[checkIndex].end() ){
        //found that there are restrictions for index[checkIndex], now see if we can determine a maximal 
        // index value that is disallowed.
        index1 = it->second.accept2( index, checkIndex - 1 );
        //if the next one, we know this is the best
        if( index1==checkIndex-1 ){
          return index1;
        }
      }
    }
    //otherwise, see if there are restrictions for the next index
    int index2 = accept2( index, checkIndex - 1 );
    return index2>index1 ? index2 : index1;
  }
}

void RAIFilter::initialize( QuantifiersEngine* qe, Node f, RepAlphabet* ra ){
  ra->debugPrint("raif");
  Debug("raif") << "Phase requirements for " << f << " : " << std::endl;
  for( std::map< Node, bool >::iterator it = qe->d_phase_reqs[f].begin(); it != qe->d_phase_reqs[f].end(); ++it ){
    Node n = it->first;
    if( Trigger::isSimpleTrigger( n ) ){
      Debug("raif") << "   " << n << " -> " << it->second << std::endl;
      Node op = n.getOperator();
      Node pol = NodeManager::currentNM()->mkConst<bool>( !(it->second) );
      std::map< int, int > restriction;
      collectPredicateRestrictions( qe, n, pol, ra, &(qe->getTermDatabase()->d_op_map_trie[op]), 0, restriction );
    }
  }
  for( std::map< Node, bool >::iterator it = qe->d_phase_reqs_equality[f].begin(); 
        it != qe->d_phase_reqs_equality[f].end(); ++it ){
    Node n = it->first;
    Node t = qe->d_phase_reqs_equality_term[f][n];
    Debug("raif") << "   " << n << ( it->second ? " == " : " != " ) << t << std::endl;
    if( n.getKind()==INST_CONSTANT ){
      t = qe->getEqualityQuery()->getRepresentative( t );
      if( it->second ){
      
      }else{
        int tValue = ra->getIndexFor( t );
        if( tValue!=-1 ){
          int index = (int)n.getAttribute(InstVarNumAttribute());
          Debug("raif") << "*** Restrict ( " << index << " -> " << tValue << " )" << std::endl;
        }
      }
    }else if( Trigger::isSimpleTrigger( n ) ){
      t = qe->getEqualityQuery()->getRepresentative( t );
      Node op = n.getOperator();

    }
  }
}

void RAIFilter::collectPredicateRestrictions( QuantifiersEngine* qe, Node n, Node pol, RepAlphabet* ra, TermArgTrie* tat, int index,
                                              std::map< int, int >& restriction ){
  if( index==(int)n.getNumChildren() ){
    //now, we must check the polarity of the actual term to see if it corresponds to the correct restriction
    Node t = tat->d_data.begin()->first;
    //Debug("raif-debug") << "Check " << t << " " << pol << " [ ";
    //uf::EqClassIterator eqc = uf::EqClassIterator( qe->getEqualityQuery()->getRepresentative( pol ), 
    //                        ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine() );
    //while( !eqc.isFinished() ){
    //  Debug("raif-debug") << (*eqc) << ", ";
    //  ++eqc;
    //}
    //Debug("raif-debug") << " ] " << std::endl;
    if( qe->getEqualityQuery()->areEqual( t, pol ) ){
      Debug("raif") << "*** " << t << " = " << pol << ", therefore: " << std::endl;
      Debug("raif") << "*** Restrict (";
      for( std::map< int, int >::iterator it = restriction.begin(); it != restriction.end(); ++it ){
        if( it->second!=-1 ){
          Debug("raif") << it->first << " -> " << it->second << ", ";
        }
      }
      Debug("raif") << " )" << std::endl;
    }
  }else{
    if( n[index].getKind()==INST_CONSTANT ){
      for( std::map< Node, TermArgTrie >::iterator it = tat->d_data.begin(); it != tat->d_data.end(); ++it ){
        int tValue = ra->getIndexFor( it->first );
        if( tValue!=-1 ){
          int tIndex = (int)n[index].getAttribute(InstVarNumAttribute());
          if( restriction.find( tIndex )==restriction.end() || 
              restriction[ tIndex ]==-1 || restriction[ tIndex ]==tValue ){
            restriction[ tIndex ] = tValue;
            collectPredicateRestrictions( qe, n, pol, ra, &(it->second), index+1, restriction );
            restriction[ tIndex ] = -1;
          }
        }
      }
    }else{
      Node r = qe->getEqualityQuery()->getRepresentative( n[index] );
      std::map< Node, TermArgTrie >::iterator it = tat->d_data.find( r );
      if( it!=tat->d_data.end() ){
        collectPredicateRestrictions( qe, n, pol, ra, &(it->second), index+1, restriction );
      }
    }
  }
}

int RAIFilter::acceptCurrent( RepAlphabetIterator* rai ){
  //return d_rt.accept( rai->d_index );
  return -1;
}

RepAlphabetIterator::RepAlphabetIterator( QuantifiersEngine* qe, Node f, RepAlphabet* ra ) : d_f( f ), d_ra( ra ){
  d_index.resize( f[0].getNumChildren(), 0 );
  //d_raif.initialize( qe, f, ra );
}

void RepAlphabetIterator::increment( QuantifiersEngine* qe ){
  Assert( !isFinished() );
  int counter = 0;
  do{
    //increment d_index
    while( d_index[counter]==(int)(d_ra->d_type_reps[d_f[0][counter].getType()].size()-1) ){
      d_index[counter] = 0;
      counter++;
      if( counter==(int)d_index.size() ){
        d_index.clear();
        return;
      }
    }
    d_index[counter]++;
    //check if this is an acceptable instantiation to try
    counter = d_raif.acceptCurrent( this );
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
    RepAlphabetIterator riter( d_quantEngine, f, &d_inst_group.back() );
    d_inst_nodes.back().push_back( f );
    bool addedLemma = false;
    while( !riter.isFinished() ){
      //while( !riter.isFinished() && didInstantiation( f, riter ) ){
      //  riter.increment();
      //}
      //if successful, add instantiation
      if( !riter.isFinished() ){
        InstMatch m;
        riter.getMatch( d_quantEngine, m );
        riter.increment( d_quantEngine );
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

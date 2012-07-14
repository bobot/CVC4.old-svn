/*********************                                                        */
/*! \file inst_strategy.cpp
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
 ** \brief Implementation of theory uf instantiation strategies
 **/

#include "theory/uf/inst_strategy.h"

#include "theory/uf/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

#define USE_SINGLE_TRIGGER_BEFORE_MULTI_TRIGGER
//#define MULTI_TRIGGER_FULL_EFFORT_HALF
#define MULTI_MULTI_TRIGGERS

struct sortQuantifiersForSymbol {
  QuantifiersEngine* d_qe;
  bool operator() (Node i, Node j) {
    int nqfsi = d_qe->getNumQuantifiersForSymbol( i.getOperator() );
    int nqfsj = d_qe->getNumQuantifiersForSymbol( j.getOperator() );
    if( nqfsi<nqfsj ){
      return true;
    }else if( nqfsi>nqfsj ){
      return false;
    }else{
      return false;
    }
  }
};


void InstStrategyCheckCESolved::processResetInstantiationRound( Theory::Effort effort ){
  for( std::map< Node, bool >::iterator it = d_solved.begin(); it != d_solved.end(); ++it ){
    calcSolved( it->first );
  }
}

int InstStrategyCheckCESolved::process( Node f, Theory::Effort effort, int e ){
  if( e==0 ){
    //calc solved if not done so already
    if( d_solved.find( f )==d_solved.end() ){
      calcSolved( f );
    }
    //check if f is counterexample-solved
    Debug("quant-uf-strategy") << "Try CE-solved.." << std::endl;
    if( d_solved[ f ] ){
      if( d_quantEngine->addInstantiation( f, d_th->d_baseMatch[f] ) ){
        ++(d_th->d_statistics.d_instantiations_ce_solved);
        //d_quantEngine->d_hasInstantiated[f] = true;
      }
      d_solved[f] = false;
    }
    Debug("quant-uf-strategy") << "done." << std::endl;
  }
  return STATUS_UNKNOWN;
}

void InstStrategyCheckCESolved::calcSolved( Node f ){
  d_th->d_baseMatch[f].clear();
  d_solved[ f ]= true;
  //check if instantiation constants are solved for
  for( int j = 0; j<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); j++ ){
    Node i = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, j );
    Node rep = d_th->getInternalRepresentative( i );
    if( !rep.hasAttribute(InstConstantAttribute()) ){
      d_th->d_baseMatch[f].d_map[ i ] = rep;
    }else{
      d_solved[ f ] = false;
    }
  }
}

void InstStrategyUserPatterns::processResetInstantiationRound( Theory::Effort effort ){
  //reset triggers
  for( std::map< Node, std::vector< Trigger* > >::iterator it = d_user_gen.begin(); it != d_user_gen.end(); ++it ){
    for( int i=0; i<(int)it->second.size(); i++ ){
      it->second[i]->resetInstantiationRound();
      it->second[i]->reset( Node::null() );
    }
  }
}

int InstStrategyUserPatterns::process( Node f, Theory::Effort effort, int e ){
  if( e==0 ){
    return STATUS_UNFINISHED;
  }else if( e==1 ){
    d_counter[f]++;
    Debug("quant-uf-strategy") << "Try user-provided patterns..." << std::endl;
    //Notice() << "Try user-provided patterns..." << std::endl;
    for( int i=0; i<(int)d_user_gen[f].size(); i++ ){
      bool processTrigger = true;
      if( effort!=Theory::EFFORT_LAST_CALL && d_user_gen[f][i]->isMultiTrigger() ){
//#ifdef MULTI_TRIGGER_FULL_EFFORT_HALF
//        processTrigger = d_counter[f]%2==0;
//#endif
      }
      if( processTrigger ){
        //if( d_user_gen[f][i]->isMultiTrigger() )
          //Notice() << "  Process (user) " << (*d_user_gen[f][i]) << " for " << f << "..." << std::endl;
        int numInst = d_user_gen[f][i]->addInstantiations( d_th->d_baseMatch[f] );
        //if( d_user_gen[f][i]->isMultiTrigger() )
          //Notice() << "  Done, numInst = " << numInst << "." << std::endl;
        d_th->d_statistics.d_instantiations_user_pattern += numInst;
        if( d_user_gen[f][i]->isMultiTrigger() ){
          d_quantEngine->d_statistics.d_multi_trigger_instantiations += numInst;
        }
        //d_quantEngine->d_hasInstantiated[f] = true;
      }
    }
    Debug("quant-uf-strategy") << "done." << std::endl;
    //Notice() << "done" << std::endl;
  }
  return STATUS_UNKNOWN;
}

void InstStrategyUserPatterns::addUserPattern( Node f, Node pat ){
  //add to generators
  std::vector< Node > nodes;
  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    nodes.push_back( pat[i] );
  }
  if( Trigger::isUsableTrigger( nodes, f ) ){
    //extend to literal matching
    d_quantEngine->getPhaseReqTerms( f, nodes );
    //check match option
    int matchOption = options::efficientEMatching() ? InstMatchGenerator::MATCH_GEN_EFFICIENT_E_MATCH : 0;
    d_user_gen[f].push_back( Trigger::mkTrigger( d_quantEngine, f, nodes, matchOption, true, Trigger::TR_MAKE_NEW,
                                                 options::smartTriggers() ) );
  }
}

void InstStrategyAutoGenTriggers::processResetInstantiationRound( Theory::Effort effort ){
  //reset triggers
  for( std::map< Node, std::map< Trigger*, bool > >::iterator it = d_auto_gen_trigger.begin(); it != d_auto_gen_trigger.end(); ++it ){
    for( std::map< Trigger*, bool >::iterator itt = it->second.begin(); itt != it->second.end(); ++itt ){
      itt->first->resetInstantiationRound();
      itt->first->reset( Node::null() );
    }
  }
}

int InstStrategyAutoGenTriggers::process( Node f, Theory::Effort effort, int e ){
  int peffort = f.getNumChildren()==3 ? 2 : 1;
  //int peffort = f.getNumChildren()==3 ? 2 : 1;
  //int peffort = 1;
  if( e<peffort ){
    return STATUS_UNFINISHED;
  }else{
    bool gen = false;
    if( e==peffort ){
      if( d_counter.find( f )==d_counter.end() ){
        d_counter[f] = 0;
        gen = true;
      }else{
        d_counter[f]++;
        gen = d_regenerate && d_counter[f]%d_regenerate_frequency==0;
      }
    }else{
      gen = true;
    }
    if( gen ){
      generateTriggers( f );
    }
    Debug("quant-uf-strategy")  << "Try auto-generated triggers... " << d_tr_strategy << " " << e << std::endl;
    //Notice() << "Try auto-generated triggers..." << std::endl;
    for( std::map< Trigger*, bool >::iterator itt = d_auto_gen_trigger[f].begin(); itt != d_auto_gen_trigger[f].end(); ++itt ){
      Trigger* tr = itt->first;
      if( tr ){
        bool processTrigger = itt->second;
        if( effort!=Theory::EFFORT_LAST_CALL && tr->isMultiTrigger() ){
#ifdef MULTI_TRIGGER_FULL_EFFORT_HALF
          processTrigger = d_counter[f]%2==0;
#endif
        }
        if( processTrigger ){
          //if( tr->isMultiTrigger() )
            Debug("quant-uf-strategy-auto-gen-triggers") << "  Process " << (*tr) << "..." << std::endl;
          int numInst = tr->addInstantiations( d_th->d_baseMatch[f] );
          //if( tr->isMultiTrigger() )
            Debug("quant-uf-strategy-auto-gen-triggers") << "  Done, numInst = " << numInst << "." << std::endl;
          if( d_tr_strategy==Trigger::TS_MIN_TRIGGER ){
            d_th->d_statistics.d_instantiations_auto_gen_min += numInst;
          }else{
            d_th->d_statistics.d_instantiations_auto_gen += numInst;
          }
          if( tr->isMultiTrigger() ){
            d_quantEngine->d_statistics.d_multi_trigger_instantiations += numInst;
          }
          //d_quantEngine->d_hasInstantiated[f] = true;
        }
      }
    }
    Debug("quant-uf-strategy") << "done." << std::endl;
    //Notice() << "done" << std::endl;
  }
  return STATUS_UNKNOWN;
}

void InstStrategyAutoGenTriggers::generateTriggers( Node f ){
  Debug("auto-gen-trigger") << "Generate trigger for " << f << std::endl;
  if( d_patTerms[0].find( f )==d_patTerms[0].end() ){
    //determine all possible pattern terms based on trigger term selection strategy d_tr_strategy
    d_patTerms[0][f].clear();
    d_patTerms[1][f].clear();
    std::vector< Node > patTermsF;
    Trigger::collectPatTerms( d_quantEngine, f, d_quantEngine->getTermDatabase()->getCounterexampleBody( f ), patTermsF, d_tr_strategy, true );
    Debug("auto-gen-trigger") << "Collected pat terms for " << d_quantEngine->getTermDatabase()->getCounterexampleBody( f ) << std::endl;
    Debug("auto-gen-trigger") << "   ";
    for( int i=0; i<(int)patTermsF.size(); i++ ){
      Debug("auto-gen-trigger") << patTermsF[i] << " ";
    }
    Debug("auto-gen-trigger") << std::endl;
    //extend to literal matching
    d_quantEngine->getPhaseReqTerms( f, patTermsF );
    //sort into single/multi triggers
    std::map< Node, std::vector< Node > > varContains;
    Trigger::getVarContains( f, patTermsF, varContains );
    for( std::map< Node, std::vector< Node > >::iterator it = varContains.begin(); it != varContains.end(); ++it ){
      if( it->second.size()==f[0].getNumChildren() ){
        d_patTerms[0][f].push_back( it->first );
        d_is_single_trigger[ it->first ] = true;
      }else{
        d_patTerms[1][f].push_back( it->first );
        d_is_single_trigger[ it->first ] = false;
      }
    }
    d_made_multi_trigger[f] = false;
    Debug("auto-gen-trigger") << "Single triggers for " << f << " : " << std::endl;
    Debug("auto-gen-trigger") << "   ";
    for( int i=0; i<(int)d_patTerms[0][f].size(); i++ ){
      Debug("auto-gen-trigger") << d_patTerms[0][f][i] << " ";
    }
    Debug("auto-gen-trigger") << std::endl;
    Debug("auto-gen-trigger") << "Multi-trigger term pool for " << f << " : " << std::endl;
    Debug("auto-gen-trigger") << "   ";
    for( int i=0; i<(int)d_patTerms[1][f].size(); i++ ){
      Debug("auto-gen-trigger") << d_patTerms[1][f][i] << " ";
    }
    Debug("auto-gen-trigger") << std::endl;
  }

  //populate candidate pattern term vector for the current trigger
  std::vector< Node > patTerms;
#ifdef USE_SINGLE_TRIGGER_BEFORE_MULTI_TRIGGER
  //try to add single triggers first
  for( int i=0; i<(int)d_patTerms[0][f].size(); i++ ){
    if( !d_single_trigger_gen[d_patTerms[0][f][i]] ){
      patTerms.push_back( d_patTerms[0][f][i] );
    }
  }
  //if no single triggers exist, add multi trigger terms
  if( patTerms.empty() ){
    patTerms.insert( patTerms.begin(), d_patTerms[1][f].begin(), d_patTerms[1][f].end() );
  }
#else
  patTerms.insert( patTerms.begin(), d_patTerms[0][f].begin(), d_patTerms[0][f].end() );
  patTerms.insert( patTerms.begin(), d_patTerms[1][f].begin(), d_patTerms[1][f].end() );
#endif

  if( !patTerms.empty() ){
    Debug("auto-gen-trigger") << "Generate trigger for " << f << std::endl;
    //sort terms based on relevance
    if( d_rlv_strategy==RELEVANCE_DEFAULT ){
      sortQuantifiersForSymbol sqfs;
      sqfs.d_qe = d_quantEngine;
      //sort based on # occurrences (this will cause Trigger to select rarer symbols)
      std::sort( patTerms.begin(), patTerms.end(), sqfs );
      Debug("relevant-trigger") << "Terms based on relevance: " << std::endl;
      for( int i=0; i<(int)patTerms.size(); i++ ){
        Debug("relevant-trigger") << "   " << patTerms[i] << " (";
        Debug("relevant-trigger") << d_quantEngine->getNumQuantifiersForSymbol( patTerms[i].getOperator() ) << ")" << std::endl;
      }
      //Notice() << "Terms based on relevance: " << std::endl;
      //for( int i=0; i<(int)patTerms.size(); i++ ){
      //  Notice() << "   " << patTerms[i] << " (";
      //  Notice() << d_quantEngine->getNumQuantifiersForSymbol( patTerms[i].getOperator() ) << ")" << std::endl;
      //}
    }
    //now, generate the trigger...
    int matchOption = options::efficientEMatching() ? InstMatchGenerator::MATCH_GEN_EFFICIENT_E_MATCH : 0;
    Trigger* tr = NULL;
    if( d_is_single_trigger[ patTerms[0] ] ){
      tr = Trigger::mkTrigger( d_quantEngine, f, patTerms[0], matchOption, false, Trigger::TR_RETURN_NULL,
                               options::smartTriggers() );
      d_single_trigger_gen[ patTerms[0] ] = true;
    }else{
      //if we are re-generating triggers, shuffle based on some method
      if( d_made_multi_trigger[f] ){
#ifndef MULTI_MULTI_TRIGGERS
        return;
#endif
        std::random_shuffle( patTerms.begin(), patTerms.end() ); //shuffle randomly
      }else{
        d_made_multi_trigger[f] = true;
      }
      //will possibly want to get an old trigger
      tr = Trigger::mkTrigger( d_quantEngine, f, patTerms, matchOption, false, Trigger::TR_GET_OLD,
                               options::smartTriggers() );
    }
    if( tr ){
      if( tr->isMultiTrigger() ){
        //disable all other multi triggers
        for( std::map< Trigger*, bool >::iterator it = d_auto_gen_trigger[f].begin(); it != d_auto_gen_trigger[f].end(); ++it ){
          if( it->first->isMultiTrigger() ){
            d_auto_gen_trigger[f][ it->first ] = false;
          }
        }
      }
      //making it during an instantiation round, so must reset
      if( d_auto_gen_trigger[f].find( tr )==d_auto_gen_trigger[f].end() ){
        tr->resetInstantiationRound();
        tr->reset( Node::null() );
      }
      d_auto_gen_trigger[f][tr] = true;
      //if we are generating additional triggers...
      if( d_generate_additional && d_is_single_trigger[ patTerms[0] ] ){
        int index = 0;
        if( index<(int)patTerms.size() ){
          //Notice() << "check add additional" << std::endl;
          //check if similar patterns exist, and if so, add them additionally
          int nqfs_curr = d_quantEngine->getNumQuantifiersForSymbol( patTerms[0].getOperator() );
          index++;
          bool success = true;
          while( success && index<(int)patTerms.size() && d_is_single_trigger[ patTerms[index] ] ){
            success = false;
            if( d_quantEngine->getNumQuantifiersForSymbol( patTerms[index].getOperator() )<=nqfs_curr ){
              d_single_trigger_gen[ patTerms[index] ] = true;
              Trigger* tr2 = Trigger::mkTrigger( d_quantEngine, f, patTerms[index], matchOption, false, Trigger::TR_RETURN_NULL,
                                                 options::smartTriggers() );
              if( tr2 ){
                //Notice() << "Add additional trigger " << patTerms[index] << std::endl;
                tr2->resetInstantiationRound();
                tr2->reset( Node::null() );
                d_auto_gen_trigger[f][tr2] = true;
              }
              success = true;
            }
            index++;
          }
          //Notice() << "done check add additional" << std::endl;
        }
      }
    }
  }
}

#if 0

void InstStrategyAddFailSplits::processResetInstantiationRound( Theory::Effort effort ){
}

int InstStrategyAddFailSplits::process( Node f, Theory::Effort effort, int e ){
  if( e<4 ){
    return STATUS_UNFINISHED;
  }else{
    for( std::map< Node, std::map< Node, std::vector< InstMatchGenerator* > > >::iterator it = InstMatchGenerator::d_match_fails.begin();
         it != InstMatchGenerator::d_match_fails.end(); ++it ){
      for( std::map< Node, std::vector< InstMatchGenerator* > >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        if( !it2->second.empty() ){
          Node n1 = it->first;
          Node n2 = it2->first;
          if( !d_quantEngine->getEqualityQuery()->areEqual( n1, n2 ) && !d_quantEngine->getEqualityQuery()->areDisequal( n1, n2 ) ){
            d_quantEngine->addSplitEquality( n1, n2, true );
          }
          it2->second.clear();
        }
      }
    }
    return STATUS_UNKNOWN;
  }
}

#endif /* 0 */

void InstStrategyFreeVariable::processResetInstantiationRound( Theory::Effort effort ){
}

int InstStrategyFreeVariable::process( Node f, Theory::Effort effort, int e ){
  if( e<5 ){
    return STATUS_UNFINISHED;
  }else{
    if( d_guessed.find( f )==d_guessed.end() ){
      d_guessed[f] = true;
      Debug("quant-uf-alg") << "Add guessed instantiation" << std::endl;
      InstMatch m;
      if( d_quantEngine->addInstantiation( f, m ) ){
        ++(d_th->d_statistics.d_instantiations_guess);
        //d_quantEngine->d_hasInstantiated[f] = true;
      }
    }
    return STATUS_UNKNOWN;
  }
}

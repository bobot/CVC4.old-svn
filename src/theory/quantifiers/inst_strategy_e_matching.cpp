/*********************                                                        */
/*! \file inst_strategy_e_matching.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): bobot
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of e matching instantiation strategies
 **/

#include "theory/quantifiers/inst_strategy_e_matching.h"

#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/inst_match_generator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;
using namespace CVC4::theory::quantifiers;

#define USE_SINGLE_TRIGGER_BEFORE_MULTI_TRIGGER
//#define MULTI_TRIGGER_FULL_EFFORT_HALF
#define MULTI_MULTI_TRIGGERS

struct sortQuantifiersForSymbol {
  QuantifiersEngine* d_qe;
  bool operator() (Node i, Node j) {
    int nqfsi = d_qe->getQuantifierRelevance()->getNumQuantifiersForSymbol( i.getOperator() );
    int nqfsj = d_qe->getQuantifierRelevance()->getNumQuantifiersForSymbol( j.getOperator() );
    if( nqfsi<nqfsj ){
      return true;
    }else if( nqfsi>nqfsj ){
      return false;
    }else{
      return false;
    }
  }
};

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
        InstMatch baseMatch;
        int numInst = d_user_gen[f][i]->addInstantiations( baseMatch );
        //if( d_user_gen[f][i]->isMultiTrigger() )
          //Notice() << "  Done, numInst = " << numInst << "." << std::endl;
        d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_user_patterns += numInst;
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
/*
InstStrategyUserPatterns::Statistics::Statistics():
  d_instantiations("InstStrategyUserPatterns::Instantiations", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
}

InstStrategyUserPatterns::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
}
*/

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
          InstMatch baseMatch;
          int numInst = tr->addInstantiations( baseMatch );
          //if( tr->isMultiTrigger() )
            Debug("quant-uf-strategy-auto-gen-triggers") << "  Done, numInst = " << numInst << "." << std::endl;
          if( d_tr_strategy==Trigger::TS_MIN_TRIGGER ){
            d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_auto_gen_min += numInst;
          }else{
            d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_auto_gen += numInst;
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
    Trigger::collectPatTerms( d_quantEngine, f, d_quantEngine->getTermDatabase()->getInstConstantBody( f ), patTermsF, d_tr_strategy, true );
    Debug("auto-gen-trigger") << "Collected pat terms for " << d_quantEngine->getTermDatabase()->getInstConstantBody( f ) << std::endl;
    Debug("auto-gen-trigger") << "   ";
    for( int i=0; i<(int)patTermsF.size(); i++ ){
      Debug("auto-gen-trigger") << patTermsF[i] << " ";
    }
    Debug("auto-gen-trigger") << std::endl;
    //extend to literal matching (if applicable)
    d_quantEngine->getPhaseReqTerms( f, patTermsF );
    //sort into single/multi triggers
    std::map< Node, std::vector< Node > > varContains;
    d_quantEngine->getTermDatabase()->getVarContains( f, patTermsF, varContains );
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
        Debug("relevant-trigger") << d_quantEngine->getQuantifierRelevance()->getNumQuantifiersForSymbol( patTerms[i].getOperator() ) << ")" << std::endl;
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
          int nqfs_curr = d_quantEngine->getQuantifierRelevance()->getNumQuantifiersForSymbol( patTerms[0].getOperator() );
          index++;
          bool success = true;
          while( success && index<(int)patTerms.size() && d_is_single_trigger[ patTerms[index] ] ){
            success = false;
            if( d_quantEngine->getQuantifierRelevance()->getNumQuantifiersForSymbol( patTerms[index].getOperator() )<=nqfs_curr ){
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
/*
InstStrategyAutoGenTriggers::Statistics::Statistics():
  d_instantiations("InstStrategyAutoGenTriggers::Instantiations", 0),
  d_instantiations_min("InstStrategyAutoGenTriggers::Instantiations_min", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_instantiations_min);
}

InstStrategyAutoGenTriggers::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_instantiations_min);
}
*/

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
        ++(d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_guess);
        //d_quantEngine->d_hasInstantiated[f] = true;
      }
    }
    return STATUS_UNKNOWN;
  }
}
/*
InstStrategyFreeVariable::Statistics::Statistics():
  d_instantiations("InstStrategyGuess::Instantiations", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
}

InstStrategyFreeVariable::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
}
*/

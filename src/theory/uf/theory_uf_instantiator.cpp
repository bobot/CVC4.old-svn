/*********************                                                        */
/*! \file theory_uf_instantiator.cpp
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
 ** \brief Implementation of theory uf instantiator class
 **/

#include "theory/uf/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine_impl.h"
#include "theory/uf/inst_strategy_model_find.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

#define USE_SINGLE_TRIGGER_BEFORE_MULTI_TRIGGER
//#define MULTI_TRIGGER_ONLY_LAST_CALL
#define MULTI_TRIGGER_FULL_EFFORT_HALF
//#define MULTI_MULTI_TRIGGERS

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

int InstStrategyCheckCESolved::process( Node f, Theory::Effort effort, int e, int instLimit ){
  if( e==0 ){
    //calc solved if not done so already
    if( d_solved.find( f )==d_solved.end() ){
      calcSolved( f );
    }
    //check if f is counterexample-solved
    if( d_solved[ f ] ){
      if( d_quantEngine->addInstantiation( f, d_th->d_baseMatch[f] ) ){
        ++(d_th->d_statistics.d_instantiations_ce_solved);
        //d_quantEngine->d_hasInstantiated[f] = true;
      }
      d_solved[f] = false;
    } 
  }
  return STATUS_UNKNOWN;
}

void InstStrategyCheckCESolved::calcSolved( Node f ){
  d_th->d_baseMatch[f].clear();
  d_solved[ f ]= true;
  //check if instantiation constants are solved for
  for( int j = 0; j<(int)d_quantEngine->getNumInstantiationConstants( f ); j++ ){
    Node i = d_quantEngine->getInstantiationConstant( f, j );
    Node rep = d_th->getInternalRepresentative( i );
    if( !rep.hasAttribute(InstConstantAttribute()) ){
      d_th->d_baseMatch[f].d_map[ i ] = rep;
    }else{
      d_solved[ f ] = false;
    }
  }
}

void InstStrategyUserPatterns::processResetInstantiationRound( Theory::Effort effort ){
  for( std::map< Node, std::vector< Trigger* > >::iterator it = d_user_gen.begin(); it != d_user_gen.end(); ++it ){
    for( int i=0; i<(int)it->second.size(); i++ ){
      it->second[i]->resetInstantiationRound();
      it->second[i]->reset( Node::null() );
    }
  }
}

int InstStrategyUserPatterns::process( Node f, Theory::Effort effort, int e, int instLimit ){
  if( e==0 ){
    return STATUS_UNFINISHED;
  }else if( e==1 ){
    d_counter[f]++;
    Debug("quant-uf-strategy") << "Try user-provided patterns..." << std::endl;
    //std::cout << "Try user-provided patterns..." << std::endl;
    for( int i=0; i<(int)d_user_gen[f].size(); i++ ){
      bool processTrigger = true;
      if( effort!=Theory::EFFORT_LAST_CALL && d_user_gen[f][i]->isMultiTrigger() ){
#ifdef MULTI_TRIGGER_FULL_EFFORT_HALF
        processTrigger = d_counter[f]%2==0;
#endif
#ifdef MULTI_TRIGGER_ONLY_LAST_CALL
        processTrigger = false;
#endif
      }
      if( processTrigger ){
        //if( d_user_gen[f][i]->isMultiTrigger() ) 
          //std::cout << "  Process (user) " << (*d_user_gen[f][i]) << " for " << f << "..." << std::endl;
        int numInst = d_user_gen[f][i]->addInstantiations( d_th->d_baseMatch[f], instLimit );
        //if( d_user_gen[f][i]->isMultiTrigger() ) 
          //std::cout << "  Done, numInst = " << numInst << "." << std::endl;
        d_th->d_statistics.d_instantiations_user_pattern += numInst;
        if( d_user_gen[f][i]->isMultiTrigger() ){
          d_quantEngine->d_statistics.d_multi_trigger_instantiations += numInst;
        }
        //d_quantEngine->d_hasInstantiated[f] = true;
      }
    }
    Debug("quant-uf-strategy") << "done." << std::endl;
    //std::cout << "done" << std::endl;
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
    int matchOption = Options::current()->efficientEMatching ? InstMatchGenerator::MATCH_GEN_EFFICIENT_E_MATCH : 0;
    d_user_gen[f].push_back( Trigger::mkTrigger( d_quantEngine, f, nodes, matchOption, true ) );
  }
}
 
void InstStrategyAutoGenTriggers::processResetInstantiationRound( Theory::Effort effort ){
  for( std::map< Node, std::map< Trigger*, bool > >::iterator it = d_auto_gen_trigger.begin(); it != d_auto_gen_trigger.end(); ++it ){
    for( std::map< Trigger*, bool >::iterator itt = it->second.begin(); itt != it->second.end(); ++itt ){
      itt->first->resetInstantiationRound();
      itt->first->reset( Node::null() );
    }
  }
}

int InstStrategyAutoGenTriggers::process( Node f, Theory::Effort effort, int e, int instLimit ){
  int peffort = f.getNumChildren()==3 ? 2 : 1;
  //int peffort = f.getNumChildren()==3 ? 2 : 1;
  //int peffort = 1;
  if( e<peffort ){
    return STATUS_UNFINISHED;
  }else if( e==peffort ){
    bool gen = false;
    if( d_counter.find( f )==d_counter.end() ){
      d_counter[f] = 0;
      gen = true;
    }else{
      d_counter[f]++;
      gen = d_regenerate && d_counter[f]%d_regenerate_frequency==0;
    }
    if( gen ){
      generateTriggers( f );
    }
    Debug("quant-uf-strategy")  << "Try auto-generated triggers... " << d_tr_strategy << std::endl;
    //std::cout << "Try auto-generated triggers..." << std::endl;
    for( std::map< Trigger*, bool >::iterator itt = d_auto_gen_trigger[f].begin(); itt != d_auto_gen_trigger[f].end(); ++itt ){
      Trigger* tr = itt->first;
      if( tr ){
        bool processTrigger = itt->second;
        if( effort!=Theory::EFFORT_LAST_CALL && tr->isMultiTrigger() ){
#ifdef MULTI_TRIGGER_FULL_EFFORT_HALF
          processTrigger = d_counter[f]%2==0;
#endif
#ifdef MULTI_TRIGGER_ONLY_LAST_CALL
          processTrigger = false;
#endif
        }
        if( processTrigger ){
          //if( tr->isMultiTrigger() ) 
            //std::cout << "  Process " << (*tr) << " for " << f << "..." << std::endl;
          int numInst = tr->addInstantiations( d_th->d_baseMatch[f], instLimit );
          //if( tr->isMultiTrigger() ) 
            //std::cout << "  Done, numInst = " << numInst << "." << std::endl;
          if( d_tr_strategy==Trigger::TS_MIN_TRIGGER ){
            d_th->d_statistics.d_instantiations_auto_gen_min += numInst;
          }else{
            d_th->d_statistics.d_instantiations_auto_gen += numInst;
          }
          if( tr->isMultiTrigger() ){
            d_quantEngine->d_statistics.d_multi_trigger_instantiations += numInst;
          }
          //d_quantEngine->d_hasInstantiated[f] = true;
          Debug("quant-uf-strategy") << "done." << std::endl;
        }
      }
    }
    //std::cout << "done" << std::endl;
  }
  return STATUS_UNKNOWN;
}

void InstStrategyAutoGenTriggers::generateTriggers( Node f ){
  Debug("auto-gen-trigger")  << "Generate trigger for " << f << std::endl;
  if( d_patTerms[0].find( f )==d_patTerms[0].end() ){
    //determine all possible pattern terms based on trigger term selection strategy d_tr_strategy
    d_patTerms[0][f].clear();
    d_patTerms[1][f].clear();
    std::vector< Node > patTermsF;
    Trigger::collectPatTerms( f, d_quantEngine->getCounterexampleBody( f ), patTermsF, d_tr_strategy, true );
    //extend to literal matching
    d_quantEngine->getPhaseReqTerms( f, patTermsF );
    //sort into single/multi triggers
    std::map< Node, std::vector< Node > > varContains;
    Trigger::getVarContains( patTermsF, varContains );
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
    //sort terms based on relevance
    if( d_rlv_strategy==RELEVANCE_DEFAULT ){
      sortQuantifiersForSymbol sqfs;
      sqfs.d_qe = d_quantEngine;
      //sort based on # occurrences (this will cause Trigger to select rarer symbols)
      //std::cout << "do sort" << std::endl;
      std::sort( patTerms.begin(), patTerms.end(), sqfs );
      Debug("relevant-trigger") << "Terms based on relevance: " << std::endl;
      for( int i=0; i<(int)patTerms.size(); i++ ){
        Debug("relevant-trigger") << "   " << patTerms[i] << " (";
        Debug("relevant-trigger") << d_quantEngine->getNumQuantifiersForSymbol( patTerms[i].getOperator() ) << ")" << std::endl;
      }
      //std::cout << "Terms based on relevance: " << std::endl;
      //for( int i=0; i<(int)patTerms.size(); i++ ){
      //  std::cout << "   " << patTerms[i] << " (";
      //  std::cout << d_quantEngine->getNumQuantifiersForSymbol( patTerms[i].getOperator() ) << ")" << std::endl;
      //}
    }
    //now, generate the trigger...
    int matchOption = Options::current()->efficientEMatching ? InstMatchGenerator::MATCH_GEN_EFFICIENT_E_MATCH : 0;
    Trigger* tr = NULL;
    if( d_is_single_trigger[ patTerms[0] ] ){
      tr = Trigger::mkTrigger( d_quantEngine, f, patTerms[0], matchOption, false, Trigger::TR_RETURN_NULL );
      d_single_trigger_gen[ patTerms[0] ] = true;
    }else{
      //if we are re-generating triggers, shuffle based on some method
      if( d_made_multi_trigger[f] ){
#ifndef MULTI_MULTI_TRIGGERS
        return;
#endif
        std::random_shuffle( patTerms.begin(), patTerms.end() ); //shuffle randomly
      }
      //will possibly want to get an old trigger
      tr = Trigger::mkTrigger( d_quantEngine, f, patTerms, matchOption, false, Trigger::TR_GET_OLD );
    }
    if( tr ){
      if( tr->isMultiTrigger() ){
        d_made_multi_trigger[f] = true;
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
          //std::cout << "check add additional" << std::endl;
          //check if similar patterns exist, and if so, add them additionally
          int nqfs_curr = d_quantEngine->getNumQuantifiersForSymbol( patTerms[0].getOperator() );
          index++;
          bool success = true;
          while( success && index<(int)patTerms.size() && d_is_single_trigger[ patTerms[index] ] ){
            success = false;
            if( d_quantEngine->getNumQuantifiersForSymbol( patTerms[index].getOperator() )<=nqfs_curr ){
              d_single_trigger_gen[ patTerms[index] ] = true;
              Trigger* tr2 = Trigger::mkTrigger( d_quantEngine, f, patTerms[index], matchOption, false, Trigger::TR_RETURN_NULL );
              if( tr2 ){
                //std::cout << "Add additional trigger " << patTerms[index] << std::endl;
                tr2->resetInstantiationRound();
                tr2->reset( Node::null() );
                d_auto_gen_trigger[f][tr2] = true;
              }
              success = true;
            }
            index++;
          }
          //std::cout << "done check add additional" << std::endl;
        }
      }
    }
  }
}

void InstStrategyFreeVariable::processResetInstantiationRound( Theory::Effort effort ){
  
}

int InstStrategyFreeVariable::process( Node f, Theory::Effort effort, int e, int instLimit ){
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

void UfTermDb::add( Node n, std::vector< Node >& added, bool withinQuant ){
#if 1
  //don't add terms in quantifier bodies
  if( withinQuant ){
    return;
  }
#endif
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( !n.hasAttribute(InstConstantAttribute()) ){
      if( std::find( d_op_map[op].begin(), d_op_map[op].end(), n )==d_op_map[op].end() ){
        Debug("uf-term-db") << "register term " << n << std::endl;

        d_op_map[op].push_back( n );
        added.push_back( n );
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          add( n[i], added, withinQuant );
          if( Options::current()->efficientEMatching ){
            if( d_parents[n[i]][op].empty() ){
              //must add parent to equivalence class info
              Node nir = d_ith->getRepresentative( n[i] );
              EqClassInfo* eci_nir = d_ith->getEquivalenceClassInfo( nir );
              if( eci_nir ){
                eci_nir->d_pfuns[ op ] = true;
              }
            }
            //add to parent structure
            if( std::find( d_parents[n[i]][op][i].begin(), d_parents[n[i]][op][i].end(), n )==d_parents[n[i]][op][i].end() ){
              d_parents[n[i]][op][i].push_back( n );
            }
          }
        }
        if( Options::current()->efficientEMatching ){
          //check if congruent to preexisting node
          bool congruent = false;
          //for( int i=0; i<(int)d_op_map[op].size(); i++ ){
          //  Node np = d_op_map[op][i];
          //  bool ncong = false;
          //  for( int a=0; a<(int)np.getNumChildren(); a++ ){
          //    if( !d_ith->areEqual( n[a], np[a] ) ){
          //      ncong = true;
          //      break;
          //    }
          //  }
          //  if( !ncong ){
          //    congruent = true;
          //    break;
          //  }
          //}
          if( !congruent ){
            //std::cout << "Add candidate (NEW) " << n << std::endl;
            //new term, add n to candidate generators
            for( int i=0; i<(int)d_ith->d_cand_gens[op].size(); i++ ){
              d_ith->d_cand_gens[op][i]->addCandidate( n );
            }
          }
        }
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        add( n[i], added, withinQuant );
      }
    }
  }
}

EqClassInfo::EqClassInfo( context::Context* c ) : d_funs( c ), d_pfuns( c ), d_disequal( c ){

}

//set member
void EqClassInfo::setMember( Node n, UfTermDb* db ){
  if( n.getKind()==APPLY_UF ){
    d_funs[n.getOperator()] = true;
  }
  //add parent functions
  for( std::map< Node, std::map< int, std::vector< Node > > >::iterator it = db->d_parents[n].begin();
    it != db->d_parents[n].end(); ++it ){
    d_pfuns[ it->first ] = true;
  }
}

//get has function 
bool EqClassInfo::hasFunction( Node op ){
  return d_funs.find( op )!=d_funs.end();
}

bool EqClassInfo::hasParent( Node op ){
  return d_pfuns.find( op )!=d_pfuns.end();
}

//merge with another eq class info
void EqClassInfo::merge( EqClassInfo* eci ){
  for( BoolMap::iterator it = eci->d_funs.begin(); it != eci->d_funs.end(); it++ ) {
    d_funs[ (*it).first ] = true;
  }
  for( BoolMap::iterator it = eci->d_pfuns.begin(); it != eci->d_pfuns.end(); it++ ) {
    d_pfuns[ (*it).first ] = true;
  }
}


InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::QuantifiersEngine* ie, Theory* th) :
Instantiator( c, ie, th )
//d_ob_changed( c ),
//d_obligations( c ),
//d_disequality( c )
{
  d_db = new UfTermDb( this );
  ie->setTermDatabase( d_db );

  if(Options::current()->finiteModelFind ){
    addInstStrategy( new InstStrategyFinteModelFind( c, this, ((TheoryUF*)th)->getStrongSolver(), ie ) );
  }else{
    if( Options::current()->cbqi ){
      addInstStrategy( new InstStrategyCheckCESolved( this, ie ) );
    }
    d_isup = new InstStrategyUserPatterns( this, ie );
    addInstStrategy( d_isup );
    InstStrategyAutoGenTriggers* i_ag = new InstStrategyAutoGenTriggers( this, ie, Trigger::TS_ALL, 
                                                                         InstStrategyAutoGenTriggers::RELEVANCE_DEFAULT, 3 );
    i_ag->setGenerateAdditional( true );
    addInstStrategy( i_ag );
    addInstStrategy( new InstStrategyFreeVariable( this, ie ) );
    //d_isup->setPriorityOver( i_ag );
    //d_isup->setPriorityOver( i_agm );
    //i_ag->setPriorityOver( i_agm );
  }
}

//void InstantiatorTheoryUf::addObligationToList( Node o, Node f ){
//  NodeList* ob;
//  NodeLists::iterator ob_i = d_obligations.find( f );
//  if( ob_i==d_obligations.end() ){
//    ob = new(d_th->getContext()->getCMM()) NodeList(true, d_th->getContext(), false,
//                                                    ContextMemoryAllocator<Node>(d_th->getContext()->getCMM()));
//    d_obligations.insertDataFromContextMemory( f, ob );
//  }else{
//    ob = (*ob_i).second;
//  }
//  for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
//    if( *it==o ){
//      return;
//    }
//  }
//  d_ob_changed[f] = true;
//  ob->push_back( o );
//}
//
//void InstantiatorTheoryUf::addObligations( Node n, Node ob ){
//  if( n.hasAttribute(InstConstantAttribute()) ){
//    addObligationToList( ob, n.getAttribute(InstConstantAttribute()) );
//  }else{
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      addObligations( n[i], ob );
//    }
//  }
//}

void InstantiatorTheoryUf::preRegisterTerm( Node t ){
  switch(t.getKind()) {
  case kind::EQUAL:
    d_quantEngine->addTermToDatabase( t[0] );
    d_quantEngine->addTermToDatabase( t[1] );
    break;
  case kind::NOT:
    if( t[0].getKind()==EQUAL || t[0].getKind()==IFF ){
      d_quantEngine->addTermToDatabase( t[0][0] );
      d_quantEngine->addTermToDatabase( t[0][1] );
    }else if( t[0].getKind()==APPLY_UF ){
      d_quantEngine->addTermToDatabase( t[0] );
    }
    break;
  case kind::CARDINALITY_CONSTRAINT:
    break;
  default:
    d_quantEngine->addTermToDatabase( t );
    break;
  }
  if( t.hasAttribute(InstConstantAttribute()) ){
    setHasConstraintsFrom( t.getAttribute(InstConstantAttribute()) );
  }else if( t.getKind()==NOT && t[0].hasAttribute(InstConstantAttribute()) ){
    setHasConstraintsFrom( t[0].getAttribute(InstConstantAttribute()) );
  }
}

void InstantiatorTheoryUf::assertNode( Node assertion )
{
  Debug("quant-uf-assert") << "InstantiatorTheoryUf::check: " << assertion << std::endl;
  preRegisterTerm( assertion );
  ////addObligations( assertion, assertion );
}

void InstantiatorTheoryUf::addUserPattern( Node f, Node pat ){
  if( d_isup ){
    d_isup->addUserPattern( f, pat );
  }
  setHasConstraintsFrom( f );
}


void InstantiatorTheoryUf::processResetInstantiationRound( Theory::Effort effort ){
  d_ground_reps.clear();
}

int InstantiatorTheoryUf::process( Node f, Theory::Effort effort, int e, int instLimit ){
  Debug("quant-uf") << "UF: Try to solve (" << e << ") for " << f << "... " << std::endl;
  return InstStrategy::STATUS_SAT;
}

void InstantiatorTheoryUf::debugPrint( const char* c )
{

}

bool InstantiatorTheoryUf::areEqual( Node a, Node b ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) &&
      ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( b ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.areEqual( a, b );
  }else{
    return a==b;
  }
}

bool InstantiatorTheoryUf::areDisequal( Node a, Node b ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) &&
      ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( b ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.areDisequal( a, b );
  }else{
    return false;
  }
}

Node InstantiatorTheoryUf::getRepresentative( Node a ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.getRepresentative( a );
  }else{
    return a;
  }
}

Node InstantiatorTheoryUf::getInternalRepresentative( Node a ){
  if( d_ground_reps.find( a )==d_ground_reps.end() ){
    if( !((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) ){
      return a;
    }else{
      Node rep = getRepresentative( a );
      if( !rep.hasAttribute(InstLevelAttribute()) ){
        //return the representative of a
        d_ground_reps[a] = rep;
        return rep;
      }else{
        //otherwise, must search eq class
        EqClassIterator eqc_iter( rep, &((TheoryUF*)d_th)->d_equalityEngine );
        rep = Node::null();
        while( !eqc_iter.isFinished() ){
          if( !(*eqc_iter).hasAttribute(InstConstantAttribute()) ){
            d_ground_reps[ a ] = *eqc_iter;
            return *eqc_iter;
          }
          eqc_iter++;
        }
        d_ground_reps[ a ] = a;
      }
    }
  }
  return d_ground_reps[a];
}

//void InstantiatorTheoryUf::getObligations( Node f, std::vector< Node >& obs ){
//  NodeLists::iterator ob_i = d_obligations.find( f );
//  if( ob_i!=d_obligations.end() ){
//    NodeList* ob = (*ob_i).second;
//    //std::cout  << "Generate trigger for literal matching..." << std::endl;
//    //this is matching at the literal level : use obligations of f as pattern terms
//    for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
//      obs.push_back( *it );
//    }
//    d_ob_changed[f] = false;
//  }
//}

InstantiatorTheoryUf::Statistics::Statistics():
  //d_instantiations("InstantiatorTheoryUf::Total_Instantiations", 0),
  d_instantiations_ce_solved("InstantiatorTheoryUf::Instantiations_CE-Solved", 0),
  d_instantiations_e_induced("InstantiatorTheoryUf::Instantiations_E-Induced", 0),
  d_instantiations_user_pattern("InstantiatorTheoryUf::Instantiations_User_Pattern", 0),
  d_instantiations_guess("InstantiatorTheoryUf::Instantiations_Free_Var", 0),
  d_instantiations_auto_gen("InstantiatorTheoryUf::Instantiations_Auto_Gen", 0),
  d_instantiations_auto_gen_min("InstantiatorTheoryUf::Instantiations_Auto_Gen_Min", 0),
  d_splits("InstantiatorTheoryUf::Total_Splits", 0)
{
  //StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_instantiations_ce_solved);
  StatisticsRegistry::registerStat(&d_instantiations_e_induced);
  StatisticsRegistry::registerStat(&d_instantiations_user_pattern );
  StatisticsRegistry::registerStat(&d_instantiations_guess );
  StatisticsRegistry::registerStat(&d_instantiations_auto_gen );
  StatisticsRegistry::registerStat(&d_instantiations_auto_gen_min );
  StatisticsRegistry::registerStat(&d_splits);
}

InstantiatorTheoryUf::Statistics::~Statistics(){
  //StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_instantiations_ce_solved);
  StatisticsRegistry::unregisterStat(&d_instantiations_e_induced);
  StatisticsRegistry::unregisterStat(&d_instantiations_user_pattern );
  StatisticsRegistry::unregisterStat(&d_instantiations_guess );
  StatisticsRegistry::unregisterStat(&d_instantiations_auto_gen );
  StatisticsRegistry::unregisterStat(&d_instantiations_auto_gen_min );
  StatisticsRegistry::unregisterStat(&d_splits);
}

/** new node */
void InstantiatorTheoryUf::newEqClass( TNode n ){

}

/** merge */
void InstantiatorTheoryUf::merge( TNode a, TNode b ){
  if( Options::current()->efficientEMatching ){
    if( a.getKind()!=IFF && a.getKind()!=EQUAL && b.getKind()!=IFF && b.getKind()!=EQUAL ){
      Debug("efficient-e-match") << "Merging " << a << " with " << b << std::endl;

      //determine new candidates for instantiation
      computeCandidatesPcPairs( a, b );
      computeCandidatesPcPairs( b, a );
      computeCandidatesPpPairs( a, b );
      computeCandidatesPpPairs( b, a );
    }
    //merge eqc_ops of b into a
    EqClassInfo* eci_a = getOrCreateEquivalenceClassInfo( a );
    EqClassInfo* eci_b = getOrCreateEquivalenceClassInfo( b );
    eci_a->merge( eci_b );
  }
}

/** assert terms are disequal */
void InstantiatorTheoryUf::assertDisequal( TNode a, TNode b, TNode reason ){
  
}

EqClassInfo* InstantiatorTheoryUf::getEquivalenceClassInfo( Node n ) { 
  return d_eqc_ops.find( n )==d_eqc_ops.end() ? NULL : d_eqc_ops[n]; 
}
EqClassInfo* InstantiatorTheoryUf::getOrCreateEquivalenceClassInfo( Node n ){
  Assert( n==getRepresentative( n ) );
  if( d_eqc_ops.find( n )==d_eqc_ops.end() ){
    EqClassInfo* eci = new EqClassInfo( d_th->getContext() );
    eci->setMember( n, d_db );
    d_eqc_ops[n] = eci;
  }
  return d_eqc_ops[n]; 
}

void InstantiatorTheoryUf::computeCandidatesPcPairs( Node a, Node b ){
  Debug("efficient-e-match") << "Compute candidates for pc pairs..." << std::endl;
  Debug("efficient-e-match") << "  Eq class = [";
  outputEqClass( "efficient-e-match", a);
  Debug("efficient-e-match") << "]" << std::endl;
  EqClassInfo* eci_a = getOrCreateEquivalenceClassInfo( a );
  EqClassInfo* eci_b = getOrCreateEquivalenceClassInfo( a );
  for( BoolMap::iterator it = eci_a->d_funs.begin(); it != eci_a->d_funs.end(); it++ ) {
    //the child function:  a member of eq_class( a ) has top symbol g, in other words g is in funs( a )
    Node g = (*it).first;
    Debug("efficient-e-match") << "  Checking application " << g << std::endl;
    //look at all parent/child pairs
    for( std::map< Node, std::map< Node, std::vector< InvertedPathString > > >::iterator itf = d_pc_pairs[g].begin(); 
         itf != d_pc_pairs[g].end(); ++itf ){
      //f/g is a parent/child pair
      Node f = itf->first;
      if( eci_b->hasParent( f ) || true ){
        //DO_THIS: determine if f in pfuns( b ), only do the follow if so
        Debug("efficient-e-match") << "    Checking parent application " << f << std::endl;
        //scan through the list of inverted path strings/candidate generators
        for( std::map< Node, std::vector< InvertedPathString > >::iterator cit = itf->second.begin(); 
            cit != itf->second.end(); ++cit ){
          Node pat = cit->first;
          Debug("efficient-e-match") << "      Checking pattern " << pat << std::endl;
          for( int c=0; c<(int)cit->second.size(); c++ ){
            Debug("efficient-e-match") << "        Check inverted path string for pattern ";
            outputInvertedPathString( "efficient-e-match", cit->second[c] );
            Debug("efficient-e-match") << std::endl;

            //collect all new relevant terms
            std::vector< Node > terms;
            terms.push_back( b );
            collectTermsIps( cit->second[c], terms );
            if( !terms.empty() ){
              Debug("efficient-e-match") << "        -> Added terms (" << (int)terms.size() << "): ";
              //add them as candidates to the candidate generator
              for( int t=0; t<(int)terms.size(); t++ ){
                Debug("efficient-e-match") << terms[t] << " ";
                //std::cout << "Add candidate (PC) " << terms[t] << std::endl;
                for( int cg=0; cg<(int)d_pat_cand_gens[pat].size(); cg++ ){
                  d_pat_cand_gens[pat][cg]->addCandidate( terms[t] );
                }
              }
              Debug("efficient-e-match") << std::endl;
            }
          }
        }
      }
    }
  }
}

void InstantiatorTheoryUf::computeCandidatesPpPairs( Node a, Node b ){
  Debug("efficient-e-match") << "Compute candidates for pp pairs..." << std::endl;
  EqClassInfo* eci_a = getOrCreateEquivalenceClassInfo( a );
  EqClassInfo* eci_b = getOrCreateEquivalenceClassInfo( a );
  for( std::map< Node, std::map< Node, std::map< Node, std::vector< IpsPair > > > >::iterator it = d_pp_pairs.begin();
       it != d_pp_pairs.end(); ++it ){
    Node f = it->first;
    if( eci_a->hasParent( f ) ){
      Debug("efficient-e-match") << "  Checking parent application " << f << std::endl;
      for( std::map< Node, std::map< Node, std::vector< IpsPair > > >::iterator it2 = it->second.begin();
           it2 != it->second.end(); ++it2 ){
        Node g = it2->first;
        if( eci_b->hasParent( g ) ){
          Debug("efficient-e-match") << "    Checking parent application " << g << std::endl;
          //if f in pfuns( a ) and g is in pfuns( b ), only do the follow if so
          for( std::map< Node, std::vector< IpsPair > >::iterator cit = it2->second.begin(); 
               cit != it2->second.end(); ++cit ){
            Node pat = cit->first;
            for( int c=0; c<(int)cit->second.size(); c++ ){
              std::vector< Node > a_terms;
              a_terms.push_back( a );
              if( !a_terms.empty() ){
                collectTermsIps( cit->second[c].first, a_terms );
                std::vector< Node > b_terms;
                b_terms.push_back( b );
                collectTermsIps( cit->second[c].first, b_terms );
                //take intersection
                for( int t=0; t<(int)a_terms.size(); t++ ){
                  if( std::find( b_terms.begin(), b_terms.end(), a_terms[t] )!=b_terms.end() ){
                                //std::cout << "Add candidate (PP) " << a_terms[t] << std::endl;
                    Debug("efficient-e-match") << "      -> Add term " << a_terms[t] << std::endl;
                    //add to all candidate generators having this term
                    for( int cg=0; cg<(int)d_pat_cand_gens[pat].size(); cg++ ){
                      d_pat_cand_gens[pat][cg]->addCandidate( a_terms[t] );
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  } 
}

void InstantiatorTheoryUf::collectTermsIps( InvertedPathString& ips, std::vector< Node >& terms, int index ){
  if( index<(int)ips.size() && !terms.empty() ){
    Debug("efficient-e-match-debug") << "> Process " << index << std::endl;
    Node f = ips[index].first;
    int arg = ips[index].second;

    //for each term in terms, determine if any term (modulo equality) has parent "f" from position "arg"
    bool addRep = ( index!=(int)ips.size()-1 );
    std::vector< Node > newTerms;
    for( int t=0; t<(int)terms.size(); t++ ){
      collectParentsTermsIps( terms[t], f, arg, newTerms, addRep );
    }
    terms.clear();
    terms.insert( terms.begin(), newTerms.begin(), newTerms.end() );

    Debug("efficient-e-match-debug") << "> Terms are now: ";
    for( int t=0; t<(int)terms.size(); t++ ){
      Debug("efficient-e-match-debug") << terms[t] << " ";
    }
    Debug("efficient-e-match-debug") << std::endl;

    collectTermsIps( ips, terms, index+1 );
  }
}

bool InstantiatorTheoryUf::collectParentsTermsIps( Node n, Node f, int arg, std::vector< Node >& terms, bool addRep, bool modEq ){
  bool addedTerm = false;
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) && modEq ){
    Assert( getRepresentative( n )==n );
    //collect modulo equality
    //DO_THIS: this should (if necessary) compute a current set of (f, arg) parents for n and cache it
    EqClassIterator eqc_iter( getRepresentative( n ), &((TheoryUF*)d_th)->d_equalityEngine );
    while( !eqc_iter.isFinished() ){
      if( collectParentsTermsIps( (*eqc_iter), f, arg, terms, addRep, false ) ){
        //if only one argument, we know we can stop (since all others added will be congruent)
        if( f.getType().getNumChildren()==2 ){
          return true;
        }
        addedTerm = true;
      }
      eqc_iter++;
    }
  }else{
    //see if parent f exists from argument arg
    if( d_db->d_parents.find( n )!=d_db->d_parents.end() ){
      if( d_db->d_parents[n].find( f )!=d_db->d_parents[n].end() ){
        if( d_db->d_parents[n][f].find( arg )!=d_db->d_parents[n][f].end() ){
          for( int i=0; i<(int)d_db->d_parents[n][f][arg].size(); i++ ){
            Node t = d_db->d_parents[n][f][arg][i];
            if( addRep ){
              t = getRepresentative( t );
            }
            if( std::find( terms.begin(), terms.end(), t )==terms.end() ){
              terms.push_back( t );
            }
            addedTerm = true;
          }
        }
      }
    }
  }
  return addedTerm;
}

void InstantiatorTheoryUf::registerPatternElementPairs2( Node opat, Node pat, InvertedPathString& ips, 
                                                       std::map< Node, std::vector< std::pair< Node, InvertedPathString > > >& ips_map  ){
  Assert( pat.getKind()==APPLY_UF );
  //add information for possible pp-pair
  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    if( pat[i].getKind()==INST_CONSTANT ){
      ips_map[ pat[i] ].push_back( std::pair< Node, InvertedPathString >( pat.getOperator(), InvertedPathString( ips ) ) );
    }
  }
  ips.push_back( std::pair< Node, int >( pat.getOperator(), 0 ) );
  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    if( pat[i].getKind()==APPLY_UF ){
      ips.back().second = i;
      registerPatternElementPairs2( opat, pat[i], ips, ips_map );
      Debug("pattern-element-opt") << "Found pc-pair ( " << pat.getOperator() << ", " << pat[i].getOperator() << " )" << std::endl;
      Debug("pattern-element-opt") << "   Path = ";
      outputInvertedPathString( "pattern-element-opt", ips );
      Debug("pattern-element-opt") << std::endl;
      //pat.getOperator() and pat[i].getOperator() are a pc-pair
      d_pc_pairs[ pat[i].getOperator() ][ pat.getOperator() ][opat].push_back( InvertedPathString( ips ) );
    }
  }
  ips.pop_back();
}

void InstantiatorTheoryUf::registerPatternElementPairs( Node pat ){
  InvertedPathString ips;
  std::map< Node, std::vector< std::pair< Node, InvertedPathString > > > ips_map;
  registerPatternElementPairs2( pat, pat, ips, ips_map );
  for( std::map< Node, std::vector< std::pair< Node, InvertedPathString > > >::iterator it = ips_map.begin(); it != ips_map.end(); ++it ){
    for( int j=0; j<(int)it->second.size(); j++ ){
      for( int k=j+1; k<(int)it->second.size(); k++ ){
        //found a pp-pair
        Debug("pattern-element-opt") << "Found pp-pair ( " << it->second[j].first << ", " << it->second[k].first << " )" << std::endl;
        Debug("pattern-element-opt") << "   Paths = ";
        outputInvertedPathString( "pattern-element-opt", it->second[j].second );
        Debug("pattern-element-opt") << " and ";
        outputInvertedPathString( "pattern-element-opt", it->second[k].second );
        Debug("pattern-element-opt") << std::endl;
        d_pp_pairs[ it->second[j].first ][ it->second[k].first ][pat].push_back( IpsPair( it->second[j].second, it->second[k].second ) );
      }
    }
  }
}

void InstantiatorTheoryUf::registerCandidateGenerator( CandidateGenerator* cg, Node pat ){
  Debug("efficient-e-match") << "Register candidate generator..." << pat << std::endl;
  if( d_pat_cand_gens.find( pat )==d_pat_cand_gens.end() ){
    registerPatternElementPairs( pat );
  }
  d_pat_cand_gens[pat].push_back( cg );
  
  //take all terms from the uf term db and add to candidate generator
  Node op = pat.getOperator();
  for( int i=0; i<(int)d_db->d_op_map[op].size(); i++ ){
    cg->addCandidate( d_db->d_op_map[op][i] );
  }
  d_cand_gens[op].push_back( cg );

  Debug("efficient-e-match") << "Done." << std::endl;
}

void InstantiatorTheoryUf::outputEqClass( const char* c, Node n ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) ){
    EqClassIterator eqc_iter( getRepresentative( n ), 
                              &((TheoryUF*)d_th)->d_equalityEngine );
    bool firstTime = true;
    while( !eqc_iter.isFinished() ){
      if( !firstTime ){ Debug(c) << ", "; }
      Debug(c) << (*eqc_iter);
      firstTime = false;
      eqc_iter++;
    }
  }else{
    Debug(c) << n;
  }
}

void InstantiatorTheoryUf::outputInvertedPathString( const char* c, InvertedPathString& ips ){
  for( int i=0; i<(int)ips.size(); i++ ){
    if( i>0 ){ Debug( c ) << "."; }
    Debug( c ) << ips[i].first << "." << ips[i].second;
  }
}

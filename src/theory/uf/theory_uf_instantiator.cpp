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

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

#define USE_LITERAL_MATCHING
#define USE_FREE_VARIABLE_INSTANTIATION

void InstStrategyCheckCESolved::resetInstantiationRound(){
  for( std::map< Node, bool >::iterator it = d_solved.begin(); it != d_solved.end(); ++it ){
    calcSolved( it->first );
  }
}

int InstStrategyCheckCESolved::process( Node f, int effort, int instLimit ){
  if( effort==0 ){
    //calc solved if not done so already
    if( d_solved.find( f )==d_solved.end() ){
      calcSolved( f );
    }
    //check if f is counterexample-solved
    if( d_solved[ f ] ){
      if( d_quantEngine->addInstantiation( f, &d_th->d_baseMatch[f] ) ){
        ++(d_th->d_statistics.d_instantiations);
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

void InstStrategyLitMatch::resetInstantiationRound(){
  
}

int InstStrategyLitMatch::process( Node f, int effort, int instLimit ){
  //if( effort==0 ){
  //  return STATUS_UNFINISHED;
  //}else{
  //  //this is matching at the literal level : use obligations of f as pattern terms
  //  if( d_th->getObligationsChanged( f ) ){
  //    Debug("quant-uf-strategy")  << "Generate trigger for literal matching..." << std::endl;
  //    //std::cout  << "Generate trigger for literal matching..." << std::endl;
  //    std::vector< Node > pats;
  //    d_th->getObligations( f, pats );
  //    if( !pats.empty() ){
  //      //if( d_lit_match_triggers.find( f )!=d_lit_match_triggers.end() && d_lit_match_triggers[ f ] ){
  //      //  delete d_lit_match_triggers[ f ];
  //      //}
  //      d_lit_match_triggers[ f ] = Trigger::mkTrigger( d_quantEngine, f, pats, true, false );
  //    }else{
  //      d_lit_match_triggers[ f ] = NULL;
  //    }
  //  }else{
  //    if( effort==1 && d_lit_match_triggers.find( f )!=d_lit_match_triggers.end() && d_lit_match_triggers[ f ] ){
  //      d_lit_match_triggers[ f ]->resetInstantiationRound();
  //    }
  //  }
  //  Debug("quant-uf-strategy")  << "Try literal matching..." << std::endl;
  //  //std::cout << "Try literal matching for " << f << "..." << std::endl;
  //  if( d_lit_match_triggers[ f ] ){
  //    int numInst = d_lit_match_triggers[ f ]->addInstantiations( d_th->d_baseMatch[f], false );
  //    d_th->d_statistics.d_instantiations += numInst;
  //    d_th->d_statistics.d_instantiations_e_induced += numInst;
  //    //d_quantEngine->d_hasInstantiated[f] = true;
  //  }
  //  Debug("quant-uf-strategy") << "done." << std::endl;
  //  //std::cout << "done" << std::endl;
  //}
  return STATUS_UNKNOWN;
}

void InstStrategyUserPatterns::resetInstantiationRound(){
  for( std::map< Node, std::vector< Trigger* > >::iterator it = d_user_gen.begin(); it != d_user_gen.end(); ++it ){
    for( int i=0; i<(int)it->second.size(); i++ ){
      it->second[i]->resetInstantiationRound();
      it->second[i]->reset( Node::null() );
    }
  }
}

int InstStrategyUserPatterns::process( Node f, int effort, int instLimit ){
  if( effort==0 ){
    return STATUS_UNFINISHED;
  }else if( effort==1 ){
    Debug("quant-uf-strategy") << "Try user-provided patterns..." << std::endl;
    //std::cout << "Try user-provided patterns..." << std::endl;
    for( int i=0; i<(int)d_user_gen[f].size(); i++ ){
      int numInst = d_user_gen[f][i]->addInstantiations( d_th->d_baseMatch[f], instLimit );
      d_th->d_statistics.d_instantiations += numInst;
      d_th->d_statistics.d_instantiations_user_pattern += numInst;
      //d_quantEngine->d_hasInstantiated[f] = true;
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
    d_user_gen[f].push_back( Trigger::mkTrigger( d_quantEngine, f, nodes, false, true ) );
  }
}
 
void InstStrategyAutoGenTriggers::resetInstantiationRound(){
  for( std::map< Node, Trigger* >::iterator it = d_auto_gen_trigger.begin(); it != d_auto_gen_trigger.end(); ++it ){
    if( it->second ){
      it->second->resetInstantiationRound();
      it->second->reset( Node::null() );
    }
  }
}

int InstStrategyAutoGenTriggers::process( Node f, int effort, int instLimit ){
  int peffort = f.getNumChildren()==3 ? 2 : 1;
  if( effort<peffort ){
    return STATUS_UNFINISHED;
  }else if( effort==peffort ){
    Trigger* tr = getAutoGenTrigger( f );
    if( !tr ){
      return STATUS_UNKNOWN;
    }else{
      Debug("quant-uf-strategy")  << "Try auto-generated triggers... " << d_tr_strategy << " " << getAutoGenTrigger( f ) << std::endl;
      //std::cout << "Try auto-generated triggers..." << std::endl;
      int numInst = tr->addInstantiations( d_th->d_baseMatch[f], instLimit );
      d_th->d_statistics.d_instantiations += numInst;
      //d_quantEngine->d_hasInstantiated[f] = true;
      Debug("quant-uf-strategy") << "done." << std::endl;
      //std::cout << "done" << std::endl;
    }
  }
  return STATUS_UNKNOWN;
}

void InstStrategyAutoGenTriggers::collectPatTerms( Node f, Node n, std::vector< Node >& patTerms, int tstrt ){
  if( tstrt==MAX_TRIGGER ){
    if( n.getKind()==APPLY_UF && n.getAttribute(InstConstantAttribute())==f && Trigger::isUsableTrigger( n, f ) ){
      if( std::find( patTerms.begin(), patTerms.end(), n )==patTerms.end() ){
        patTerms.push_back( n );
      }
    }else if( n.getKind()!=FORALL ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        collectPatTerms( f, n[i], patTerms, tstrt );
      }
    }
  }else if( tstrt==MIN_TRIGGER ){
    if( n.getKind()!=FORALL ){
      int patTermSize = (int)patTerms.size();
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        collectPatTerms( f, n[i], patTerms, tstrt );
      }
      if( n.getKind()==APPLY_UF && n.getAttribute(InstConstantAttribute())==f && patTermSize==(int)patTerms.size() ){
        if( std::find( patTerms.begin(), patTerms.end(), n )==patTerms.end() ){
          if( Trigger::isUsableTrigger( n, f ) ){
            patTerms.push_back( n );
          } 
        }
      }
    }
  }
}

Trigger* InstStrategyAutoGenTriggers::getAutoGenTrigger( Node f ){
  if( d_auto_gen_trigger.find( f )==d_auto_gen_trigger.end() ){
    //if( f.getNumChildren()==3 ){
    //  //don't auto-generate any trigger for quantifiers with user-provided patterns
    //  d_auto_gen_trigger[f] = NULL;
    //}else{
      std::vector< Node > patTerms;
      collectPatTerms( f, d_quantEngine->getCounterexampleBody( f ), patTerms, d_tr_strategy );
      //std::cout << "patTerms = " << (int)patTerms.size() << std::endl;
      if( !patTerms.empty() ){
        Trigger* tr = Trigger::mkTrigger( d_quantEngine, f, patTerms, false, false, Trigger::TRP_RETURN_NULL );
        //making it during an instantiation round, so must reset
        if( tr ){
          tr->resetInstantiationRound();
          tr->reset( Node::null() );
        }
        d_auto_gen_trigger[f] = tr;
      }else{
        d_auto_gen_trigger[f] = NULL;
      }
    //}
  }
  return d_auto_gen_trigger[f];
}

void InstStrategyFreeVariable::resetInstantiationRound(){
  
}

int InstStrategyFreeVariable::process( Node f, int effort, int instLimit ){
  if( effort<5 ){
    return STATUS_UNFINISHED;
  }else{
    if( d_guessed.find( f )==d_guessed.end() ){
      d_guessed[f] = true;
      Debug("quant-uf-alg") << "Add guessed instantiation" << std::endl;
      InstMatch m;
      if( d_quantEngine->addInstantiation( f, &m ) ){
        ++(d_th->d_statistics.d_instantiations);
        ++(d_th->d_statistics.d_instantiations_guess);
        //d_quantEngine->d_hasInstantiated[f] = true;
      }
    }
    return STATUS_UNKNOWN;
  }
}

void UfTermDb::add( Node n ){
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( !n.hasAttribute(InstConstantAttribute()) ){
      if( std::find( d_op_map[op].begin(), d_op_map[op].end(), n )==d_op_map[op].end() ){
        Debug("uf-term-db") << "register term " << n << std::endl;
        d_op_map[op].push_back( n );
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          add( n[i] );
        }
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        add( n[i] );
      }
    }
  }
}
void UfTermDb::finishInstantiationRound(){
  for( std::map< Node, std::vector< Node > >::iterator it = d_op_map.begin(); it != d_op_map.end(); ++it ){
    d_op_index[ it->first ] = (int)it->second.size();
  }
}

EqClassInfo::EqClassInfo( context::Context* c ) : d_funs( c ), d_pfuns( c ), d_disequal( c ){

}

//set member
void EqClassInfo::setMember( Node n ){

}

//get has function 
bool EqClassInfo::hasFunction( Node op ){
  return false;
}

//merge with another eq class info
void EqClassInfo::merge( EqClassInfo* eci ){
  
}


InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::QuantifiersEngine* ie, Theory* th) :
Instantiator( c, ie, th )
//d_ob_changed( c ),
//d_obligations( c ),
//d_disequality( c )
{
  d_db = new UfTermDb( this );

  d_isup = new InstStrategyUserPatterns( this, ie );
  addInstStrategy( new InstStrategyCheckCESolved( this, ie ) );
  //addInstStrategy( new InstStrategyLitMatch( this, ie ) );
  addInstStrategy( d_isup );
  addInstStrategy( new InstStrategyAutoGenTriggers( this, ie, InstStrategyAutoGenTriggers::MAX_TRIGGER ) );
  addInstStrategy( new InstStrategyAutoGenTriggers( this, ie, InstStrategyAutoGenTriggers::MIN_TRIGGER ) );
  addInstStrategy( new InstStrategyFreeVariable( this, ie ) );
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
    d_db->add( t[0] );
    d_db->add( t[1] );
    break;
  case kind::NOT:
    if( t[0].getKind()==EQUAL || t[0].getKind()==IFF ){
      d_db->add( t[0][0] );
      d_db->add( t[0][1] );
    }else if( t[0].getKind()==APPLY_UF ){
      d_db->add( t[0] );
    }
    break;
  case kind::CARDINALITY_CONSTRAINT:
    break;
  default:
    d_db->add( t );
    break;
  }
  if( t.hasAttribute(InstConstantAttribute()) ){
    setHasConstraintsFrom( t.getAttribute(InstConstantAttribute()) );
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


void InstantiatorTheoryUf::resetInstantiationRound(){
  d_ground_reps.clear();
}

void InstantiatorTheoryUf::debugPrint( const char* c )
{

}

bool InstantiatorTheoryUf::areEqual( Node a, Node b ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) &&
      ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( b ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.areEqual( a, b );
  }else{
    return false;
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
      //a is singleton equivalence class, just return it
      d_ground_reps[ a ] = a;
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

int InstantiatorTheoryUf::process( Node f, int effort, int instLimit ){
  Debug("quant-uf") << "UF: Try to solve (" << effort << ") for " << f << "... " << std::endl;
  return InstStrategy::STATUS_UNKNOWN;
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
  d_instantiations("InstantiatorTheoryUf::Total_Instantiations", 0),
  d_instantiations_ce_solved("InstantiatorTheoryUf::CE-Solved_Instantiations", 0),
  d_instantiations_e_induced("InstantiatorTheoryUf::E-Induced_Instantiations", 0),
  d_instantiations_user_pattern("InstantiatorTheoryUf::User_Pattern_Instantiations", 0),
  d_instantiations_guess("InstantiatorTheoryUf::Free_Var_Instantiations", 0),
  d_splits("InstantiatorTheoryUf::Total_Splits", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_instantiations_ce_solved);
  StatisticsRegistry::registerStat(&d_instantiations_e_induced);
  StatisticsRegistry::registerStat(&d_instantiations_user_pattern );
  StatisticsRegistry::registerStat(&d_instantiations_guess );
  StatisticsRegistry::registerStat(&d_splits);
}

InstantiatorTheoryUf::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_instantiations_ce_solved);
  StatisticsRegistry::unregisterStat(&d_instantiations_e_induced);
  StatisticsRegistry::unregisterStat(&d_instantiations_user_pattern );
  StatisticsRegistry::unregisterStat(&d_instantiations_guess );
  StatisticsRegistry::unregisterStat(&d_splits);
}

/** new node */
void InstantiatorTheoryUf::newEqClass( TNode n ){
#if 0

#endif
}

/** merge */
void InstantiatorTheoryUf::merge( TNode a, TNode b ){
#if 0
  EqClassInfo* eci_a = getEquivalenceClassInfo( a );
  //merge eqc_ops of b into a
  if( d_eqc_ops.find( b )==d_eqc_ops.end() ){
    eci_a->setMember( b );
  }else{
    eci_a->merge( d_eqc_ops[b] );
  }
#endif
}

/** assert terms are disequal */
void InstantiatorTheoryUf::assertDisequal( TNode a, TNode b, TNode reason ){
  
}

EqClassInfo* InstantiatorTheoryUf::getEquivalenceClassInfo( Node n ) { 
  Assert( n==getRepresentative( n ) );
  if( d_eqc_ops.find( n )==d_eqc_ops.end() ){
    EqClassInfo* eci = new EqClassInfo( d_th->getContext() );
    eci->setMember( n );
    d_eqc_ops[n] = eci;
  }
  return d_eqc_ops[n]; 
}

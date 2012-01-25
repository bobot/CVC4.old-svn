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
  
}

int InstStrategyCheckCESolved::process( Node f, int effort ){
  if( effort==0 ){
    d_th->d_baseMatch.clear();
    //check if any instantiation constants are solved for
    for( int j = 0; j<(int)d_instEngine->getNumInstantiationConstants( f ); j++ ){
      Node i = d_instEngine->getInstantiationConstant( f, j );
      Node rep = d_th->getInternalRepresentative( i );
      if( !rep.hasAttribute(InstConstantAttribute()) ){
        d_th->d_baseMatch.setMatch( i, rep );
      }
    }
    //check if f is counterexample-solved
    if( d_th->d_baseMatch.isComplete( f ) ){
      if( d_instEngine->addInstantiation( f, &d_th->d_baseMatch ) ){
        ++(d_th->d_statistics.d_instantiations);
        ++(d_th->d_statistics.d_instantiations_ce_solved);
      }
    } 
  }
  return STATUS_UNKNOWN;
}

void InstStrategyLitMatch::resetInstantiationRound(){
  
}

int InstStrategyLitMatch::process( Node f, int effort ){
  if( effort==0 ){
    return STATUS_UNFINISHED;
  }else{
    //this is matching at the literal level : use obligations of f as pattern terms
    Debug("quant-uf-debug")  << "Generate trigger for literal matching..." << std::endl;
    //std::cout  << "Generate trigger for literal matching..." << std::endl;
    if( d_th->getObligationsChanged( f ) ){
      std::vector< Node > pats;
      d_th->getObligations( f, pats );
      if( !pats.empty() ){
        //if( d_lit_match_triggers.find( f )!=d_lit_match_triggers.end() && d_lit_match_triggers[ f ] ){
        //  delete d_lit_match_triggers[ f ];
        //}
        d_lit_match_triggers[ f ] = new Trigger( d_instEngine, f, pats, true );
      }else{
        d_lit_match_triggers[ f ] = NULL;
      }
    }else{
      if( effort==1 && d_lit_match_triggers.find( f )!=d_lit_match_triggers.end() && d_lit_match_triggers[ f ] ){
        d_lit_match_triggers[ f ]->resetInstantiationRound( d_th );
      }
    }
    Debug("quant-uf-debug")  << "Try literal matching..." << std::endl;
    //std::cout << "Try literal matching for " << f << "..." << std::endl;
    if( d_lit_match_triggers[ f ] ){
      static int triggerThreshLit = effort==1 ? 1 : 2;
      if( d_lit_match_triggers[ f ]->addInstantiation( d_th, d_th->d_baseMatch, false, triggerThreshLit ) ){
        ++(d_th->d_statistics.d_instantiations);
        ++(d_th->d_statistics.d_instantiations_e_induced);
      }
    }
    Debug("quant-uf-debug") << "done." << std::endl;
    //std::cout << "done" << std::endl;
    return effort==2 ? STATUS_UNKNOWN : STATUS_UNFINISHED;
  }
}

void InstStrategyUserPatterns::resetInstantiationRound(){
  
}

int InstStrategyUserPatterns::process( Node f, int effort ){
  if( effort==0 ){
    return STATUS_UNFINISHED;
  }else{
    Debug("quant-uf-debug") << "Try user-provided patterns..." << std::endl;
    //std::cout << "Try user-provided patterns..." << std::endl;
    for( int i=0; i<(int)getNumUserGenerators( f ); i++ ){
      if( effort==1 ){
        getUserGenerator( f, i )->resetInstantiationRound( d_th );
      }
      if( getUserGenerator( f, i )->addInstantiation( d_th, d_th->d_baseMatch ) ){
        ++(d_th->d_statistics.d_instantiations);
        ++(d_th->d_statistics.d_instantiations_user_pattern);
      }
    }
    Debug("quant-uf-debug") << "done." << std::endl;
    //std::cout << "done" << std::endl;
    return effort==2 ? STATUS_UNKNOWN : STATUS_UNFINISHED;
  }
}

void InstStrategyUserPatterns::addUserPattern( Node f, Node pat ){
  //add to generators
  std::vector< Node > nodes;
  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    nodes.push_back( pat[i] );
  }
  d_user_gen[f].push_back( new Trigger( d_instEngine, f, nodes, true ) );
}

void InstStrategyAutoGenTriggers::resetInstantiationRound(){
  
}

int InstStrategyAutoGenTriggers::process( Node f, int effort ){
  if( effort==0 ){
    return STATUS_UNFINISHED;
  }else{
    Debug("quant-uf-debug")  << "Try auto-generated triggers..." << std::endl;
    //std::cout << "Try auto-generated triggers..." << std::endl;
    static int triggerThresh = effort==1 ? 1 : 2;
    if( effort==1 ){
      getAutoGenTrigger( f )->resetInstantiationRound( d_th );
    }
    if( getAutoGenTrigger( f )->addInstantiation( d_th, d_th->d_baseMatch, false, triggerThresh ) ){
      ++(d_th->d_statistics.d_instantiations);
    }
    Debug("quant-uf-debug") << "done." << std::endl;
    //std::cout << "done" << std::endl;
    return effort==2 ? STATUS_UNKNOWN : STATUS_UNFINISHED;
  }
}

void InstStrategyAutoGenTriggers::collectPatTerms( Node f, Node n, std::vector< Node >& patTerms ){
  if( n.getKind()==APPLY_UF && n.getAttribute(InstConstantAttribute())==f  ){
    if( std::find( patTerms.begin(), patTerms.end(), n )==patTerms.end() ){
      patTerms.push_back( n );
    }
  }else if( n.getKind()!=FORALL ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      collectPatTerms( f, n[i], patTerms );
    }
  }
}

Trigger* InstStrategyAutoGenTriggers::getAutoGenTrigger( Node f ){
  if( !d_auto_gen_trigger[f] ){
    std::vector< Node > patTerms;
    collectPatTerms( f, d_instEngine->getCounterexampleBody( f ), patTerms );
    d_auto_gen_trigger[f] = new Trigger( d_instEngine, f, patTerms, true );
  }
  return d_auto_gen_trigger[f];
}

void InstStrategyFreeVariable::resetInstantiationRound(){
  
}

int InstStrategyFreeVariable::process( Node f, int effort ){
  if( effort<5 ){
    return STATUS_UNFINISHED;
  }else{
    if( d_guessed.find( f )==d_guessed.end() ){
      d_guessed[f] = true;
      Debug("quant-uf-alg") << "Add guessed instantiation" << std::endl;
      InstMatch m;
      d_instEngine->addInstantiation( f, &m );
      ++(d_th->d_statistics.d_instantiations);
      ++(d_th->d_statistics.d_instantiations_guess);
    }
    return STATUS_UNKNOWN;
  }
}

void UfTermDb::registerTerm( Node n ){
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    int index = n.hasAttribute(InstConstantAttribute()) ? 1 : 0;
    int altIndex = index==0 ? 1 : 0;
    if( std::find( d_op_map[index][op].begin(), d_op_map[index][op].end(), n )==d_op_map[index][op].end() ){
      //std::cout << "register term " << n << std::endl;
      d_op_map[index][op].push_back( n );
      //add pattern/ground term pairs produced
      for( int i=0; i<(int)d_op_map[altIndex][op].size(); i++ ){
        if( index==0 ){
          InstMatchGenerator::addAnyMatchPair( d_op_map[altIndex][op][i], n );
        }else{
          InstMatchGenerator::addAnyMatchPair( n, d_op_map[altIndex][op][i] );
        }
      }
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        registerTerm( n[i] );
      }
    }
  }
}

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie, th ),
d_ob_changed( c ),
d_obligations( c ),
//d_terms_full( c ),
d_disequality( c )
{
  registerTerm( ((TheoryUF*)d_th)->d_true );
  registerTerm( ((TheoryUF*)d_th)->d_false );
  Node eq = NodeManager::currentNM()->mkNode( IFF, ((TheoryUF*)d_th)->d_true, ((TheoryUF*)d_th)->d_false );
  d_disequality.push_back( eq );

  d_isup = new InstStrategyUserPatterns( this, ie );
  addInstStrategy( new InstStrategyCheckCESolved( this, ie ) );
  addInstStrategy( new InstStrategyLitMatch( this, ie ) );
  addInstStrategy( d_isup );
  addInstStrategy( new InstStrategyAutoGenTriggers( this, ie ) );
  addInstStrategy( new InstStrategyFreeVariable( this, ie ) );
}

void InstantiatorTheoryUf::addObligationToList( Node o, Node f ){
  NodeList* ob;
  NodeLists::iterator ob_i = d_obligations.find( f );
  if( ob_i==d_obligations.end() ){
    ob = new(d_th->getContext()->getCMM()) NodeList(true, d_th->getContext(), false,
                                                    ContextMemoryAllocator<Node>(d_th->getContext()->getCMM()));
    d_obligations.insertDataFromContextMemory( f, ob );
  }else{
    ob = (*ob_i).second;
  }
  for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
    if( *it==o ){
      return;
    }
  }
  d_ob_changed[f] = true;
  ob->push_back( o );
}

void InstantiatorTheoryUf::addObligations( Node n, Node ob ){
  if( n.hasAttribute(InstConstantAttribute()) ){
    addObligationToList( ob, n.getAttribute(InstConstantAttribute()) );
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      addObligations( n[i], ob );
    }
  }
}

void InstantiatorTheoryUf::check( Node assertion )
{
  Debug("quant-uf-assert") << "InstantiatorTheoryUf::check: " << assertion << std::endl;
  addObligations( assertion, assertion );
  switch (assertion.getKind()) {
  case kind::EQUAL:
    registerTerm( assertion[0] );
    registerTerm( assertion[1] );
    break;
  case kind::APPLY_UF:
    registerTerm( assertion );
    break;
  case kind::NOT:
    if( assertion[0].getKind()==EQUAL || assertion[0].getKind()==IFF ){
      d_disequality.push_back( assertion[0] );
      registerTerm( assertion[0][0] );
      registerTerm( assertion[0][1] );
    }
    break;
  default:
    Unreachable();
  }
}

void InstantiatorTheoryUf::registerTerm( Node n ){
  d_db.registerTerm( n );
  if( n.hasAttribute(InstConstantAttribute()) ){
    setHasConstraintsFrom( n.getAttribute(InstConstantAttribute()) );
  }
}

void InstantiatorTheoryUf::addUserPattern( Node f, Node pat ){
  if( d_isup ){
    d_isup->addUserPattern( f, pat );
  }
  setHasConstraintsFrom( f );
}


void InstantiatorTheoryUf::resetInstantiationRound()
{
  d_litMatchCandidates[0].clear();
  d_litMatchCandidates[1].clear();
  //get representatives that will be used
  EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
  while( !eqc_iter.isFinished() ){
    EqClassIterator< TheoryUF::NotifyClass > eqc_iter2( *eqc_iter, &((TheoryUF*)d_th)->d_equalityEngine );
    Node rep;
    while( !eqc_iter2.isFinished() ){
      if( rep==Node::null() ){
        rep = *eqc_iter2;
      }else if( !(*eqc_iter2).hasAttribute(InstConstantAttribute()) ){
        if( rep.hasAttribute(InstConstantAttribute()) ){
          rep = *eqc_iter2;
        }else if( rep.hasAttribute(InstLevelAttribute()) ){
          if( !(*eqc_iter2).hasAttribute(InstLevelAttribute()) || 
              (*eqc_iter2).getAttribute(InstLevelAttribute())<rep.getAttribute(InstLevelAttribute()) ){
            rep = *eqc_iter2;
          }
        }
      }
      eqc_iter2++;
    }
    d_reps[ *eqc_iter ] = rep;
    eqc_iter++;
  }
  //build disequality lists
  d_dmap.clear();
  for( NodeList::const_iterator it = d_disequality.begin(); it!=d_disequality.end(); ++it ){
    Node n = (*it);
    Node r1 = getRepresentative( n[0] );
    Node r2 = getRepresentative( n[1] );
    if( std::find( d_dmap[r1].begin(), d_dmap[r1].end(), r2 )==d_dmap[r1].end() ){
      d_dmap[r1].push_back( r2 );
    }
    if( std::find( d_dmap[r2].begin(), d_dmap[r2].end(), r1 )==d_dmap[r2].end() ){
      d_dmap[r2].push_back( r1 );
    }
  }
  //debug print
  debugPrint("quant-uf-debug");
  Instantiator::resetInstantiationRound();
}

void InstantiatorTheoryUf::debugPrint( const char* c )
{
  //Debug( c ) << "Terms:" << std::endl;
  //for( BoolMap::const_iterator it = d_terms.begin(); it!=d_terms.end(); ++it ){
  //  Debug( c ) << "   " << (*it).first;
  //  //Debug( c ) << "  ->  " << getRepresentative( (*it).first );
  //  Debug( c ) << std::endl;
  //}
  EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
  while( !eqc_iter.isFinished() ){
    Debug( c ) << "Eq class [[" << (*eqc_iter) << "]]" << std::endl;
    EqClassIterator< TheoryUF::NotifyClass > eqc_iter2( *eqc_iter, &((TheoryUF*)d_th)->d_equalityEngine );
    Debug( c ) << "   ";
    while( !eqc_iter2.isFinished() ){
      Debug( c ) << "[" << (*eqc_iter2) << "] ";
      eqc_iter2++;
    }
    Debug( c ) << std::endl;
    eqc_iter++;
  }
  //Print disequalities? DO_THIS

  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    Node f = it->first;
    Debug( c ) << f;
    if( !d_instEngine->getActive( f ) ){
      Debug( c ) << " (***inactive***)";
    }
    Debug( c ) << std::endl;
    Debug( c ) << "   Inst constants:" << std::endl;
    Debug( c ) << "      ";
    for( int i=0; i<(int)d_instEngine->getNumInstantiationConstants( f ); i++ ){
      if( i>0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << d_instEngine->getInstantiationConstant( f, i );
      //if(d_terms_full.find( it->second[i] )==d_terms_full.end()){
      //  Debug( c ) << " (inactive)";
      //}
    }
    Debug( c ) << std::endl;
    Debug( c ) << "   Obligations:" << std::endl;
    NodeLists::iterator ob_i = d_obligations.find( f );
    if( ob_i!=d_obligations.end() ){
      NodeList* ob = (*ob_i).second;
      for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
        //Debug( c ) << "      " << ( !d_ob_pol[*it] ? "NOT " : "" );
        Debug( c ) << *it;
        //Debug( c ) << " " << ( d_ob_reqPol[ *it ] ? "(REQ)" : "" );
        Debug( c ) << std::endl;
      }
    }
  }

  Debug( c ) << std::endl;

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
  Node rep = getRepresentative( a );
  if( d_reps.find( rep )!=d_reps.end() ){
    return d_reps[ rep ];
  }else{
    return rep;
  }
  //if( !a.hasAttribute(InstConstantAttribute()) && rep.hasAttribute(InstConstantAttribute()) ){
  //  std::cout << "Violation: " << a << " " << rep << " " << getRepresentative( a ) << std::endl;
  //  std::cout << "eq class = ";
  //  Node rep2 = getRepresentative( a );
  //  EqClassIterator< TheoryUF::NotifyClass > eqc_iter2( rep2, &((TheoryUF*)d_th)->d_equalityEngine );
  //  while( !eqc_iter2.isFinished() ){
  //    std::cout << *eqc_iter2 << " ";
  //    eqc_iter2++;
  //  }
  //  std::cout << std::endl;
  //}
}

int InstantiatorTheoryUf::process( Node f, int effort ){
  Debug("quant-uf") << "UF: Try to solve (" << effort << ") for " << f << "... " << std::endl;
  Debug("quant-uf-alg") << std::endl;
  return InstStrategy::STATUS_UNKNOWN;
}

void InstantiatorTheoryUf::calculateEIndLitCandidates( Node t, Node s, Node f, bool isEq ){
  int ind = isEq ? 0 : 1;
  if( d_litMatchCandidates[ind].find( t )==d_litMatchCandidates[ind].end() ||
      d_litMatchCandidates[ind][t].find( s )==d_litMatchCandidates[ind][t].end() ){
    Debug("quant-uf-ematch") << "Calc Eind lit candidates " << t << (isEq ? " = " : " != " ) << s << std::endl;
    if( !isEq ){
      Assert( t.getAttribute(InstConstantAttribute())==f );
      if( s.getAttribute(InstConstantAttribute())==f  ){
        //a disequality between two triggers
        //for each equivalence class E
        EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
        while( !eqc_iter.isFinished() ){
          Node ct = getRepresentative( *eqc_iter );
          ++eqc_iter;
          Assert( ct==getRepresentative( ct ) );
          if( ct.getType()==t.getType() && !ct.hasAttribute(InstConstantAttribute()) ){
            calculateEIndLitCandidates( t, ct, f, true );
            if( !d_litMatchCandidates[0][t][ct].empty() ){
              //for each equivalence class disequal from E
              for( int j=0; j<(int)d_dmap[ct].size(); j++ ){
                Node cs = d_dmap[ct][j];
                Assert( cs==getRepresentative( cs ) );
                if( !cs.hasAttribute(InstConstantAttribute()) ){
                  calculateEIndLitCandidates( s, cs, f, true );
                  if( !d_litMatchCandidates[0][s][cs].empty() ){
                    // could be the case that t matches ct and s matches cs
                    Kind knd = ct.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
                    Node ceq = NodeManager::currentNM()->mkNode( knd, ct, cs );
                    d_litMatchCandidates[1][t][s].push_back( ceq );
                  }
                }
              }
            }
          }
        }
      }else{
        //a disequality between a trigger and ground term
        Node c = getRepresentative( s );
        //match against all equivalence classes disequal from c
        for( int j=0; j<(int)d_dmap[c].size(); j++ ){
          Node ct = d_dmap[c][j];
          Assert( ct==getRepresentative( ct ) );
          if( !ct.hasAttribute(InstConstantAttribute()) ){
            calculateEIndLitCandidates( t, ct, f, true );  
            if( !d_litMatchCandidates[0][t][ct].empty() ){
              //it could be the case that t matches with ct
              d_litMatchCandidates[1][t][s].push_back( ct );
            }
          }
        }
      }
    }else{
      if( s.getAttribute(InstConstantAttribute())==f ){
        //equality between two triggers
        //for each equivalence class
        EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
        while( !eqc_iter.isFinished() ){
          Node c = getRepresentative( *eqc_iter );
          ++eqc_iter;
          if( c.getType()==t.getType() && !c.hasAttribute(InstConstantAttribute()) ){
            calculateEIndLitCandidates( t, c, f, true );
            if( !d_litMatchCandidates[0][t][c].empty() ){
              calculateEIndLitCandidates( s, c, f, true );
              if( !d_litMatchCandidates[0][s][c].empty() ){
                // both have a chance to match in the equivalence class, thus i1 = i2 may be forced by c
                d_litMatchCandidates[0][t][s].push_back( c );
              }
            }
          }
        }
      }else{
        Node c = getRepresentative( s );
        if( d_litMatchCandidates[0].find( t )==d_litMatchCandidates[0].end() ||
            d_litMatchCandidates[0][t].find( c )==d_litMatchCandidates[0][t].end() ){
          if( t.getKind()==INST_CONSTANT ){
            //there is no need in scanning the equivalence class of c 
            c = getInternalRepresentative( c );
            if( !c.hasAttribute(InstConstantAttribute()) ){
              d_litMatchCandidates[0][t][c].push_back( c );
            }
          }else{
            EqClassIterator< TheoryUF::NotifyClass > eqc_iter( c, &((TheoryUF*)d_th)->d_equalityEngine );
            while( !eqc_iter.isFinished() ){
              Node ca = *eqc_iter;
              if( !ca.hasAttribute(InstConstantAttribute()) ){
                if( ca.getKind()==APPLY_UF && ca.getOperator()==t.getOperator() ){
                  d_litMatchCandidates[0][t][c].push_back( ca );
                }
              }
              ++eqc_iter;
            }
          }
        }
        if( s!=c ){
          d_litMatchCandidates[0][t][s].insert( d_litMatchCandidates[0][t][s].begin(),
                                                d_litMatchCandidates[0][t][c].begin(),
                                                d_litMatchCandidates[0][t][c].end() );
        }
      }
    }
    //std::random_shuffle( d_litMatchCandidates[ind][t][s].begin(), d_litMatchCandidates[ind][t][s].end() );
  }
}

void InstantiatorTheoryUf::getObligations( Node f, std::vector< Node >& obs ){
  NodeLists::iterator ob_i = d_obligations.find( f );
  if( ob_i!=d_obligations.end() ){
    NodeList* ob = (*ob_i).second;
    //std::cout  << "Generate trigger for literal matching..." << std::endl;
    //this is matching at the literal level : use obligations of f as pattern terms
    for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
      obs.push_back( *it );
    }
    d_ob_changed[f] = false;
  }
}

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


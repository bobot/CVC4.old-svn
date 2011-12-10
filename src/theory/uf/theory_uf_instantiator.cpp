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

void InstStrategyCheckCESolved::resetInstantiationRound(){

}

bool InstStrategyCheckCESolved::process( int effort ){
  d_instEngine->getMatchGenerator( d_f )->d_baseMatch = InstMatch( d_f, d_instEngine );
  //check if any instantiation constants are solved for
  for( int j = 0; j<(int)d_instEngine->getNumInstantiationConstants( d_f ); j++ ){
    Node i = d_instEngine->getInstantiationConstant( d_f, j );
    Node rep = d_th->getConcreteRep( i );
    if( rep!=Node::null() ){
      d_instEngine->getMatchGenerator( d_f )->d_baseMatch.setMatch( i, rep );
    }
  }
  //check if f is counterexample-solved
  if( d_instEngine->getMatchGenerator( d_f )->d_baseMatch.isComplete() ){
    if( d_instEngine->addInstantiation( &d_instEngine->getMatchGenerator( d_f )->d_baseMatch ) ){
      ++(d_th->d_statistics.d_instantiations);
      ++(d_th->d_statistics.d_instantiations_ce_solved);
    }
  }  
  return false;
}

void InstStrategyLitMatch::resetInstantiationRound(){
  
}

bool InstStrategyLitMatch::process( int effort ){
  //std::cout  << "Generate trigger for literal matching..." << std::endl;
  //this is matching at the literal level : use obligations of f as pattern terms
  std::vector< Node > pats;
  d_th->getObligations( d_f, pats );
  if( !pats.empty() ){
    d_instEngine->getMatchGenerator( d_f )->initializePatternTerms( pats );
    if( d_instEngine->getMatchGenerator( d_f )->addInstantiation() ){
      ++(d_th->d_statistics.d_instantiations);
      ++(d_th->d_statistics.d_instantiations_e_induced);
    }
  }
  return false;
}

void InstStrategyUserPatterns::resetInstantiationRound(){
  
}

bool InstStrategyUserPatterns::process( int effort ){
  for( int i=0; i<(int)d_instEngine->getMatchGenerator( d_f )->getNumUserPatterns(); i++ ){
    if( d_instEngine->getMatchGenerator( d_f )->addInstantiation( i ) ){
      ++(d_th->d_statistics.d_instantiations);
      ++(d_th->d_statistics.d_instantiations_user_pattern);
    }
  }
  return false;
}

void InstStrategyAutoGenTriggers::resetInstantiationRound(){
  
}

bool InstStrategyAutoGenTriggers::process( int effort ){
  static int triggerThresh = 3;   //try at most 3 triggers
  d_instEngine->getMatchGenerator( d_f )->initializePatternTerms();
  if( d_instEngine->getMatchGenerator( d_f )->addInstantiation( -1, triggerThresh ) ){
    ++(d_th->d_statistics.d_instantiations);
  }
  return false;
}

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie, th ),
d_obligations( c ),
d_terms_full( c ),
d_terms( c ),
d_disequality( c )
{
  registerTerm( ((TheoryUF*)d_th)->d_true );
  registerTerm( ((TheoryUF*)d_th)->d_false );
  Node eq = NodeManager::currentNM()->mkNode( IFF, ((TheoryUF*)d_th)->d_true, ((TheoryUF*)d_th)->d_false );
  d_disequality.push_back( eq );
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

void InstantiatorTheoryUf::registerTerm( Node n, bool isTop ){
  if( d_terms_full.find( n )==d_terms_full.end() ){
    if( isTop ){
      d_terms[n] = true;
    }
    d_terms_full[n] = true;

    if( n.getKind()==INST_CONSTANT ){
      d_instEngine->d_ic_active[n] = true;
    }
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerTerm( n[i], false );
    }
  }
  if( n.hasAttribute(InstConstantAttribute()) ){
    setHasConstraintsFrom( n.getAttribute(InstConstantAttribute()) );
  }
}

void InstantiatorTheoryUf::resetInstantiationRound()
{
  InstMatchGenerator::d_itu = this;
  InstMatchGenerator::resetAssigned();
  d_status = STATUS_UNFINISHED; 
  d_matches.clear();
  d_anyMatches.clear();
  d_eq_dep.clear();
  d_litMatchCandidates[0].clear();
  d_litMatchCandidates[1].clear();
  d_concrete_reps.clear();
  //get representatives that will be used
  EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
  while( !eqc_iter.isFinished() ){
    EqClassIterator< TheoryUF::NotifyClass > eqc_iter2( *eqc_iter, &((TheoryUF*)d_th)->d_equalityEngine );
    Node rep;
    while( !eqc_iter2.isFinished() ){
      if( rep==Node::null() ){
        rep = *eqc_iter2;
      }else{
        bool useRep = false;
        if( rep.hasAttribute(InstConstantAttribute()) ){
          if( !(*eqc_iter2).hasAttribute(InstConstantAttribute()) ){
            useRep = true;
          }
        }else{
          if( rep.hasAttribute(InstLevelAttribute()) ){
            if( !(*eqc_iter2).hasAttribute(InstLevelAttribute()) || 
                (*eqc_iter2).getAttribute(InstLevelAttribute())<rep.getAttribute(InstLevelAttribute()) ){
              useRep = true;
            }
          }
        }
        if( useRep ){
          rep = *eqc_iter2;
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
    for( int i=0; i<(int)it->second.size(); i++ ){
      if( i>0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << it->second[i];
      if(d_terms_full.find( it->second[i] )==d_terms_full.end()){
        Debug( c ) << " (inactive)";
      }
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
  if( d_reps.find( rep )==d_reps.end() ){
    return rep;
  }else{
    return d_reps[ rep ];
  }
}

void InstantiatorTheoryUf::process( Node f, int effort ){
  Debug("quant-uf") << "UF: Try to solve (" << effort << ") for " << f << "... " << std::endl;
  if( effort>5 ){
    if( effort==6 ){
      Debug("quant-uf") << "Add guessed instantiation" << std::endl;
      InstMatch m( f, d_instEngine );
      d_instEngine->addInstantiation( &m );
      ++(d_statistics.d_instantiations);
    }
    d_quantStatus = STATUS_UNKNOWN;
  }else if( effort==0 ){
    d_instEngine->getMatchGenerator( f )->d_baseMatch = InstMatch( f, d_instEngine );
    //check if any instantiation constants are solved for
    for( int j = 0; j<(int)d_instEngine->getNumInstantiationConstants( f ); j++ ){
      Node i = d_instEngine->getInstantiationConstant( f, j );
      if( d_terms_full.find( i )!=d_terms_full.end() ){
#if 0
        Node rep = getConcreteRep( i );
        if( rep!=Node::null() ){
#else
        Node rep = getInternalRepresentative( i );
        if( !rep.hasAttribute(InstConstantAttribute()) ){
#endif
          d_instEngine->getMatchGenerator( f )->d_baseMatch.setMatch( i, rep );
        }
      }
    }
    //check if f is counterexample-solved
    if( d_instEngine->getMatchGenerator( f )->d_baseMatch.isComplete() ){
      if( d_instEngine->addInstantiation( &d_instEngine->getMatchGenerator( f )->d_baseMatch ) ){
        ++(d_statistics.d_instantiations);
        ++(d_statistics.d_instantiations_ce_solved);
      }
    }
  }else if( effort<=3 ){
    //reset the quantifier match generator
    InstMatchGenerator::d_splitThreshold = effort==1 ? 0 : ( effort==2 ? 1 : 2 );
    InstMatchGenerator::d_useSplitThreshold = true;
    d_instEngine->getMatchGenerator( f )->resetInstantiationRound();
    //this is matching at the literal level : use obligations of f as pattern terms
    //std::cout  << "Generate trigger for literal matching..." << std::endl;
    std::vector< Node > pats;
    getObligations( f, pats );
    if( !pats.empty() ){
      d_instEngine->getMatchGenerator( f )->initializePatternTerms( pats );
      static int triggerThresh = effort==1 ? 1 : 2;
      if( d_instEngine->getMatchGenerator( f )->addInstantiation( -1, triggerThresh ) ){
        ++(d_statistics.d_instantiations);
        ++(d_statistics.d_instantiations_e_induced);
      }
    }
    //std::cout << "done" << std::endl;
    //std::cout << "Try user-provided patterns..." << std::endl;
    for( int i=0; i<(int)d_instEngine->getMatchGenerator( f )->getNumUserPatterns(); i++ ){
      if( d_instEngine->getMatchGenerator( f )->addInstantiation( i ) ){
        ++(d_statistics.d_instantiations);
        ++(d_statistics.d_instantiations_user_pattern);
      }
    }
    //std::cout << "done" << std::endl;
    d_instEngine->getMatchGenerator( f )->resetInstantiationRound();
    //std::cout  << "Try auto-generated triggers..." << std::endl;
    static int triggerThresh = 3;   //try at most 3 triggers
    d_instEngine->getMatchGenerator( f )->initializePatternTerms();
    if( d_instEngine->getMatchGenerator( f )->addInstantiation( -1, triggerThresh ) ){
      ++(d_statistics.d_instantiations);
    }
    //std::cout << "done" << std::endl;
  }else{
#if 1
    if( d_guessed.find( f )==d_guessed.end() ){
      d_guessed[f] = true;
      Debug("quant-uf-alg") << "Add guessed instantiation" << std::endl;
      InstMatch m( f, d_instEngine );
      d_instEngine->addInstantiation( &m );
      ++(d_statistics.d_instantiations);
      ++(d_statistics.d_instantiations_guess);
    }
#endif
    d_quantStatus = STATUS_UNKNOWN;
  }


  Debug("quant-uf-alg") << std::endl;
}

void InstantiatorTheoryUf::calculateMatches( Node f, Node t ){
  Assert( t.getAttribute(InstConstantAttribute())==f );
  if( d_matches.find( t )==d_matches.end() ){
    d_matches[t].clear();
    d_anyMatches[t].clear();
    for( BoolMap::const_iterator it = d_terms_full.begin(); it!=d_terms_full.end(); ++it ){
      Node c = (*it).first;
      if( t!=c && t.getType()==c.getType() ){
        calculateEqDep( t, c, f );
        if( d_eq_dep[t][c] ){
          if( !c.hasAttribute(InstConstantAttribute()) ){
            d_matches[t].push_back( c );
          }else{
            d_anyMatches[t].push_back( c );
          }
        }
      }
    }
  }
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
#if 0
            Node cc = getConcreteRep( c );
            Assert( cc!=Node::null() );
            d_litMatchCandidates[0][t][c].push_back( cc );
#else
            c = getInternalRepresentative( c );
            if( !c.hasAttribute(InstConstantAttribute()) ){
              d_litMatchCandidates[0][t][c].push_back( c );
            }
#endif
          }else{
            EqClassIterator< TheoryUF::NotifyClass > eqc_iter( c, &((TheoryUF*)d_th)->d_equalityEngine );
            while( !eqc_iter.isFinished() ){
              Node ca = *eqc_iter;
              if( !ca.hasAttribute(InstConstantAttribute()) ){
                calculateEqDep( t, ca, f );
                if( d_eq_dep[t][ca] ){
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
  }
}

void InstantiatorTheoryUf::calculateEqDep( Node i, Node c, Node f ){
  if( d_eq_dep.find( i )==d_eq_dep.end() ||
      d_eq_dep[i].find( c )==d_eq_dep[i].end() ){
    if( i.getKind()==INST_CONSTANT ){
      d_eq_dep[i][c] = true;
    }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
      d_eq_dep[i][c] = false;
    }else{
      Assert( i.getKind()==APPLY_UF && c.getKind()==APPLY_UF );
      Assert( i.getNumChildren()==c.getNumChildren() );
      d_eq_dep[i][c] = true;
      for( int j=0; j<(int)c.getNumChildren(); j++ ){
        if( areDisequal( i[j], c[j] ) ){
          d_eq_dep[i][c] = false;
          break;
        }
      }
    }
  }
}

Node InstantiatorTheoryUf::getConcreteRep( Node n ){
  n = getRepresentative( n );
  if( !n.hasAttribute(InstConstantAttribute()) ){
    return n;
  }else if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) ){
    Node rep;
    if( d_concrete_reps.find( n )==d_concrete_reps.end() ){
      d_concrete_reps[n] = Node::null();
      EqClassIterator< TheoryUF::NotifyClass > eqc_iter( n, &((TheoryUF*)d_th)->d_equalityEngine );
      while( !eqc_iter.isFinished() ){
        if( !(*eqc_iter).hasAttribute(InstConstantAttribute()) ){
          d_concrete_reps[n] = *eqc_iter;
          break;
        }
        ++eqc_iter;
      }
    }
    return d_concrete_reps[n];
  }else{
    return Node::null();
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
  }
}

InstantiatorTheoryUf::Statistics::Statistics():
  d_instantiations("InstantiatorTheoryUf::Total Instantiations", 0),
  d_instantiations_ce_solved("InstantiatorTheoryUf::CE-Solved Instantiations", 0),
  d_instantiations_e_induced("InstantiatorTheoryUf::E-Induced Instantiations", 0),
  d_instantiations_user_pattern("InstantiatorTheoryUf::User pattern Instantiations", 0),
  d_instantiations_guess("InstantiatorTheoryUf::Guess Instantiations", 0),
  d_splits("InstantiatorTheoryUf::Splits", 0)
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


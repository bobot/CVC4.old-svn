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


//SubTermNode::SubTermNode( context::Context* c, Node n ) :
//d_parents( c ),
//d_obligations( c ),
//d_node( n ){
//  
//}
//
//void SubTermNode::addParent( SubTermNode* g ) { 
//  for( GmnList::const_iterator it = d_parents.begin(); it!=d_parents.end(); ++it ){
//    if( *it == g ){
//      return;
//    }
//  }
//  d_parents.push_back( g ); 
//}
//
//void SubTermNode::addObligation( Node n ) { 
//  for( ObList::const_iterator it = d_obligations.begin(); it!=d_obligations.end(); ++it ){
//    if( *it == n ){
//      return;
//    }
//  }
//  d_obligations.push_back( n ); 
//}

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie, th ),
//d_subterms( c ),
//d_subterm_size( c ),
d_obligations( c ),
d_ob_pol( c ),
d_ob_reqPol( c ),
d_terms_full( c ),
d_terms( c ),
d_disequality( c )
{
  registerTerm( ((TheoryUF*)d_th)->d_true );
  registerTerm( ((TheoryUF*)d_th)->d_false );
  Node eq = NodeManager::currentNM()->mkNode( IFF, ((TheoryUF*)d_th)->d_true, ((TheoryUF*)d_th)->d_false );
  d_disequality.push_back( eq );
}

void InstantiatorTheoryUf::check( Node assertion )
{
  Debug("quant-uf-assert") << "InstantiatorTheoryUf::check: " << assertion << std::endl;
  switch (assertion.getKind()) {
  case kind::EQUAL:
    assertEqual( assertion[0], assertion[1], 
                 d_instEngine->d_phase_reqs.find( assertion )!=d_instEngine->d_phase_reqs.end()  );
    break;
  case kind::APPLY_UF:
    assertEqual( assertion, ((TheoryUF*)d_th)->d_true, 
                 d_instEngine->d_phase_reqs.find( assertion )!=d_instEngine->d_phase_reqs.end()  );
    break;
  case kind::NOT:
    assertEqual( assertion[0], ((TheoryUF*)d_th)->d_false, 
                 d_instEngine->d_phase_reqs.find( assertion[0] )!=d_instEngine->d_phase_reqs.end() );
    break;
  default:
    Unreachable();
  }
}

void InstantiatorTheoryUf::assertEqual( Node a, Node b, bool reqPol )
{
  if( a.hasAttribute(InstConstantAttribute()) || 
      b.hasAttribute(InstConstantAttribute()) ){
    //add to obligation list
    Node formula;
    Node f;
    bool isEq = true;
    if( a.hasAttribute(InstConstantAttribute()) ){
      f = a.getAttribute(InstConstantAttribute());
      Kind knd = a.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
      formula = NodeManager::currentNM()->mkNode( knd, a, b );
    }else if( b.hasAttribute(InstConstantAttribute()) ){
      f = b.getAttribute(InstConstantAttribute());
      //swap sides
      Kind knd = a.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
      formula = NodeManager::currentNM()->mkNode( knd, b, a );
    }
    //swap sides for a disequality
    if( a.getKind()==EQUAL || a.getKind()==IFF ){
      if( !a[0].hasAttribute(InstConstantAttribute()) ){
        Assert( a[1].hasAttribute(InstConstantAttribute()) );
        a = NodeManager::currentNM()->mkNode( a.getKind(), a[1], a[0] );
        InstConstantAttribute icai;
        a.setAttribute(icai,f);
      }
      isEq = false;
      formula = a;
    }
    Assert( f!=Node::null() );
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
      Assert( *it != formula );
    }
    ob->push_back( formula );
    d_ob_pol[ formula ] = isEq;
    d_ob_reqPol[ formula ] = reqPol;
    //this theory has constraints from f
    setHasConstraintsFrom( f );
  }
  if( a.getKind()==EQUAL || a.getKind()==IFF ){
    Assert( b==((TheoryUF*)d_th)->d_false );
    d_disequality.push_back( a );
    registerTerm( a[0] );
    registerTerm( a[1] );
  }else{
    Assert( b.getKind()!=EQUAL && b.getKind()!=IFF );
    registerTerm( a );
    registerTerm( b );
  }
}

void InstantiatorTheoryUf::registerTerm( Node n, bool isTop )
{
  if( !n.hasAttribute(InstLevelAttribute()) ){
    InstLevelAttribute ila;
    n.setAttribute(ila,0);
  }
  if( d_terms_full.find( n )==d_terms_full.end() ){
    d_instEngine->registerTerm( n );
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
}

//void InstantiatorTheoryUf::buildSubTerms( Node n )
//{
//  SubTermMap::iterator it = d_subterms.find( n );
//  if( it==d_subterms.end() ){
//    SubTermNode* g = getSubTerm( n );
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      if( n[i].hasAttribute(InstConstantAttribute()) ){
//        buildSubTerms( n[i] );
//        getSubTerm( n[i] )->addParent( g );
//      }
//    }
//  }
//}
//
//SubTermNode* InstantiatorTheoryUf::getSubTerm( Node n )
//{
//  SubTermMap::iterator gm_i = d_subterms.find( n );
//  if( gm_i == d_subterms.end() ) {
//    SubTermNode* g = new SubTermNode( d_th->getContext(), n );
//    d_subterms[n] = g;
//    //add to count for the counterexample of its quantifier
//    for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
//          it !=d_inst_constants.end(); ++it ){
//      if( hasInstantiationConstantsFrom( n, it->first ) ){
//        IntMap::iterator gms_i = d_subterm_size.find( it->first );
//        if( gms_i==d_subterm_size.end() ){
//          d_subterm_size[ it->first ] = 0;
//        }
//        d_subterm_size[ it->first ] = d_subterm_size[ it->first ] + 1;
//      }
//    }
//    return g;
//  }else{
//    return (*gm_i).second;
//  }
//}

//void InstantiatorTheoryUf::setActiveInstConstants( Node n ){
//  Assert( n.hasAttribute(InstConstantAttribute()) );
//  if( n.getKind()==INST_CONSTANT ){
//    d_active_ic[ n ] = true;
//  }else{
//    if( d_inst_terms.find( n )==d_inst_terms.end() ){
//      for( int i=0; i<(int)n.getNumChildren(); i++ ){
//        if( n[i].hasAttribute(InstConstantAttribute()) ){
//          setActiveInstConstants( n[i] );
//        }
//      }
//    }
//  }
//}

void InstantiatorTheoryUf::resetInstantiation()
{
  InstMatchGenerator::d_itu = this;
  InstMatchGenerator::resetAssigned();
  d_status = STATUS_UNFINISHED; 
  d_baseMatch.clear();
  d_matches.clear();
  d_anyMatches.clear();
  d_eq_dep.clear();
  d_litMatchCandidates[0].clear();
  d_litMatchCandidates[1].clear();
  //build equivalence classes
  d_emap.clear();
  for( BoolMap::iterator it = d_terms.begin(); it!=d_terms.end(); ++it ){
    Node n = (*it).first;
    if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) ){
      Node r = ((TheoryUF*)d_th)->d_equalityEngine.getRepresentative( n );
      Assert( std::find( d_emap[r].begin(), d_emap[r].end(), n )==d_emap[r].end() );
      d_emap[r].push_back( n );
    }
  }
  //set representatives
  std::map< Node, Node > repReplace;
  for( std::map< Node, std::vector< Node > >::iterator it = d_emap.begin(); it!=d_emap.end(); ++it ){
    Node r = it->first;
    if( r.hasAttribute(InstConstantAttribute()) ){
      //see if there is concrete ground term, make that representative
      for( int i=0; i<(int)it->second.size(); i++ ){
        if( !it->second[i].hasAttribute(InstConstantAttribute()) ){
          repReplace[ r ] = it->second[i];
        }
      }
    }
  }
  for( std::map< Node, Node >::iterator it = repReplace.begin(); it!=repReplace.end(); ++it ){
    Assert( d_emap[ it->second ].empty() );
    d_emap[ it->second ].clear();
    d_emap[ it->second ].insert( d_emap[ it->second ].begin(), d_emap[ it->first ].begin(), d_emap[ it->first ].end() );
    d_emap.erase( it->first );
  }
  d_reps.clear();
  for( std::map< Node, std::vector< Node > >::iterator it = d_emap.begin(); it!=d_emap.end(); ++it ){
    for( int i=0; i<(int)it->second.size(); i++ ){
      d_reps[ it->second[i] ] = it->first;
    }
  }
  //build disequality lists
  d_dmap.clear();
  for( NodeList::const_iterator it = d_disequality.begin(); it!=d_disequality.end(); ++it ){
    Node n = (*it);
    Node r1 = getRepresentative( n[0] );
    //must be added to emap
    if( d_emap.find( r1 )==d_emap.end() ){
      Assert( r1==n[0] );
      d_emap[ r1 ].push_back( r1 );
    }
    Node r2 = getRepresentative( n[1] );
    //must be added to emap
    if( d_emap.find( r2 )==d_emap.end() ){
      Assert( r2==n[1] );
      d_emap[ r2 ].push_back( r2 );
    }
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
  Debug( c ) << "Equivalence classes:" << std::endl;
  int counter = 1;
  for( std::map< Node, std::vector< Node > >::iterator it = d_emap.begin(); it!=d_emap.end(); ++it ){
    Debug( c ) << "E" << counter << ": { ";
    for( int i = 0; i<(int)it->second.size(); i++ ){
      if( i!=0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << it->second[i];
    }
    Debug( c ) << " }";
    Debug( c ) << ", disequal : ";
    std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( it->first );
    if( itd!=d_dmap.end() ){
      for( int i = 0; i<(int)itd->second.size(); i++ ){
        if( i!=0 ){
          Debug( c ) << ", ";
        }
        int counter2 = 1;
        std::map< Node, std::vector< Node > >::iterator it4 = d_emap.begin();
        while( it4!=d_emap.end() && !areEqual( it4->first, itd->second[i] ) ){
          ++it4;
          ++counter2;
        }
        if( it4==d_emap.end() ){
          Debug( c ) << getRepresentative( itd->second[i] );
        }else{
          Debug( c ) << "E" << counter2;
        }
      }
    }
    ++counter;
    //Debug( c ) << ", rep = " << it->first;
    Debug( c ) << std::endl;
  }
  Debug( c ) << std::endl;

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
        Debug( c ) << "      " << ( !d_ob_pol[*it] ? "NOT " : "" );
        Debug( c ) << *it;
        Debug( c ) << " " << ( d_ob_reqPol[ *it ] ? "(REQ)" : "" );
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
  a = getRepresentative( a );
  b = getRepresentative( b );
  std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( a );
  if( itd!=d_dmap.end() ){
    for( int i=0; i<(int)itd->second.size(); i++ ){
      if( getRepresentative( itd->second[i] )==b ){
        return true;
      }
    }
  }
  return false;
}

Node InstantiatorTheoryUf::getRepresentative( Node a ){
  if( d_reps.find( a )!=d_reps.end() ){
    return d_reps[a];
  }else{
    return a;
  }
}

void InstantiatorTheoryUf::process( Node f, int effort ){
  Debug("quant-uf") << "UF: Try to solve (" << effort << ") for " << f << "... " << std::endl;
  if( effort>5 ){
    if( effort==6 && !d_unmatched[f] ){
      Debug("quant-uf") << "Add guessed instantiation" << std::endl;
      InstMatch m( f, d_instEngine );
      d_instEngine->addInstantiation( &m );
      ++(d_statistics.d_instantiations);
    }
    d_quantStatus = STATUS_UNKNOWN;
  }else if( effort==0 ){
    //calculate base matches
    d_baseMatch[f] = InstMatch( f, d_instEngine );
    //check if any instantiation constants are solved for
    for( int j = 0; j<(int)d_instEngine->d_inst_constants[f].size(); j++ ){
      Node i = d_instEngine->d_inst_constants[f][j];
      if( d_instEngine->getTheoryEngine()->theoryOf( i )==getTheory() ){
        if( d_terms_full.find( i )!=d_terms_full.end() ){
          Node rep = getRepresentative( i );
          if( !rep.hasAttribute(InstConstantAttribute()) ){
            d_baseMatch[f].setMatch( i, rep );
          }
        }//else{
          //d_baseMatch[f].setMatch( i, NodeManager::currentNM()->mkVar( i.getType() ) );
        //}
      }
    }
    //check if f is counterexample-solved
    if( d_baseMatch[f].isComplete() ){
      if( d_instEngine->addInstantiation( &d_baseMatch[f] ) ){
        ++(d_statistics.d_instantiations);
        ++(d_statistics.d_instantiations_ce_solved);
      }
    }
  }else{
    NodeLists::iterator ob_i = d_obligations.find( f );
    if( ob_i!=d_obligations.end() ){
      NodeList* ob = (*ob_i).second;
      if( effort==1 ){
        InstMatchGenerator::d_splitThreshold = 0;
        // for each literal asserted about the negation of the body of f
        d_mergeIter[ f ] = InstMatchGenerator::mkInstMatchGenerator( false );
        for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
          Node lit = (*it);
          if( d_ob_reqPol[lit] ){
            d_mergeIter[ f ]->d_children.push_back( InstMatchGenerator::mkCombineInstMatchGenerator( lit[0], lit[1], d_ob_pol[lit] ) );
          }else{
            //this literal does not require this polarity, produce matches for either polarity
            InstMatchGenerator* it = InstMatchGenerator::mkInstMatchGenerator( true );
            it->d_children.push_back( InstMatchGenerator::mkCombineInstMatchGenerator( lit[0], lit[1], d_ob_pol[lit] ) );
            it->d_children.push_back( InstMatchGenerator::mkCombineInstMatchGenerator( lit[0], lit[1], !d_ob_pol[lit] ) );
            d_mergeIter[ f ]->d_children.push_back( it );
          }
        }
        while( d_mergeIter[ f ]->getNextMatch() ){
          // f is E-induced
          InstMatch temp( d_mergeIter[ f ]->getCurrent() );
          temp.add( d_baseMatch[f] );
          if( d_instEngine->addInstantiation( &temp ) ){
            ++(d_statistics.d_instantiations);
            ++(d_statistics.d_instantiations_e_induced);
            break;
          }
        }
      }else if( effort<5 ){
        d_mergeIter[ f ]->clearMatches();
        Debug("quant-uf-alg") << "Here is the merge iterator: " << std::endl;
        d_mergeIter[ f ]->debugPrint( "quant-uf-alg", 0 );
        InstMatchGenerator::d_splitThreshold = effort==2 ? 1 : 2;
        InstMatchGenerator::d_useSplitThreshold = effort<4;
        while( d_mergeIter[ f ]->getNextMatch() ){
          // f is (conditionally) E-induced
          InstMatch temp( d_mergeIter[ f ]->getCurrent() );
          temp.add( d_baseMatch[f] );
          if( d_instEngine->addInstantiation( &temp, true ) ){
            ++(d_statistics.d_instantiations);
            Debug("quant-uf") << "Added this inst match: " << std::endl;
            temp.debugPrint( "quant-uf" );
            break;
          }
        }
      }else if( effort==5 ){
        Debug("quant-uf-alg") << "Here is the merge iterator: " << std::endl;
        d_mergeIter[ f ]->debugPrint( "quant-uf-alg", 0 );
        //check if all literals are matchable
        //resolve matches on the literal level
        calculateMatchable( f );
        if( !d_unmatched[f] ){
          std::map< InstMatchGenerator*, InstMatchGenerator* > index;
          std::vector< InstMatchGenerator* > unmerged;
          std::vector< InstMatchGenerator* > cover;
          d_mergeIter[ f ]->collectUnmerged( unmerged, cover );
          Debug("quant-uf-alg") << "Here are the unmerged points: " << std::endl;
          for( int i=0; i<(int)unmerged.size(); i++ ){
            unmerged[i]->debugPrint( "quant-uf-alg", 1, false );
          }
          Debug("quant-uf-alg") << "Here are the covering points: " << std::endl;
          for( int i=0; i<(int)cover.size(); i++ ){
            cover[i]->debugPrint( "quant-uf-alg", 1, false );
            cover[i]->d_mg.debugPrint( "quant-uf-alg" );
          }
          bool success = false;
          for( int i=0; i<(int)cover.size(); i++ ){
            //see if we can construct any complete instantiations 
            cover[i]->reset();
            while( !success && cover[i]->getNextMatch() ){
              if( cover[i]->getCurrent()->isComplete( &d_baseMatch[f] ) ){
                InstMatch temp( cover[i]->getCurrent() );
                temp.add( d_baseMatch[f] );
                if( d_instEngine->addInstantiation( &temp, true ) ){
                  ++(d_statistics.d_instantiations);
                  success = true;
                }
              }
            }
          }
          if( !success ){
            std::vector< std::pair< Node, Node > > splits;
            std::vector< std::pair< Node, Node > > matchFails;
            for( int i=0; i<(int)unmerged.size(); i++ ){
              //process each unmerged point
              //make more children for this
              resolveLiteralMatches( unmerged[i]->d_t, unmerged[i]->d_s, f );
            }
          }
        }
      }
    }
  }



      //  calculateEIndLitCandidates( lit[0], lit[1], f, d_ob_pol[lit] );
      //  int ind = d_ob_pol[lit] ? 0 : 1;
      //  if( !d_litMatchCandidates[ind][lit[0]][lit[1]].empty() ){
      //    Debug("quant-uf-alg") << "-> Literal is literal-matched." << std::endl;
      //  }else{
      //    if( effort<4 ){
      //      Debug("quant-uf-alg") << "-> Literal is not literal-matched." << std::endl;
      //      process = false;
      //      break;
      //    }else{
      //      bool matchable = true;
      //      bool unmatched = false;
      //      for( int i=0; i<2; i++ ){
      //        if( lit[i].hasAttribute(InstConstantAttribute()) ){
      //          calculateMatches( f, lit[i] );
      //          if( d_matches[ lit[i] ].empty() ){
      //            matchable = false;
      //            if( d_anyMatches[ lit[i] ].empty() ){
      //              unmatched = true;
      //              break;
      //            }
      //          }
      //        }
      //      }
      //      if( matchable ){
      //        litMatchFails.push_back( lit );
      //        Debug("quant-uf-alg") << "-> Literal is matchable." << std::endl;
      //      }else if( unmatched ){
      //        process = false;
      //        Debug("quant-uf-alg") << "-> Literal is unmatched." << std::endl;
      //      }else{
      //        Debug("quant-uf-alg") << "-> Literal is not matchable." << std::endl;
      //      }
      //    }
      //  }
      //}
      //if( process ){
      //  bool addedLemma = false;
      //  if( litMatchFails.empty() ){
      //    ////create iterators over the candidate matches
      //    //std::vector< int > litMatchCandidateIter;
      //    //litMatchCandidateIter.resize( ob->size(), 1 );
      //    MergeInstMatchGenerator mi;
      //    for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
      //      Node lit = (*it);
      //      mi.d_children.push_back( CombineInstMatchGenerator( lit[0], lit[1], d_ob_pol[lit], f ) );
      //    }

  Debug("quant-uf-alg") << std::endl;
}

void InstantiatorTheoryUf::calculateMatchable( Node f ){
  NodeLists::iterator ob_i = d_obligations.find( f );
  if( ob_i!=d_obligations.end() ){
    NodeList* ob = (*ob_i).second;
    d_matchable[f] = true;
    d_unmatched[f] = false;
    for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
      Node lit = (*it);
      Node t = lit[0];
      Node s = lit[1];
      int ind = d_ob_pol[lit] ? 0 : 1;
      Debug("quant-uf-alg") << "Process obligation " << ( !d_ob_pol[*it] ? "NOT " : "" );
      Debug("quant-uf-alg") << (*it) << std::endl;
      calculateEIndLitCandidates( t, s, f, d_ob_pol[lit] );
      if( !d_litMatchCandidates[ind][t][s].empty() ){
        Debug("quant-uf-alg") << "-> Literal is matched." << std::endl;
      }else{
        for( int i=0; i<2; i++ ){
          if( lit[i].hasAttribute(InstConstantAttribute()) ){
            calculateMatches( f, lit[i] );
            if( d_matches[ lit[i] ].empty() ){
              d_matchable[f] = false;
              if( d_anyMatches[ lit[i] ].empty() ){
                d_unmatched[f] = true;
                break;
              }
            }
          }
        }
        if( !d_matchable[f] ){
          if( d_unmatched[f] ){
            Debug("quant-uf-alg") << "-> Literal is unmatched." << std::endl;
          }else{
            Debug("quant-uf-alg") << "-> Literal is not matchable." << std::endl;
          }
        }
      }
    }
  }
}

bool InstantiatorTheoryUf::resolveLiteralMatches( Node t, Node s, Node f ){
  bool addedLemma = false;
  for( int i=0; i<(int)d_matches[t].size(); i++ ){
    Node mt = d_matches[t][i];
    if( s.getAttribute(InstConstantAttribute())==f ){
      for( int j=0; j<(int)d_matches[s].size(); j++ ){
        Node ms = d_matches[s][j];
        if( !areEqual( mt, ms ) && !areDisequal( mt, ms ) ){
          if( d_instEngine->addSplitEquality( mt, ms ) ){
            addedLemma = true;
          }
        }
      }
    }else{
      if( !areEqual( mt, s ) && !areDisequal( mt, s ) ){
        if( d_instEngine->addSplitEquality( mt, s ) ){
          addedLemma = true;
        }
      }
    }
  }
  return addedLemma;
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
        for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
          Node ct = (*it1).first;
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
        Assert( !s.hasAttribute(InstConstantAttribute()) );
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
        for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
          Node c = (*it1).first;
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
        Assert( !s.hasAttribute(InstConstantAttribute()) );
        Node c = getRepresentative( s );
        Assert( !c.hasAttribute(InstConstantAttribute()) );
        if( d_litMatchCandidates[0].find( t )==d_litMatchCandidates[0].end() ||
            d_litMatchCandidates[0][t].find( c )==d_litMatchCandidates[0][t].end() ){
          Debug("quant-uf-ematch") << "EIndMod " << t << " = " << c << std::endl;
          //equality between trigger and concrete ground term
          //build E-matches with terms in the same equivalence class
          if( t.getKind()==INST_CONSTANT || d_emap.find( c )==d_emap.end() ){
            //there is no need in scanning the equivalence class of c 
            //(either singleton or instantiation constant case)
            calculateEqDep( t, c, f );
            if( d_eq_dep[t][c] ){
              d_litMatchCandidates[0][t][c].push_back( c );
            }
          }else{
            for( int j=0; j<(int)d_emap[c].size(); j++ ){
              Node ca = d_emap[c][j];
              if( !ca.hasAttribute(InstConstantAttribute()) ){
                calculateEqDep( t, ca, f );
                if( d_eq_dep[t][ca] ){
                  d_litMatchCandidates[0][t][c].push_back( ca );
                }
              }
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

InstantiatorTheoryUf::Statistics::Statistics():
  d_instantiations("InstantiatorTheoryUf::Total Instantiations", 0),
  d_instantiations_ce_solved("InstantiatorTheoryUf::CE-Solved Instantiations", 0),
  d_instantiations_e_induced("InstantiatorTheoryUf::E-Induced Instantiations", 0),
  d_splits("InstantiatorTheoryUf::Splits", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_instantiations_ce_solved);
  StatisticsRegistry::registerStat(&d_instantiations_e_induced);
  StatisticsRegistry::registerStat(&d_splits);
}

InstantiatorTheoryUf::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_instantiations_ce_solved);
  StatisticsRegistry::unregisterStat(&d_instantiations_e_induced);
  StatisticsRegistry::unregisterStat(&d_splits);
}


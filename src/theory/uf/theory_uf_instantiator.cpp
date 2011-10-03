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
d_terms( c ),
d_terms_full( c ),
d_disequality( c )
//d_eind_done( c )
{
  registerTerm( ((TheoryUF*)d_th)->d_true );
  registerTerm( ((TheoryUF*)d_th)->d_false );
  Node eq = NodeManager::currentNM()->mkNode( IFF, ((TheoryUF*)d_th)->d_true, ((TheoryUF*)d_th)->d_false );
  d_disequality.push_back( eq );
}

void InstantiatorTheoryUf::check( Node assertion )
{
  switch (assertion.getKind()) {
  case kind::EQUAL:
    assertEqual( assertion[0], assertion[1] );
    break;
  case kind::APPLY_UF:
    assertEqual(assertion, ((TheoryUF*)d_th)->d_true );
    break;
  case kind::NOT:
    assertEqual( assertion[0], ((TheoryUF*)d_th)->d_false );
    break;
  default:
    Unreachable();
  }
}

void InstantiatorTheoryUf::assertEqual( Node a, Node b )
{
  Debug("inst-uf") << "InstantiatorTheoryUf::equal: " << a << " == " << b << std::endl;
  if( a.hasAttribute(InstConstantAttribute()) || 
      b.hasAttribute(InstConstantAttribute()) ){
    //add to obligation list
    Node formula;
    Node f;
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
      formula = NodeManager::currentNM()->mkNode( NOT, a );
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
    //DO_THIS: sub quantifiers?  add to their obligation list too?
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
  bool recurse = false;
  if( isTop ){
    if( d_terms.find( n )==d_terms.end() ){
      d_terms[n] = true;
      d_terms_full[n] = true;
      recurse = true;
    }
  }else{
    if( d_terms_full.find( n )==d_terms_full.end() ){
      d_terms_full[n] = true;
      recurse = true;
    }
  }
  if( recurse ){
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
  d_status = STATUS_UNFINISHED; 
  d_baseMatch.clear();
  d_eq_amb.clear();
  d_eind.clear();
  d_litMatches[0].clear();
  d_litMatches[1].clear();
  d_litMatchCandidates[0].clear();
  d_litMatchCandidates[1].clear();
  d_matches.clear();
  d_anyMatches.clear();
  //d_numEqArg.clear();
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
}

bool InstantiatorTheoryUf::doInstantiation( int effort )
{
  if( effort==0 ){
    debugPrint("quant-uf");
  }
  Debug("quant-uf") << "Search (" << effort << ") for instantiation for UF: " << std::endl;

  d_status = STATUS_SAT;
  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    if( d_instEngine->getActive( it->first ) ){
      d_quantStatus = STATUS_UNFINISHED;
      process( it->first, effort );
      Instantiator::updateStatus( d_status, d_quantStatus );
    }
  }
  //if( d_inst_matches.getNumMatches()>0 ){
  //  Debug("quant-uf") << "*** I produced these matches (" << e << ") : " << std::endl;
  //  d_inst_matches.debugPrint("quant-uf");
  //  Debug("quant-uf") << std::endl;
  //}
  if( effort==4 && d_status==STATUS_UNFINISHED ){
    d_status = STATUS_UNKNOWN;
    Debug("quant-uf-debug") << "Stuck at this state:" << std::endl;
    debugPrint("quant-uf-debug");
  }
  return false;
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
    Debug( c ) << f << std::endl;
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
        Debug( c ) << "      " << *it << std::endl;
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
  Debug("quant-uf") << "Try to solve (" << effort << ") for " << f << "... " << std::endl;
  if( effort==0 ){
    //calculate base matches
    d_baseMatch[f] = InstMatch( f, d_instEngine );
    //check if any instantiation constants are solved for
    for( int j = 0; j<(int)d_instEngine->d_inst_constants[f].size(); j++ ){
      Node i = d_instEngine->d_inst_constants[f][j];
      if(  d_instEngine->getTheoryEngine()->theoryOf( i )==getTheory() ){
        Node c;
        if( d_instEngine->d_ic_active.find( i )==d_instEngine->d_ic_active.end() ){
          //i does not exist in a literal in the current context, can use fresh constant
          c = NodeManager::currentNM()->mkVar( i.getType() ); 
          //c = d_instEngine->d_skolem_constants[f][j];  //for convience/performance, use skolem constant?
        }else{
          Node rep = getRepresentative( i );
          if( !rep.hasAttribute(InstConstantAttribute()) ){
            c = rep;
          }
        }
        if( c!=Node::null() ){
          d_baseMatch[f].setMatch( i, c );
        }
      }
    }
    if( d_baseMatch[f].isComplete() ){
      //f is solved
      d_instEngine->addInstantiation( &d_baseMatch[f] );
    }
  }else{
    NodeLists::iterator ob_i = d_obligations.find( f );
    if( ob_i!=d_obligations.end() ){
      NodeList* ob = (*ob_i).second;
      if( effort==1 ){
        InstMatchGroup combined;
        bool firstTime = true;
        // for each literal asserted about the negation of the body of f
        for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
          Node lit = (*it);
          bool isEq = true;
          if( lit.getKind()==NOT ){
            lit = lit[0];
            isEq = false;
          }
          Debug("quant-uf-alg-2") << "Process obligation " << (*it) << std::endl;
          calculateEIndLit( lit[0], lit[1], f, isEq );
          int ind = isEq ? 0 : 1;
          if( firstTime ){
            combined.add( d_litMatches[ind][lit[0]][lit[1]] );
            firstTime = false;
          }else{
            combined.merge( d_litMatches[ind][lit[0]][lit[1]] );
          }
          if( combined.getNumMatches()==0 ){
            break;
          }
        }
        for( int i=0; i<(int)combined.d_matches.size(); i++ ){
          if( combined.d_matches[i].isComplete( &d_baseMatch[f] ) ){
            //psi is E-induced
            combined.d_matches[i].add( d_baseMatch[f] );
            if( d_instEngine->addInstantiation( &combined.d_matches[i] ) ){
              break;
            }
          }
        }
      }else{
        bool resolveMatches = true;
        bool resolveMerges = true;
        std::vector< InstMatchGroup* > mergeFails;
        std::vector< std::vector< InstMatchGroup* > > mergeLitFails;
        std::vector< std::pair< Node, Node > > matchFails[2];
        // for each literal asserted about the negation of the body of f
        for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
          Node lit = (*it);
          bool isEq = true;
          if( lit.getKind()==NOT ){
            lit = lit[0];
            isEq = false;
          }
          Debug("quant-uf-alg") << "Process obligation " << lit << std::endl;
          calculateEIndLit( lit[0], lit[1], f, isEq );
          int ind = isEq ? 0 : 1;
          if( d_litMatches[ind][lit[0]][lit[1]].getNumMatches()>0 ){
            Debug("quant-uf-alg") << "-> Literal is induced." << std::endl;
            mergeFails.push_back( &d_litMatches[ind][lit[0]][lit[1]] );
          }else{
            resolveMerges = false;
            if( effort==2 ){
              resolveMatches = false;
              Debug("quant-uf-alg") << "-> Literal is not induced." << std::endl;
              break;
            }else{
              if( d_litMatchCandidates[ind][lit[0]][lit[1]].empty() ){
                if( effort==3 ){
                  resolveMatches = false;
                  Debug("quant-uf-alg") << "-> No literal matches found." << std::endl;
                  break;
                }else{
                  Node amb_t[2];
                  for( int i=0; i<2; i++ ){
                    if( lit[i].getAttribute(InstConstantAttribute())==f ){
                      calculateMatches( f, lit[i] );
                      if( d_matches[ lit[i] ].empty() ){
                        //is lit[i] unconstrained in M?
                        resolveModel( f, lit[i] );
                        if( d_anyMatches[ lit[i] ].empty() ){
                          //model can be generated?
                          //d_quantStatus = STATUS_SAT;
                        }
                      }else{
                        //maybe do all?
                        //sortMatches( f, lit[i] );
                        Debug("quant-uf-alg") << "-> " << lit[i] << " matchable with ";
                        Debug("quant-uf-alg") << d_matches[ lit[i] ][0] << "." << std::endl;
                        amb_t[i] = d_matches[ lit[i] ][0];
                      }
                    }else{
                      amb_t[i] = lit[i];
                    }
                  }
                  if( amb_t[0]!=Node::null() && amb_t[1]!=Node::null() ){
                    //t and t_{~s} are eq-dep, s and s_{~t} are eq-dep, but t_{~s} !~ s_{~t}
                    if( !areEqual( amb_t[0], amb_t[1] ) && !areDisequal( amb_t[0], amb_t[1] ) ){
                      addSplitEquality( amb_t[0], amb_t[1] );
                    }
                    //alternatively, we could try to ensure that t and t_{~s} match
                    // and similarly for s and s_{~t}.
                  }
                }
              }else{
                matchFails[ ind ].push_back( std::pair< Node, Node >( lit[0], lit[1] ) );
              }
            }
          }
        }
        if( resolveMerges ){
          resolveMerge( mergeFails, f );
        }
        if( resolveMatches ){
          for( int e=0; e<2; e++ ){
            for( int i=0; i<(int)matchFails[e].size(); i++ ){
              resolveLitMatch( matchFails[e][i].first, matchFails[e][i].second, f, e==0 );
            }
          }
        }
      }
    }
  }

  Debug("quant-uf-alg") << std::endl;
}

bool InstantiatorTheoryUf::resolveLitMatch( Node t, Node s, Node f, bool isEq ){
  Debug("quant-uf-alg") << "Why wasn't a match produced for ";
  Debug("quant-uf-alg") << t << ( !isEq ? " != " : " = " ) << s << "?" << std::endl;
  bool addedLemma = false;
  int ind = isEq ? 0 : 1;
  Assert( !d_litMatchCandidates[ind][t][s].empty() );
  if( !isEq ){
    if( s.getAttribute(InstConstantAttribute())==f ){
      for( int i=0; i<(int)d_litMatchCandidates[1][t][s].size(); i++ ){
        Node mt = d_litMatchCandidates[1][t][s][i][0];
        Node ms = d_litMatchCandidates[1][t][s][i][1];
        if( resolveMatchPair( t, mt, s, ms, f ) ){
          addedLemma = true;
          break;
        }
      }
    }else{
      for( int i=0; i<(int)d_litMatchCandidates[ 1 ][ t ][ s ].size(); i++ ){
        if( resolveLitMatch( t, d_litMatchCandidates[ 1 ][ t ][ s ][i], f, true ) ){
          addedLemma = true;
          break;
        }
      }
    }
  }else{
    //if have same top symbol, look at arguments directly
    if( t.getKind()==APPLY_UF && s.getKind()==APPLY_UF && 
        t.getOperator()==s.getOperator() ){
      for( int j=0; j<(int)t.getNumChildren(); j++ ){
        Node n1 = t[j];
        Node n2 = s[j];
        if( !areEqual( n1, n2 ) ){
          if( n2.getAttribute(InstConstantAttribute())==f && !n1.hasAttribute(InstConstantAttribute()) ){
            Node temp = n2;
            n2 = n1;
            n1 = temp;
          }
          if( n1.getAttribute(InstConstantAttribute())==f ){
            if( resolveLitMatch( n1, n2, f, true ) ){
              addedLemma = true;
            }
          }else{
            if( addSplitEquality( n1, n2 ) ){
              addedLemma = true;
            }
          }
        }
      }
    }else{
      if( s.getAttribute(InstConstantAttribute())==f ){
        for( int i=0; i<(int)d_litMatchCandidates[0][t][s].size(); i++ ){
          Node m = d_litMatchCandidates[0][t][s][i];
          if( resolveMatchPair( t, m, s, m, f ) ){
            addedLemma = true;
            break;
          }
        }
      }else{
        for( int i=0; i<(int)d_litMatchCandidates[0][t][s].size(); i++ ){
          if( resolveMatch( t, d_litMatchCandidates[0][t][s][i], f ) ){
            addedLemma = true;
            break;
          }
        }
      }
    }
  }
  return addedLemma;
}

bool InstantiatorTheoryUf::resolveMatchPair( Node t, Node mt, Node s, Node ms, Node f ){
  Debug("quant-uf-alg") << "Resolve match pair " << t << " = " << mt << ", " << s << " = " << ms << std::endl;
  Debug("quant-uf-alg") << "Match status = " << !d_litMatches[0][t][mt].empty() << " " << !d_litMatches[0][s][ms].empty() << std::endl;
  if( !d_litMatches[0][t][mt].empty() && !d_litMatches[0][s][ms].empty() ){
    std::vector< InstMatchGroup* > mgg;
    mgg.push_back( &d_litMatches[0][t][mt] );
    mgg.push_back( &d_litMatches[0][s][ms] );
    if( resolveMerge( mgg, f ) ){
      return true;
    }
  }
  if( d_litMatches[0][t][mt].empty() ){
    if( resolveMatch( t, mt, f ) ){
      return true;
    }
  }
  if( d_litMatches[0][s][ms].empty() ){
    if( resolveMatch( s, ms, f ) ){
      return true;
    }
  }
  return false;
}

bool InstantiatorTheoryUf::resolveMatch( Node t, Node g, Node f ){
  Assert( !g.hasAttribute(InstConstantAttribute()) );
  Debug("quant-uf-alg") << "Why didn't " << t << " match with " << g << "?" << std::endl;
  if( !t.hasAttribute(InstConstantAttribute()) ){
    return addSplitEquality( t, g );
  }else{
    Assert( d_litMatches[0][t][g].empty() );
    bool addedLemma = false;
    calculateEqAmb( t, g, f );
    Assert( d_eq_amb[t][g] );
    Assert( t.getKind()==APPLY_UF && g.getKind()==APPLY_UF );
    Assert( t.getNumChildren()==g.getNumChildren() );
    std::vector< InstMatchGroup* > mergeFails;
    std::vector< std::pair< Node, Node > > matchFails;
    bool resolveMerges = true;
    for( int j=0; j<(int)t.getNumChildren(); j++ ){
      if( !areEqual( t[j], g[j] ) ){
        if( t[j].hasAttribute(InstConstantAttribute()) ){
          Node ga = getRepresentative( g[j] );
          calculateEIndLit( t[j], ga, f, true );
          if( d_litMatches[0][ t[j] ][ ga ].getNumMatches()>0 ){
            // t[j] and ga were matched
            mergeFails.push_back( &d_litMatches[0][ t[j] ][ ga ] );
          }else{
            resolveMerges = false;
            if( d_litMatchCandidates[ 0 ][ t[j] ][ ga ].empty() ){
              //DO_THIS
              //calculateMatches( f, t[j] );
            }else{
              matchFails.push_back( std::pair< Node, Node >( t[j], ga ) );
            }
          }
        }else{
          //t and g have concrete ground term arguments that are not entailed to be equal
          addSplitEquality( t[j], g[j] );
          resolveMerges = false;
          addedLemma = true;
        }
      }
    }
    if( !resolveMerges ){
      //for arguments that did not match
      for( int i=0; i<(int)matchFails.size(); i++ ){
        if( resolveLitMatch( matchFails[i].first, matchFails[i].second, f, true ) ){
          addedLemma = true;
        }
      }
    }else{
      //all arguments matched, but did not merge
      if( resolveMerge( mergeFails, f ) ){
        addedLemma = true;
      }
    }
    return addedLemma;
  }
}

bool mgVecCompare( std::pair< std::vector< int >, InstMatch > i,
                   std::pair< std::vector< int >, InstMatch > j ) { return (i.first.size()>j.first.size()); }

bool InstantiatorTheoryUf::resolveMerge( std::vector< InstMatchGroup* >& matches, Node f ){
  bool addedLemma = false;
  for( int i=0; i<(int)matches.size(); i++ ){
    Assert( !matches[i]->d_matches.empty() );
  }
  if( matches.size()>1 ){
    Debug("quant-uf-alg") << "Why weren't we able to merge these sets of unifiers?  " << std::endl;
    for( int i=0; i<(int)matches.size(); i++ ){
      Debug("quant-uf-alg") << "#" << i << ": " << std::endl;
      matches[i]->debugPrint( "quant-uf-alg" );
      Debug("quant-uf-alg") << std::endl;
    }
    std::vector< std::pair< std::vector< int >, InstMatch > > combined;
    for( int i=0; i<(int)matches.size(); i++ ){
      std::vector< std::pair< std::vector< int >, InstMatch > > newCombined;
      newCombined.insert( newCombined.begin(), combined.begin(), combined.end() );
      std::vector< int > vecI;
      vecI.push_back( i );
      for( int j=0; j<(int)matches[i]->getNumMatches(); j++ ){
        newCombined.push_back( std::pair< std::vector< int >, InstMatch >( vecI, InstMatch( matches[i]->getMatch( j ) ) ) );
        for( int k=0; k<(int)combined.size(); k++ ){
          InstMatch temp( matches[i]->getMatch( j ) );
          if( temp.merge( combined[k].second ) ){
            std::vector< int > merged;
            merged.insert( merged.begin(), combined[k].first.begin(), combined[k].first.end() );
            merged.push_back( i );
            newCombined.push_back( std::pair< std::vector< int >, InstMatch >( merged, temp ) );
          }
        }
      }
      combined.clear();
      combined.insert( combined.begin(), newCombined.begin(), newCombined.end() );
    }
    std::random_shuffle( combined.begin(), combined.end() );
    //use the most merged matches first
    std::sort( combined.begin(), combined.end(), mgVecCompare );
    Debug("quant-uf-alg") << "Combined matches: " << std::endl;
    for( int i=0; i<(int)combined.size(); i++ ){
      for( int j=0; j<(int)combined[i].first.size(); j++ ){
        Debug("quant-uf-alg") << combined[i].first[j] << " ";
      }
      Debug("quant-uf-alg") << ": " << std::endl;
      combined[i].second.debugPrint("quant-uf-alg");
    }
    for( int i=0; i<(int)combined.size(); i++ ){
      for( int j=0; j<(int)matches.size(); j++ ){
        if( std::find( combined[i].first.begin(), combined[i].first.end(), j )==combined[i].first.end() ){
          Debug("quant-uf-alg") << "Determine merge conflict " << i << " " << j << std::endl;
          //find minimal disagreement in matches[j] with combined[i].second
          int minUndet;
          int minIndex = -1;
          for( int k=0; k<(int)matches[j]->getNumMatches(); k++ ){
            Assert( matches[j]->getMatch( k )->getQuantifier()==combined[i].second.getQuantifier() );
            bool isConsistent = true;
            int undet = 0;
            for( int l=0; l<(int)combined[i].second.d_vars.size(); l++ ){
              Node var = combined[i].second.d_vars[l];
              Node v1 = combined[i].second.d_map[ var ];
              Node v2 = matches[j]->getMatch( k )->d_map[ var ];
              if( v1!=Node::null() && v2!=Node::null() ){
                if( areDisequal( v1, v2 ) ){
                  isConsistent = false;
                  break;
                }else if( !areEqual( v1, v2 ) ){
                  undet++;
                }
              }
            }
            if( isConsistent && undet>0 ){
              if( minIndex==-1 || undet<minUndet ){
                minIndex = k;
                minUndet = undet;
              }
            }
          }
          if( minIndex!=-1 ){
            Debug("quant-uf-alg") << "Minimal disagreement, resolve: " << std::endl;
            combined[i].second.debugPrint("quant-uf-alg");
            Debug("quant-uf-alg") << "-----" << std::endl;
            matches[j]->getMatch( minIndex )->debugPrint("quant-uf-alg");
            Debug("quant-uf-alg") << std::endl;
            for( int l=0; l<(int)combined[i].second.d_vars.size(); l++ ){
              Node var = combined[i].second.d_vars[l];
              Node v1 = combined[i].second.d_map[ var ];
              Node v2 = matches[j]->getMatch( minIndex )->d_map[ var ];
              if( v1!=Node::null() && v2!=Node::null() ){
                if( !areEqual( v1, v2 ) ){
                  if( addSplitEquality( v1, v2 ) ){
                    addedLemma = true;
                  }
                }
              }
            }
          }else{
            Debug("quant-uf-alg") << "Could not find consistent disagreement." << std::endl;
          }
        }
      }
      if( addedLemma ){
        break;
      }
    }
    ////if no lemmas added, add complete instantiations such that psi is partially induced?
    //if( !addedLemma ){
    //  for( int i=0; i<(int)combined.size(); i++ ){
    //    if( combined[i].second.isComplete( &d_baseMatch[f] ) ){
    //      //psi is E-induced
    //      combined[i].second.add( d_baseMatch[f] );
    //      d_instEngine->addInstantiation( &combined[i].second );
    //    }
    //  }
    //}
  }else if( matches.size()==1 ){
    ////add complete instantiations such that psi is partially induced??
    //for( int i=0; i<(int)matches[0]->getNumMatches(); i++ ){
    //  if( matches[0]->getMatch( i )->isComplete( &d_baseMatch[f] ) ){
    //    InstMatch temp( matches[0]->getMatch( i ) );
    //    temp.add( d_baseMatch[f] );
    //    d_instEngine->addInstantiation( &temp );
    //  }
    //}
  }
  return addedLemma;
}

bool InstantiatorTheoryUf::resolveModel( Node f, Node t ){
  calculateMatches( f, t, true );
  if( d_anyMatches[t].empty() ){
    Debug("quant-uf-alg") << "-> " << t << " is unmatchable." << std::endl;
    return false;
  }else{
    bool addedLemma = false;
    Debug("quant-uf-alg") << "-> " << t << " only matchable with (ineligible) term ";
    Debug("quant-uf-alg") << d_anyMatches[t][0] << "." << std::endl;
    //resolve t and d_anyMatch[t], if possible, otherwise this term is unresolved
    if( t.getKind()!=INST_CONSTANT ){
      //see if any arguments are splittable
      Assert( t.getNumChildren()==d_anyMatches[t][0].getNumChildren() );
      for( int j=0; j<(int)t.getNumChildren(); j++ ){
        if( !t[j].hasAttribute(InstConstantAttribute()) &&
            !d_anyMatches[t][0][j].hasAttribute(InstConstantAttribute()) &&
            !areEqual( t[j], d_anyMatches[t][j] ) ){
          //Assert( !areDisequal( t[j], d_anyMatch[t][j] ) );
          if( addSplitEquality( t[j], d_anyMatches[t][0][j] ) ){
            addedLemma = true;
          }
        }
      }
    }
    return addedLemma;
  }
}

void InstantiatorTheoryUf::calculateEIndLit( Node t, Node s, Node f, bool isEq ){
  int ind = isEq ? 0 : 1;
  if( d_litMatches[ind].find( t )==d_litMatches[ind].end() ||
      d_litMatches[ind][t].find( s )==d_litMatches[ind][t].end() ){
    Debug("quant-uf-ematch") << "Calc Eind lit " << t << (isEq ? " = " : " != " ) << s << std::endl;
    if( !isEq ){
      Assert( t.getAttribute(InstConstantAttribute())==f );
      if( s.getAttribute(InstConstantAttribute())==f  ){
        //a disequality between two triggers
        //for each equivalence class E
        for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
          Node ct = (*it1).first;
          Assert( ct==getRepresentative( ct ) );
          if( ct.getType()==t.getType() && !ct.hasAttribute(InstConstantAttribute()) ){
            //for each equivalence class disequal from E
            for( int j=0; j<(int)d_dmap[ct].size(); j++ ){
              Node cs = d_dmap[ct][j];
              Assert( cs==getRepresentative( cs ) );
              if( !cs.hasAttribute(InstConstantAttribute()) ){
                InstMatchGroup mg;
                calculateEIndLit( t, ct, f, true );
                mg.add( d_litMatches[0][t][ct] );
                calculateEIndLit( s, cs, f, true );
                mg.merge( d_litMatches[0][s][cs] );
                d_litMatches[1][t][s].add( mg );
                if( !d_litMatchCandidates[0][t][ct].empty() && 
                    !d_litMatchCandidates[0][s][cs].empty() ){
                  Kind knd = ct.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
                  Node ceq = NodeManager::currentNM()->mkNode( knd, ct, cs );
                  d_litMatchCandidates[1][t][s].push_back( ceq );
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
            calculateEIndLit( t, ct, f, true );  
            d_litMatches[1][t][s].add( d_litMatches[0][t][ct] );
            if( !d_litMatchCandidates[0][t][ct].empty() ){
              //it could be the case that t matches with ct
              d_litMatchCandidates[1][t][s].push_back( ct );
            }
          }
        }
      }
    }else{
      //if have same top symbol, look at arguments directly
      if( t.getKind()==APPLY_UF && s.getKind()==APPLY_UF && t.getOperator()==s.getOperator() ){
        InstMatch m( f, d_instEngine );
        d_litMatches[0][t][s].d_matches.push_back( m );
        //add placeholder: this literal is literal matchable by default
        d_litMatchCandidates[0][t][s].push_back( Node::null() );
        for( int j=0; j<(int)t.getNumChildren(); j++ ){
          if( areDisequal( t[j], s[j] ) ){
            //we will not match these terms
            d_litMatches[0][t][s].clear();
            d_litMatchCandidates[0][t][s].clear();
            break;
          }
        }
        if( !d_litMatches[0][t][s].empty() ){
          for( int j=0; j<(int)t.getNumChildren(); j++ ){
            Node n1 = t[j];
            Node n2 = s[j];
            if( !areEqual( n1, n2 ) ){
              if( n2.getAttribute(InstConstantAttribute())==f && !n1.hasAttribute(InstConstantAttribute()) ){
                Node temp = n2;
                n2 = n1;
                n1 = temp;
              }
              if( n1.getAttribute(InstConstantAttribute())==f ){
                calculateEIndLit( n1, n2, f, true );
                d_litMatches[0][t][s].merge( d_litMatches[0][n1][n2] );
              }else{
                d_litMatches[0][t][s].clear();
              }
            }
            if( d_litMatches[0][t][s].empty() ){
              break;
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
              InstMatchGroup mg;
              calculateEIndLit( t, c, f, true );
              mg.add( d_litMatches[0][t][c] );
              calculateEIndLit( s, c, f, true );
              mg.merge( d_litMatches[0][s][c] );
              d_litMatches[0][t][s].add( mg );
              if( !d_litMatchCandidates[0][t][c].empty() && 
                  !d_litMatchCandidates[0][s][c].empty() ){
                // both have a chance to match in the equivalence class, thus i1 = i2 may be forced by c
                d_litMatchCandidates[0][t][s].push_back( c );
              }
            }
          }
        }else{
          Assert( !s.hasAttribute(InstConstantAttribute()) );
          Node c = getRepresentative( s );
          Assert( !c.hasAttribute(InstConstantAttribute()) );
          if( d_litMatches[0].find( t )==d_litMatches[0].end() ||
              d_litMatches[0][t].find( c )==d_litMatches[0][t].end() ){
            Debug("quant-uf-ematch") << "EIndMod " << t << " = " << c << std::endl;
            //equality between trigger and concrete ground term
            //build E-matches with terms in the same equivalence class
            if( t.getKind()==INST_CONSTANT || d_emap.find( c )==d_emap.end() ){
              calculateEInd( t, c, f );
              if( d_eq_amb[t][c] ){
                d_litMatchCandidates[0][t][c].push_back( c );
                d_litMatches[0][t][c].add( d_eind[t][c] );
              }
            }else{
              for( int j=0; j<(int)d_emap[c].size(); j++ ){
                Node ca = d_emap[c][j];
                if( !ca.hasAttribute(InstConstantAttribute()) ){
                  calculateEInd( t, ca, f );
                  if( d_eq_amb[t][ca] ){
                    d_litMatchCandidates[0][t][c].push_back( ca );
                    d_litMatches[0][t][c].add( d_eind[t][ca] );
                  }
                }
              }
              d_litMatches[0][t][c].removeRedundant();
            }
          }
          d_litMatches[0][t][s] = InstMatchGroup( &d_litMatches[0][t][c] );
          d_litMatchCandidates[0][t][s].insert( d_litMatchCandidates[0][t][s].begin(),
                                                d_litMatchCandidates[0][t][c].begin(),
                                                d_litMatchCandidates[0][t][c].end() );
        }
      }
    }
    d_litMatches[ind][t][s].removeDuplicate();
    //Debug("quant-uf-alg") << "Finished creating obligation matches." << std::endl;
    //if( d_litMatches[ lit ].d_matches.size()>0 ){
    //  Debug("quant-uf-alg") << "Matches for " << lit << " : " << std::endl;
    //  d_litMatches[ lit ].debugPrint( "quant-uf-alg" );
    //}
  }
}

void InstantiatorTheoryUf::calculateMatches( Node f, Node t, bool any ){
  Assert( t.getAttribute(InstConstantAttribute())==f );
  if( ( !any && d_matches.find( t )==d_matches.end() ) ||
      ( any && d_anyMatches.find( t )==d_anyMatches.end() ) ){
    if( !any ){
      d_matches[t].clear();
    }else{
      d_anyMatches[t].clear();
    }
    Node t_match;
    for( BoolMap::const_iterator it = d_terms.begin(); it!=d_terms.end(); ++it ){
      Node c = (*it).first;
      if( t.getType()==c.getType() ){
        bool hasInst = c.hasAttribute(InstConstantAttribute());
        if( !hasInst || ( any && hasInst && t!=c ) ){
          calculateEqAmb( t, c, f );
          if( d_eq_amb[t][c] ){
            if( !any ){
              d_matches[t].push_back( c );
            }else{
              d_anyMatches[t].push_back( c );
            }
          }
        }
      }
    }
  }
}

void InstantiatorTheoryUf::calculateEInd( Node i, Node c, Node f ){
  //Node oi = i;
  //Node oc = c;
  //std::cout << "--> " << oi << " " << oc << std::endl;
  Assert( i.getType()==c.getType() );
  Assert( i.getAttribute(InstConstantAttribute())==f );
  Assert( !c.hasAttribute(InstConstantAttribute()) );
  //if not already generated
  if( d_eind.find( i )==d_eind.end() || d_eind[i].find( c )==d_eind[i].end() ){
    d_eind[i][c].clear();
    Debug("quant-uf-ematch") << "E-match " << i << " " << c << std::endl;
    if( !areDisequal( i, c ) ){
      if( i.getKind()==INST_CONSTANT ){
        InstMatch m( f, d_instEngine );
        if( !areEqual( i, c ) ){
          m.setMatch( i, getRepresentative( c ) );
        }
        Debug("quant-uf-ematch") << i << " and " << c << " Ematched." << std::endl;
        d_eq_amb[i][c] = true;
        d_eind[i][c].d_matches.push_back( m );
      }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
        //equality independent, do nothing
        d_eq_amb[i][c] = false;
        Debug("quant-uf-ematch") << i << " and " << c << " FAILED operators." << std::endl;
      }else{
        Assert( i.getKind()==APPLY_UF && c.getKind()==APPLY_UF );
        Assert( i.getNumChildren()==c.getNumChildren() );
        d_eq_amb[i][c] = true;
        InstMatch m( f, d_instEngine );
        d_eind[i][c].d_matches.push_back( m );
        for( int j=0; j<(int)c.getNumChildren(); j++ ){
          if( areDisequal( i[j], c[j] ) ){
            Debug("quant-uf-ematch") << i << " and " << c << " FAILED disequal arg. " << j << std::endl;
            d_eq_amb[i][c] = false;
            d_eind[i][c].clear();
            break;
          }else if( !areEqual( i[j], c[j] ) && !d_eind[i][c].empty() ){
            if( i[j].hasAttribute(InstConstantAttribute()) ){
              Node ca = getRepresentative( c[j] );
              calculateEIndLit( i[j], ca, f, true );
              if( !d_eind[i][c].merge( d_litMatches[0][i[j]][ca] ) ){
                Debug("quant-uf-ematch") << i << " and " << c << " FAILED incompatible match. " << j << std::endl;
                d_eind[i][c].clear();
              }
            }else{
              Debug("quant-uf-ematch") << i << " and " << c << " FAILED unequal arg." << j << std::endl;
              d_eind[i][c].clear();
            }
          }
        }
      }
    }else{
      Debug("quant-uf-ematch") << i << " and " << c << " FAILED disequal." << std::endl;
      calculateEqAmb( i, c, f );
    }
    Assert( d_eq_amb.find( i )!=d_eq_amb.end() && d_eq_amb[i].find( c )!=d_eq_amb[i].end() );
  }
  //std::cout << "<-- " << oi << " " << oc << " " << moduloEq << std::endl;
}

void InstantiatorTheoryUf::calculateEqAmb( Node i, Node c, Node f ){
  if( d_eq_amb.find( i )==d_eq_amb.end() ||
      d_eq_amb[i].find( c )==d_eq_amb[i].end() ){
    if( i.getKind()==INST_CONSTANT ){
      d_eq_amb[i][c] = true;
    }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
      d_eq_amb[i][c] = false;
    }else{
      Assert( i.getKind()==APPLY_UF && c.getKind()==APPLY_UF );
      Assert( i.getNumChildren()==c.getNumChildren() );
      d_eq_amb[i][c] = true;
      for( int j=0; j<(int)c.getNumChildren(); j++ ){
        if( areDisequal( i[j], c[j] ) ){
          d_eq_amb[i][c] = false;
          break;
        }
      }
    }
  }
}

//int InstantiatorTheoryUf::getNumNeqArgs( Node i, Node c ){
//  if( d_numEqArg.find( i )==d_numEqArg.end() ||
//      d_numEqArg[i].find( c )==d_numEqArg[i].end() ){
//    Assert( i.hasAttribute(InstConstantAttribute()) );
//    Assert( i.getType()==c.getType() );
//    int argsNeq = 0;
//    //if matchable, consider all arguments to be equal
//    bool matched = false;
//    if( !c.hasAttribute(InstConstantAttribute()) ){
//      calculateEInd( i, c, i.getAttribute(InstConstantAttribute()) );
//      matched = d_does_eind[i][c];
//    }
//    if( !matched ){
//      if( i.getKind()!=INST_CONSTANT ){
//        Assert( i.getKind()==APPLY_UF && c.getKind()==APPLY_UF );
//        Assert( i.getOperator()==c.getOperator() );
//        Assert( i.getNumChildren()==c.getNumChildren() );
//        for( int k=0; k<(int)c.getNumChildren(); k++ ){
//          if( !areEqual( i[k], c[k] ) ){
//            argsNeq++;
//          }
//        }
//      }
//    }
//    d_numEqArg[i][c] = argsNeq;
//    return argsNeq;
//  }else{
//    return d_numEqArg[i][c];
//  }
//}

bool InstantiatorTheoryUf::addSplitEquality( Node n1, Node n2 ){
  Assert( !n1.hasAttribute(InstConstantAttribute()) );
  Assert( !n2.hasAttribute(InstConstantAttribute()) );
  Assert( !areEqual( n1, n2 ) );
  Assert( !areDisequal( n1, n2 ) );
  Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  Node fm = NodeManager::currentNM()->mkNode( knd, n1, n2 );
  fm = Rewriter::rewrite( fm );
  if( d_instEngine->addSplit( fm ) ){
    Debug("quant-uf-split") << "*** Add split " << n1 << " = " << n2 << std::endl;
    //require phase?
    d_instEngine->d_curr_out->requirePhase( fm, true );
    return true;
  }else{
    return false;
  }
}

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
Instantiator( c, ie ),
//d_subterms( c ),
//d_subterm_size( c ),
d_obligations( c ),
d_th(th),
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

Theory* InstantiatorTheoryUf::getTheory() { 
  return d_th; 
}

void InstantiatorTheoryUf::check( Node assertion )
{
  //TheoryUF* t = (TheoryUF*)d_th;
  //Debug("quant-uf") << "InstantiatorTheoryUf::check: " << assertion << std::endl;
  //switch(assertion.getKind()) {
  //case kind::EQUAL:
  //case kind::IFF:
  //  assertEqual(assertion[0], assertion[1]);
  //  break;
  //case kind::APPLY_UF:
  //  { // assert it's a predicate
  //    Assert(assertion.getOperator().getType().getRangeType().isBoolean());
  //    assertEqual(assertion, t->d_trueNode);
  //  }
  //  break;
  //case kind::NOT:
  //  if(assertion[0].getKind() == kind::EQUAL ||
  //     assertion[0].getKind() == kind::IFF) {
  //    assertDisequal(assertion[0][0], assertion[0][1]);
  //  } else {
  //    // negation of a predicate
  //    Assert(assertion[0].getKind() == kind::APPLY_UF);
  //    // assert it's a predicate
  //    Assert(assertion[0].getOperator().getType().getRangeType().isBoolean());
  //    assertEqual(assertion[0], t->d_falseNode);
  //  }
  //  break;
  //default:
  //  Unhandled(assertion.getKind());
  //}
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
  d_does_eind.clear();
  d_eq_amb.clear();
  d_eind.clear();
  d_eind_mod.clear();
  d_litMatches.clear();
  d_bestLitMatch[0].clear();
  d_bestLitMatch[1].clear();
  d_bestMatch.clear();
  d_anyMatch.clear();
  d_numEqArg.clear();
  ////set representatives
  //d_reps.clear();
  //for( BoolMap::iterator it = d_terms.begin(); it!=d_terms.end(); ++it ){
  //  Node n = (*it).first;
  //  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) ){
  //    Node rep = ((TheoryUF*)d_th)->d_equalityEngine.getRepresentative( n );
  //    if( rep.hasAttribute(InstConstantAttribute()) && 
  //        !n.hasAttribute(InstConstantAttribute()) ){
  //      if( d_reps.find( rep )!=d_reps.end() ){
  //        d_reps[n] = d_reps[rep];
  //      }else{
  //        d_reps[n] = n;
  //        d_reps[rep] = n;
  //      }
  //    }else{
  //      d_reps[n] = rep;
  //    }
  //  }
  //}
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
    d_emap[ it->second ].insert( d_emap[ it->second ].begin(), d_emap[ it->first ].begin(), d_emap[ it->second ].end() );
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

void InstantiatorTheoryUf::process( Node f, int effort )
{
  Debug("quant-uf") << "Try to solve (" << effort << ") for " << f << "... " << std::endl;
  if( effort==0 ){
    //calculate base matches
    d_baseMatch[f] = InstMatch( f, d_instEngine );
    //check if any instantiation constants are solved for
    for( int j = 0; j<(int)d_instEngine->d_inst_constants[f].size(); j++ ){
      Node i = d_instEngine->d_inst_constants[f][j];
      Node c;
      if( d_terms_full.find( i )==d_terms_full.end() ){
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
    if( d_baseMatch[f].isComplete() ){
      //f is solved
      d_instEngine->addInstantiation( &d_baseMatch[f] );
    }
  }else{
    NodeLists::iterator ob_i = d_obligations.find( f );
    Assert( ob_i!=d_obligations.end() );  //should have at least one obligation (otherwise it is solved)
    NodeList* ob = (*ob_i).second;
    if( effort==1 ){
      InstMatchGroup combined;
      bool firstTime = true;
      // for each literal asserted about the negation of the body of f
      for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
        Debug("quant-uf-alg-2") << "Process obligation " << (*it) << std::endl;
        calculateEIndLit( (*it), f );
        if( firstTime ){
          combined.add( d_litMatches[ (*it) ] );
          firstTime = false;
        }else{
          combined.merge( d_litMatches[ (*it) ] );
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
      std::vector< std::vector< InstMatchGroup* > > mergeFails;
      mergeFails.push_back( std::vector< InstMatchGroup* >() );
      std::vector< std::pair< Node, Node > > matchFails;
      // for each literal asserted about the negation of the body of f
      for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
        Node lit = (*it);
        Debug("quant-uf-alg") << "Process obligation " << lit << std::endl;
        calculateEIndLit( lit, f );
        if( d_litMatches[ lit ].getNumMatches()>0 ){
          Debug("quant-uf-alg") << "-> Literal is induced." << std::endl;
          mergeFails[0].push_back( &d_litMatches[ lit ] );
        }else{
          if( effort==2 ){
            resolveMatches = false;
            resolveMerges = false;
            Debug("quant-uf-alg") << "-> Literal is not induced." << std::endl;
            break;
          }else{
            bool isEq = true;
            if( lit.getKind()==NOT ){
              lit = lit[0];
              isEq = false;
            }
            findBestLiteralMatch( f, lit[0], lit[1], isEq, true );
            Node m1 = d_bestLitMatch[ isEq ? 0 : 1 ][ lit[0] ][ lit[1] ];
            if( m1==Node::null() ){
              if( effort==3 ){
                resolveMatches = false;
                resolveMerges = false;
                Debug("quant-uf-alg") << "-> No literal matches found." << std::endl;
                break;
              }else{
                Node amb_t[2];
                for( int i=0; i<2; i++ ){
                  if( lit[i].getAttribute(InstConstantAttribute())==f ){
                    findBestMatch( f, lit[i] );
                    if( d_bestMatch[ lit[i] ]==Node::null() ){
                      //is lit[i] unconstrained in M?
                      resolveModel( f, lit[i] );
                      if( d_anyMatch[ lit[i] ]==Node::null() ){
                        //model can be generated?
                        //d_quantStatus = STATUS_SAT;
                      }
                    }else{
                      Debug("quant-uf-alg") << "-> " << lit[i] << " matchable with ";
                      Debug("quant-uf-alg") << d_bestMatch[ lit[i] ] << "." << std::endl;
                      amb_t[i] = d_bestMatch[ lit[i] ];
                    }
                  }else{
                    amb_t[i] = lit[i];
                  }
                }
                if( amb_t[0]!=Node::null() && amb_t[1]!=Node::null() ){
                  //t and t_{~s} are eq-dep, s and s_{~t} are eq-dep, but t_{~s} !~ s_{~t}
                  //if( !areEqual( amb_t[0], amb_t[1] ) && !areDisequal( amb_t[0], amb_t[1] ) ){
                  //  addSplitEquality( amb_t[0], amb_t[1] );
                  //}
                  //alternatively, we could try to ensure that t and t_{~s} match
                  // and similarly for s and s_{~t}.
                }
              }
            }else{
              Node m2;
              if( !d_does_eind[ lit[0] ][ m1 ] ){
                matchFails.push_back( std::pair< Node, Node >( lit[0], m1 ) );
              }
              if( lit[1].getAttribute(InstConstantAttribute())==f  ){
                m2 = d_bestLitMatch[ isEq ? 0 : 1 ][ lit[1] ][ lit[0] ];
                if( d_does_eind[ lit[0] ][ m1 ] && d_does_eind[ lit[1] ][ m2 ] ){
                  //the merge between two sides of literals failed
                  std::vector< InstMatchGroup* > mg;
                  mg.push_back( &d_eind[ lit[0] ][ m1 ] );
                  mg.push_back( &d_eind[ lit[1] ][ m2 ] );
                  mergeFails.push_back( mg );
                }else if( !d_does_eind[ lit[1] ][ m2 ] ){
                  matchFails.push_back( std::pair< Node, Node >( lit[1], m2 ) );
                }
              }else{
                m2 = lit[1];
                //must have failed to match (otherwise would have been literal-level match)
                Assert( !d_does_eind[ lit[0] ][ m1 ] );
              }
              Debug("quant-uf-alg") << "-> Best literal match : " << m1 << " " << m2 << std::endl;
            }
          }
        }
      }
      if( resolveMerges ){
        for( int i=0; i<(int)mergeFails.size(); i++ ){
          resolveMerge( mergeFails[i], f );
        }
      }
      if( resolveMatches ){
        for( int i=0; i<(int)matchFails.size(); i++ ){
          resolveMatch( matchFails[i].first, matchFails[i].second, f );
        }
      }
    }
  }

  Debug("quant-uf-alg") << std::endl;
}

void InstantiatorTheoryUf::resolveMatch( Node t, Node g, Node f ){
  Debug("quant-uf-alg") << "Why didn't " << t << " match with " << g << "?" << std::endl;
  if( !t.hasAttribute(InstConstantAttribute()) ){
    addSplitEquality( t, g );
  }else{
    calculateEqAmb( t, g, f );
    Assert( d_eq_amb[t][g] );
    Assert( t.getKind()==APPLY_UF && g.getKind()==APPLY_UF );
    Assert( t.getNumChildren()==g.getNumChildren() );
    std::vector< InstMatchGroup* > mergeFails;
    std::vector< std::pair< Node, Node > > matchFails;
    bool resolveMatches = true;
    bool resolveMerges = true;
    for( int j=0; j<(int)t.getNumChildren(); j++ ){
      if( !areEqual( t[j], g[j] ) ){
        if( t[j].hasAttribute(InstConstantAttribute()) ){
          Node ga = getRepresentative( g[j] );
          calculateEIndMod( t[j], ga, f );
          if( d_eind_mod[ t[j] ][ ga ].getNumMatches()>0 ){
            // t[j] and ga were matched
            mergeFails.push_back( &d_eind_mod[ t[j] ][ ga ] );
          }else{
            findBestLiteralMatch( f, t[j], ga, true );
            if( d_bestLitMatch[0][ t[j] ][ ga ]!=Node::null() ){
              //figure out why t[j] did not match with (best guess) d_bestLitMatch[0][ t[j] ][ ga ]
              matchFails.push_back( std::pair< Node, Node >( t[j], d_bestLitMatch[0][ t[j] ][ ga ] ) );
            }else{
              findBestMatch( f, t[j] );
              if( d_bestMatch[ t[j] ]!=Node::null() ){
                //there is a eq dep term for t[j], but it is not equal to ga
                matchFails.push_back( std::pair< Node, Node >( d_bestMatch[ t[j] ], ga ) );
              }else{
                //is t[j] unconstrained in M?
                resolveModel( f, t[j] );
              }
            }
            resolveMerges = false;
          }
        }else{
          //t and g have concrete ground term arguments that are not entailed to be equal
          if( addSplitEquality( t[j], g[j] ) ){
            resolveMatches = false;
            resolveMerges = false;
          }
        }
      }
    }
    if( resolveMatches ){
      //some arguments did not match
      for( int i=0; i<(int)matchFails.size(); i++ ){
        resolveMatch( matchFails[i].first, matchFails[i].second, f );
      }
    }
    if( resolveMerges ){
      //all arguments matched, but did not merge
      resolveMerge( mergeFails, f );
    }
  }
}

bool mgVecCompare( std::pair< std::vector< int >, InstMatch > i,
                   std::pair< std::vector< int >, InstMatch > j ) { return (i.first.size()>j.first.size()); }

void InstantiatorTheoryUf::resolveMerge( std::vector< InstMatchGroup* >& matches, Node f ){
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
    std::sort( combined.begin(), combined.end(), mgVecCompare );
    Debug("quant-uf-alg") << "Combined matches: " << std::endl;
    for( int i=0; i<(int)combined.size(); i++ ){
      for( int j=0; j<(int)combined[i].first.size(); j++ ){
        Debug("quant-uf-alg") << combined[i].first[j] << " ";
      }
      Debug("quant-uf-alg") << ": " << std::endl;
      combined[i].second.debugPrint("quant-uf-alg");
    }
    int numCovered = 0;
    std::vector< bool > matchCover;
    matchCover.resize( (int)matches.size(), false );
    for( int i=0; i<(int)combined.size(); i++ ){
      bool process = false;
      for( int j=0; j<(int)combined[i].first.size(); j++ ){
        if( !matchCover[ combined[i].first[j] ] ){
          process = true;
          numCovered++;
          if( numCovered==(int)matches.size() ){
            process = false;
            break;
          }
        }
        matchCover[ combined[i].first[j] ] = true;
      }
      if( process ){
        for( int j=0; j<(int)matches.size(); j++ ){
          if( !matchCover[j] ){
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
              Assert( !isConsistent || undet>0 );
              if( isConsistent ){
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
                    addSplitEquality( v1, v2 );
                  }
                }
              }
            }else{
              Debug("quant-uf-alg") << "Could not find consistent disagreement." << std::endl;
            }
          }
        }
      }
      if( numCovered==(int)matches.size() || d_instEngine->hasAddedLemma() ){
        break;
      }
    }
    ////if no lemmas added, add complete instantiations such that psi is partially induced?
    //if( !d_instEngine->hasAddedLemma() ){
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
}

void InstantiatorTheoryUf::resolveModel( Node f, Node t ){
  findBestMatch( f, t, true );
  if( d_anyMatch[t]==Node::null() ){
    Debug("quant-uf-alg") << "-> " << t << " is unmatchable." << std::endl;
  }else{
    Debug("quant-uf-alg") << "-> " << t << " only matchable with (ineligible) term ";
    Debug("quant-uf-alg") << d_anyMatch[t] << "." << std::endl;
    //resolve t and d_anyMatch[t], if possible, otherwise this term is unresolved
    if( t.getKind()!=INST_CONSTANT ){
      //see if any arguments are splittable
      Assert( t.getNumChildren()==d_anyMatch[t].getNumChildren() );
      for( int j=0; j<(int)t.getNumChildren(); j++ ){
        if( !t[j].hasAttribute(InstConstantAttribute()) &&
            !d_anyMatch[t][j].hasAttribute(InstConstantAttribute()) &&
            !areEqual( t[j], d_anyMatch[t][j] ) ){
          //Assert( !areDisequal( t[j], d_anyMatch[t][j] ) );
          addSplitEquality( t[j], d_anyMatch[t][j] );
        }
      }
    }
  }
}

void InstantiatorTheoryUf::calculateEIndLit( Node lit, Node f ){
  //std::cout << "Calc Eind lit " << lit << std::endl;
  if( d_litMatches.find( lit )==d_litMatches.end() ){
    if( lit.getKind()==NOT ){
      Assert( lit[0][0].getAttribute(InstConstantAttribute())==f );
      if( lit[0][1].getAttribute(InstConstantAttribute())==f  ){
        //a disequality between two triggers
        Node i1 = lit[0][0];
        Node i2 = lit[0][1];
        //for each equivalence class E
        for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
          Node ci1 = (*it1).first;
          Assert( ci1==getRepresentative( ci1 ) );
          if( ci1.getType()==i1.getType() ){
            //for each equivalence class disequal from E
            for( int j=0; j<(int)d_dmap[ci1].size(); j++ ){
              Node ci2 = d_dmap[ci1][j];
              Assert( ci2==getRepresentative( ci2 ) );
              InstMatchGroup mg;
              calculateEIndMod( i1, ci1, f );
              mg.add( d_eind_mod[i1][ci1] );
              calculateEIndMod( i2, ci2, f );
              mg.merge( d_eind_mod[i2][ci2] );
              d_litMatches[ lit ].add( mg );
            }
          }
        }
      }else{
        Assert( !lit[0][1].hasAttribute(InstConstantAttribute()) );
        //a disequality between a trigger and ground term
        Node i = lit[0][0];
        Node c = getRepresentative( lit[0][1] );
        //match against all equivalence classes disequal from c
        for( int j=0; j<(int)d_dmap[c].size(); j++ ){
          Node ci = d_dmap[c][j];
          Assert( ci==getRepresentative( ci ) );
          calculateEIndMod( i, ci, f );  
          d_litMatches[ lit ].add( d_eind_mod[i][ci] );
        }
      }
    }else{
      Assert( lit.getKind()==IFF || lit.getKind()==EQUAL );
      //for efficiency: if have same top symbol, look at arguments directly
      if( lit[0].getKind()==APPLY_UF && lit[1].getKind()==APPLY_UF && lit[0].getOperator()==lit[1].getOperator() ){
        InstMatch m( f, d_instEngine );
        d_litMatches[ lit ].d_matches.push_back( m );
        for( int j=0; j<(int)lit[0].getNumChildren(); j++ ){
          if( areDisequal( lit[0][j], lit[1][j] ) ){
            d_litMatches[ lit ].clear();
          }
        }
        if( !d_litMatches[ lit ].empty() ){
          for( int j=0; j<(int)lit[0].getNumChildren(); j++ ){
            Node n1 = lit[0][j];
            Node n2 = lit[1][j];
            if( !areEqual( n1, n2 ) ){
              if( n2.getAttribute(InstConstantAttribute())==f && !n1.hasAttribute(InstConstantAttribute()) ){
                Node temp = n2;
                n2 = n1;
                n1 = temp;
              }
              if( n1.getAttribute(InstConstantAttribute())==f ){
                Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
                Node argLit = NodeManager::currentNM()->mkNode( knd, n1, n2 );
                calculateEIndLit( argLit, f );
                d_litMatches[ lit ].merge( d_litMatches[ argLit ] );
              }else{
                d_litMatches[ lit ].clear();
              }
            }
            if( d_litMatches[ lit ].empty() ){
              break;
            }
          }
        }
      }else{
        if( lit[1].getAttribute(InstConstantAttribute())==f ){
          //equality between two triggers
          Node i1 = lit[0];
          Node i2 = lit[1];
          //for each equivalence class
          for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
            Node c = (*it1).first;
            if( c.getType()==i1.getType() ){
              InstMatchGroup mg;
              calculateEIndMod( i1, c, f );
              mg.add( d_eind_mod[i1][c] );
              calculateEIndMod( i2, c, f );
              mg.merge( d_eind_mod[i2][c] );
              d_litMatches[ lit ].add( mg );
            }
          }
        }else{
          Assert( !lit[1].hasAttribute(InstConstantAttribute()) );
          //equality between trigger and concrete ground term
          Node i = lit[0];
          Node c = getRepresentative( lit[1] );
          //build E-matches with terms in the same equivalence class
          calculateEIndMod( i, c, f );
          d_litMatches[ lit ].add( d_eind_mod[i][c] );
        }
      }
    }
    d_litMatches[ lit ].removeDuplicate();
    //Debug("quant-uf-alg") << "Finished creating obligation matches." << std::endl;
    //if( d_litMatches[ lit ].d_matches.size()>0 ){
    //  Debug("quant-uf-alg") << "Matches for " << lit << " : " << std::endl;
    //  d_litMatches[ lit ].debugPrint( "quant-uf-alg" );
    //}
  }
}

void InstantiatorTheoryUf::findBestLiteralMatch( Node f, Node t, Node s, bool isEq, bool rhsPat ){
  //std::cout << "find best lit match " << t << (!isEq ? " !" : " ") << "= " << s;
  //std::cout << (rhsPat ? ", rhsPat" : "") << std::endl;
  Assert( t.getAttribute(InstConstantAttribute())==f );
  int ind = isEq ? 0 : 1;
  if( d_bestLitMatch[ind].find( t )==d_bestLitMatch[ind].end() ||
      d_bestLitMatch[ind][t].find( s )==d_bestLitMatch[ind][t].end() ){
    if( t==s ){
      if( isEq ){
        if( rhsPat ){
          findBestMatch( f, t );
          d_bestLitMatch[0][t][t] = d_bestMatch[t];
        }else{
          Node rep = getRepresentative( t );
          if( !rep.hasAttribute(InstConstantAttribute()) ){
            d_bestLitMatch[0][t][t] = rep;
          }
        }
      }else{
        d_bestLitMatch[0][t][t] = Node::null();
      }
    }else{
      Node t_match;
      Node s_match;
      if( !isEq ){
        if( s.getAttribute(InstConstantAttribute())==f && rhsPat ){
          //for each equivalence class E
          for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
            Node ct = (*it1).first;
            Assert( ct==getRepresentative( ct ) );
            if( ct.getType()==t.getType() ){
              //for each equivalence class disequal from E
              for( int j=0; j<(int)d_dmap[ct].size(); j++ ){
                Node cs = d_dmap[ct][j];
                Assert( cs==getRepresentative( cs ) );
                findBestLiteralMatch( f, t, ct, true );
                findBestLiteralMatch( f, s, cs, true );
                if( d_bestLitMatch[0][t][ct]!=Node::null() && d_bestLitMatch[0][s][cs]!=Node::null() ){
                  if( isBetterMatch( t, d_bestLitMatch[0][t][ct], t_match ) &&
                      isBetterMatch( s, d_bestLitMatch[0][s][cs], s_match ) ){
                    t_match = d_bestLitMatch[0][t][ct];
                    s_match = d_bestLitMatch[0][s][cs];
                  }
                }
              }
            }
          }
        }else{
          //a disequality between a trigger and ground term
          Node c = getRepresentative( s );
          for( int j=0; j<(int)d_dmap[c].size(); j++ ){
            Node ct = d_dmap[c][j];
            Assert( ct==getRepresentative( ct ) );
            findBestLiteralMatch( f, t, ct, true );
            if( isBetterMatch( t, d_bestLitMatch[0][t][ct], t_match ) ){
              t_match = d_bestLitMatch[0][t][ct];
            }
          }
        }
      }else{
        //if have same top symbol, only need to match arguments
        if( s.getAttribute(InstConstantAttribute())==f && rhsPat ){
          //equality between two triggers
          for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
            Node c = (*it1).first;
            if( c.getType()==t.getType() ){
              findBestLiteralMatch( f, t, c, true );
              findBestLiteralMatch( f, s, c, true );
              if( d_bestLitMatch[0][t][c]!=Node::null() && d_bestLitMatch[0][s][c]!=Node::null() ){
                if( isBetterMatch( t, d_bestLitMatch[0][t][c], t_match ) &&
                    isBetterMatch( s, d_bestLitMatch[0][s][c], s_match ) ){
                  t_match = d_bestLitMatch[0][t][c];
                  s_match = d_bestLitMatch[0][s][c];
                }
              }
            }
          }
        }else{
          //equality between trigger and concrete ground term
          Node c = getRepresentative( s );
          if( !areDisequal( t, c ) ){
            if( d_emap[c].empty() ){
              d_emap[c].push_back( c );
            }
            for( int j=0; j<(int)d_emap[c].size(); j++ ){
              Node ct = d_emap[c][j];
              if( !ct.hasAttribute(InstConstantAttribute()) ){
                calculateEqAmb( t, ct, f );
                if( d_eq_amb[t][ct] ){
                  if( isBetterMatch( t, ct, t_match ) ){
                    t_match = ct;
                  }
                }
              }
            }
          }
        }
      }
      d_bestLitMatch[ind][t][s] = t_match;
      if( s.getAttribute(InstConstantAttribute())==f && rhsPat ){
        d_bestLitMatch[ind][s][t] = s_match;
      }else{
        s_match = s;
      }
      //std::cout << "Literal match for " << t << (!isEq ? " !" : " ") << "= " << s << (rhsPat ? ", rhsPat" : "" ) << std::endl;
      //std::cout << "   is " << t_match;
      //if( s.getAttribute(InstConstantAttribute())==f && rhsPat ){
      //  std::cout << ", " << s_match;
      //}
      //std::cout << std::endl;
      //if( t_match!=Node::null() ){
      //  std::cout << "eqDeq = " << areEqual( t_match, s_match ) << " " << areDisequal( t_match, s_match ) << std::endl;
      //}
      Assert( t_match==Node::null() ||
              ( isEq && areEqual( t_match, s_match ) ) ||
              ( !isEq && areDisequal( t_match, s_match ) ) );
    }
  }
}

void InstantiatorTheoryUf::findBestMatch( Node f, Node t, bool any ){
  Assert( t.getAttribute(InstConstantAttribute())==f );
  if( ( !any && d_bestMatch.find( t )==d_bestMatch.end() ) ||
      ( any && d_anyMatch.find( t )==d_anyMatch.end() ) ){
    int maxStatus;
    Node t_match;
    for( BoolMap::const_iterator it = d_terms.begin(); it!=d_terms.end(); ++it ){
      Node c = (*it).first;
      if( t.getType()==c.getType() ){
        bool hasInst = c.hasAttribute(InstConstantAttribute());
        if( !hasInst || ( any && hasInst && t!=c ) ){
          int status = ( areEqual( t, c ) ? 1 : ( areDisequal( t, c ) ? -1 : 0 ) );
          if( t_match==Node::null() || status>=maxStatus ){
            calculateEqAmb( t, c, f );
            if( d_eq_amb[t][c] ){
              if( isBetterMatch( t, c, t_match ) ){
                t_match = c;
                maxStatus = status;
              }
            }
          }
        }
      }
    }
    if( any ){
      d_anyMatch[t] = t_match;
    }else{
      d_bestMatch[t] = t_match;
    }
  }
}

bool InstantiatorTheoryUf::isBetterMatch( Node t, Node t1, Node t2 ){
  if( t1==Node::null() ){
    return false;
  }else if( t2==Node::null() ){
    return true;
  }else{
    int neqArgs1 = getNumNeqArgs( t, t1 );
    int neqArgs2 = getNumNeqArgs( t, t2 );
    if( neqArgs1<neqArgs2 ){
      return true;
    }else if( neqArgs1==0 ){
      if( d_does_eind[t][t1] ){
        if( d_does_eind[t][t2] ){
          //check subsume?
        }else{
          //t1 is induced, t2 is not
          return true;
        }
      }
    }
    return false;
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
  if( !d_eind[i][c].d_is_set ){
    d_eind[i][c].d_is_set = true;
    Debug("quant-uf-ematch") << "E-match " << i << " " << c << std::endl;
    if( !areDisequal( i, c ) ){
      if( i.getKind()==INST_CONSTANT ){
        InstMatch m( f, d_instEngine );
        if( !areEqual( i, c ) ){
          m.setMatch( i, getRepresentative( c ) );
        }
        Debug("quant-uf-ematch") << i << " and " << c << " Ematched." << std::endl;
        d_does_eind[i][c] = true;
        d_eq_amb[i][c] = true;
        d_eind[i][c].d_matches.push_back( m );
      }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
        //equality independent, do nothing
        d_does_eind[i][c] = false;
        d_eq_amb[i][c] = false;
        Debug("quant-uf-ematch") << i << " and " << c << " FAILED operators." << std::endl;
      }else{
        Assert( i.getKind()==APPLY_UF && c.getKind()==APPLY_UF );
        Assert( i.getNumChildren()==c.getNumChildren() );
        d_does_eind[i][c] = true;
        d_eq_amb[i][c] = true;
        InstMatch m( f, d_instEngine );
        d_eind[i][c].d_matches.push_back( m );
        for( int j=0; j<(int)c.getNumChildren(); j++ ){
          if( areDisequal( i[j], c[j] ) ){
            Debug("quant-uf-ematch") << i << " and " << c << " FAILED disequal arg. " << j << std::endl;
            d_does_eind[i][c] = false;
            d_eq_amb[i][c] = false;
            d_eind[i][c].clear();
            break;
          }else if( !areEqual( i[j], c[j] ) && d_does_eind[i][c] && !d_eind[i][c].empty() ){
            if( i[j].hasAttribute(InstConstantAttribute()) ){
              Node ca = getRepresentative( c[j] );
              calculateEIndMod( i[j], ca, f );
              if( !d_eind[i][c].merge( d_eind_mod[i[j]][ca] ) ){
                Debug("quant-uf-ematch") << i << " and " << c << " FAILED incompatible match. " << j << std::endl;
                d_does_eind[i][c] = false;
                d_eind[i][c].clear();
              }
            }else{
              Debug("quant-uf-ematch") << i << " and " << c << " FAILED unequal arg." << j << std::endl;
              d_does_eind[i][c] = false;
              d_eind[i][c].clear();
            }
          }
        }
      }
    }else{
      Debug("quant-uf-ematch") << i << " and " << c << " FAILED disequal." << std::endl;
      d_does_eind[i][c] = false;
      d_eq_amb[i][c] = false;
    }
    Assert( d_does_eind.find( i )!=d_does_eind.end() );
    Assert( d_does_eind[i].find( c )!=d_does_eind[i].end() );
    Assert( d_does_eind[i][c] || ( d_eq_amb.find( i )!=d_eq_amb.end() && d_eq_amb[i].find( c )!=d_eq_amb[i].end() ) );
  }
  //std::cout << "<-- " << oi << " " << oc << " " << moduloEq << std::endl;
}

void InstantiatorTheoryUf::calculateEqAmb( Node i, Node c, Node f ){
  if( d_eq_amb.find( i )==d_eq_amb.end() ||
      d_eq_amb[i].find( c )==d_eq_amb[i].end() ){
    if( !areDisequal( i, c ) ){
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
    }else{
      d_eq_amb[i][c] = false;
    }
  }
}

void InstantiatorTheoryUf::calculateEIndMod( Node i, Node c, Node f ){
  Assert( i.getType()==c.getType() );
  Assert( c==getRepresentative( c ) ); 
  if( !d_eind_mod[i][c].d_is_set ){
    d_eind_mod[i][c].d_is_set = true;
    Debug("quant-uf-ematch") << "E-match mod " << i << " " << c << std::endl;
    if( !areDisequal( i, c ) ){
      if( i.getKind()==INST_CONSTANT || d_emap[c].empty() ){
        if( !c.hasAttribute(InstConstantAttribute()) ){
          calculateEInd( i, c, f );
          if( d_does_eind[i][c] ){
            d_eind_mod[i][c].add( d_eind[i][c] );
          }
        }
      }else{
        for( int j=0; j<(int)d_emap[c].size(); j++ ){
          Node ca = d_emap[c][j];
          if( !ca.hasAttribute(InstConstantAttribute()) ){
            calculateEInd( i, ca, f );
            if( d_does_eind[i][ca] ){
              d_eind_mod[i][c].add( d_eind[i][ca] );
            }
          }
        }
        d_eind_mod[i][c].removeRedundant();
      }
    }
  }
}

int InstantiatorTheoryUf::getNumNeqArgs( Node i, Node c ){
  if( d_numEqArg.find( i )==d_numEqArg.end() ||
      d_numEqArg[i].find( c )==d_numEqArg[i].end() ){
    Assert( i.hasAttribute(InstConstantAttribute()) );
    Assert( i.getType()==c.getType() );
    int argsNeq = 0;
    //if matchable, consider all arguments to be equal
    bool matched = false;
    if( !c.hasAttribute(InstConstantAttribute()) ){
      calculateEInd( i, c, i.getAttribute(InstConstantAttribute()) );
      matched = d_does_eind[i][c];
    }
    if( !matched ){
      if( i.getKind()!=INST_CONSTANT ){
        Assert( i.getKind()==APPLY_UF && c.getKind()==APPLY_UF );
        Assert( i.getOperator()==c.getOperator() );
        Assert( i.getNumChildren()==c.getNumChildren() );
        for( int k=0; k<(int)c.getNumChildren(); k++ ){
          if( !areEqual( i[k], c[k] ) ){
            argsNeq++;
          }
        }
      }
    }
    d_numEqArg[i][c] = argsNeq;
    return argsNeq;
  }else{
    return d_numEqArg[i][c];
  }
}

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

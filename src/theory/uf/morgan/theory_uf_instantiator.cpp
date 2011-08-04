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

#include "theory/uf/morgan/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/uf/morgan/theory_uf_morgan.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::uf::morgan;


GMatchNode::GMatchNode( context::Context* c, Node n ) :
d_parents( c ),
d_obligations_eq( c ),
d_obligations_deq( c ),
d_node( n ){
  
}

void GMatchNode::addParent( GMatchNode* g ) { 
  for( GmnList::const_iterator it = d_parents.begin(); it!=d_parents.end(); ++it ){
    if( *it == g ){
      return;
    }
  }
  d_parents.push_back( g ); 
}

void GMatchNode::addObligation( Node n, bool eq ) { 
  if( eq ){
    for( ObList::const_iterator it = d_obligations_eq.begin(); it!=d_obligations_eq.end(); ++it ){
      if( *it == n ){
        return;
      }
    }
    d_obligations_eq.push_back( n ); 
  }else{
    for( ObList::const_iterator it = d_obligations_deq.begin(); it!=d_obligations_deq.end(); ++it ){
      if( *it == n ){
        return;
      }
    }
    d_obligations_deq.push_back( n ); 
  }
}

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
Instantiatior( c, ie ),
d_gmatches( c ),
d_gmatch_size( c ),
d_obligations( c ),
d_th(th),
d_inst_terms( c ),
d_concrete_terms( c ),
d_active_ic( c ),
d_equivalence_class( c ),
d_disequality( c ){
  
  d_numChoices = 0;

  assertDisequal( ((TheoryUFMorgan*)d_th)->d_trueNode, ((TheoryUFMorgan*)d_th)->d_falseNode );
}

Theory* InstantiatorTheoryUf::getTheory() { 
  return d_th; 
}

void InstantiatorTheoryUf::check( Node assertion )
{
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  Debug("quant-uf") << "InstantiatorTheoryUf::check: " << assertion << std::endl;
  switch(assertion.getKind()) {
  case kind::EQUAL:
  case kind::IFF:
    assertEqual(assertion[0], assertion[1]);
    break;
  case kind::APPLY_UF:
    { // assert it's a predicate
      Assert(assertion.getOperator().getType().getRangeType().isBoolean());
      assertEqual(assertion, t->d_trueNode);
    }
    break;
  case kind::NOT:
    if(assertion[0].getKind() == kind::EQUAL ||
       assertion[0].getKind() == kind::IFF) {
      assertDisequal(assertion[0][0], assertion[0][1]);
    } else {
      // negation of a predicate
      Assert(assertion[0].getKind() == kind::APPLY_UF);
      // assert it's a predicate
      Assert(assertion[0].getOperator().getType().getRangeType().isBoolean());
      assertEqual(assertion[0], t->d_falseNode);
    }
    break;
  default:
    Unhandled(assertion.getKind());
  }
}

void InstantiatorTheoryUf::assertEqual( Node a, Node b )
{
  Debug("inst-uf") << "InstantiatorTheoryUf::equal: " << a << " == " << b << std::endl;
  registerTerm( a );
  registerTerm( b );
  addObligation( a, b, true );

  //merge equivalence classes
  initializeEqClass( b );
  NodeList* eqc_b = (*d_equivalence_class.find( b )).second;
  NodeLists::iterator eqc_a_i = d_equivalence_class.find( a );
  if( eqc_a_i!=d_equivalence_class.end() ){
    NodeList* eqc_a = (*eqc_a_i).second;
    for( NodeList::const_iterator i = eqc_a->begin(); i != eqc_a->end(); i++ ) {
      eqc_b->push_back( *i );
    }
  }else{
    eqc_b->push_back( a );
  }

  //merge disequality lists
  NodeLists::iterator d_a_i = d_disequality.find( a );
  if( d_a_i!=d_disequality.end() ){
    NodeList* d_a = (*d_a_i).second;
    initializeDisequalityList( b );
    NodeList* d_b = (*d_disequality.find( b )).second;
    for( NodeList::const_iterator i = d_a->begin(); i != d_a->end(); i++ ) {
      d_b->push_back( *i );
    }
  }
}

void InstantiatorTheoryUf::assertDisequal( Node a, Node b )
{
  Debug("inst-uf") << "InstantiatorTheoryUf::disequal: " << a << " != " << b << std::endl;
  registerTerm( a );
  registerTerm( b );
  addObligation( a, b, false );

  initializeEqClass( a );
  initializeEqClass( b );
  initializeDisequalityList( a );
  NodeList* d_a = (*d_disequality.find( a )).second;
  d_a->push_back( b );
  initializeDisequalityList( b );
  NodeList* d_b = (*d_disequality.find( b )).second;
  d_b->push_back( a );
}

void InstantiatorTheoryUf::registerTerm( Node n )
{
  if( n.hasAttribute(InstantitionConstantAttribute()) ){
    if( d_inst_terms.find( n )==d_inst_terms.end() ){
      //std::vector< EMatchTreeNode* > active;
      //buildEMatchTree( n, active );
      //set instantiation terms
      setInstTerms( n );
      d_inst_terms[n] = true;
    }
  }else{
    setConcreteTerms( n );
    //if( n.getNumChildren()>0 ){
    //  d_concrete_terms[n] = true;
    //}
  }
  if( n.hasAttribute(InstantitionConstantAttribute()) ){
    buildGMatches( n );
  }
}

void InstantiatorTheoryUf::buildGMatches( Node n )
{
  GMatchMap::iterator it = d_gmatches.find( n );
  if( it==d_gmatches.end() ){
    GMatchNode* g = getGMatch( n );
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
        buildGMatches( n[i] );
        getGMatch( n[i] )->addParent( g );
      }
    }
  }
}

GMatchNode* InstantiatorTheoryUf::getGMatch( Node n )
{
  GMatchMap::iterator gm_i = d_gmatches.find( n );
  if( gm_i == d_gmatches.end() ) {
    GMatchNode* g = new GMatchNode( d_th->getContext(), n );
    d_gmatches[n] = g;
    //add to count for the counterexample of its quantifier
    for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
          it !=d_inst_constants.end(); ++it ){
      if( hasInstantiationConstantsFrom( n, it->first ) ){
        IntMap::iterator gms_i = d_gmatch_size.find( it->first );
        if( gms_i==d_gmatch_size.end() ){
          d_gmatch_size[ it->first ] = 0;
        }
        d_gmatch_size[ it->first ] = d_gmatch_size[ it->first ] + 1;
      }
    }
    return g;
  }else{
    return (*gm_i).second;
  }
}

void InstantiatorTheoryUf::addObligation( Node n1, Node n2, bool eq )
{
  if( n1.hasAttribute(InstantitionConstantAttribute()) ){
    getGMatch( n1 )->addObligation( n2, eq );
  }
  if( n2.hasAttribute(InstantitionConstantAttribute()) ){
    getGMatch( n2 )->addObligation( n1, eq );
  }
  if( n1.hasAttribute(InstantitionConstantAttribute()) || n2.hasAttribute(InstantitionConstantAttribute()) ){
    Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
    Node e = NodeManager::currentNM()->mkNode( knd, n1, n2 );
    e = eq ? e : e.notNode();
    for( int i=0; i<2; i++ ){
      Node n = i==0 ? n1 : n2;
      if( n.hasAttribute(InstantitionConstantAttribute()) && 
        ( i==0 || n1.getAttribute(InstantitionConstantAttribute())!=n2.getAttribute(InstantitionConstantAttribute()) ) ){
        for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
              it !=d_inst_constants.end(); ++it ){
          if( hasInstantiationConstantsFrom( n, it->first ) ){
            initializeObligationList( it->first );
            NodeList* ob = (*d_obligations.find( it->first )).second;
            bool found = false;
            for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
              if( *it == e ){
                found = true;
                break;
              }
            }
            if( !found ){
              ob->push_back( e );
            }
          }
        }
      }
    }
  }
}

void InstantiatorTheoryUf::initializeObligationList( Node f ){
  NodeLists::iterator ob_i = d_obligations.find( f );
  if( ob_i==d_obligations.end() ){
    NodeList*ob = new(d_th->getContext()->getCMM()) NodeList(true, d_th->getContext(), false,
                                                            ContextMemoryAllocator<Node>(d_th->getContext()->getCMM()));
    d_obligations.insertDataFromContextMemory( f, ob );
  }
}

void InstantiatorTheoryUf::setInstTerms( Node n ){
  Assert( n.hasAttribute(InstantitionConstantAttribute()) );
  if( n.getKind()==INST_CONSTANT ){
    d_active_ic[ n ] = true;
  }else{
    if( d_inst_terms.find( n )==d_inst_terms.end() ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
          setInstTerms( n[i] );
        }
      }
      //d_inst_terms[n] = true;
    }
  }
}

void InstantiatorTheoryUf::setConcreteTerms( Node n )
{
  if( d_concrete_terms.find( n )==d_concrete_terms.end() ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      setConcreteTerms( n[i] );
    }
    d_concrete_terms[n] = true;
  }
}

Node InstantiatorTheoryUf::getConcreteTerm( Node rep ){
  Assert( !rep.hasAttribute(InstantitionConstantAttribute()) );
  if( rep.getKind()==SKOLEM ){
    std::map< Node, std::vector< Node > >::iterator it = d_emap.find( rep );
    if( it!=d_emap.end() ){
      for( int i=0; i<(int)it->second.size(); i++ ){
        if( !it->second[i].hasAttribute(InstantitionConstantAttribute()) &&
            it->second[i].getKind()!=SKOLEM ){
           return it->second[i];
        }
      }
    }
  }
  return rep;
}


bool InstantiatorTheoryUf::prepareInstantiation()
{
  Debug("quant-uf") << "Search for instantiation for UF:" << std::endl;

  //set all solved to null
  for( std::map< Node, Node >::iterator it = d_solved_ic.begin(); it!=d_solved_ic.end(); ++it ){
    d_solved_ic[ it->first ] = Node::null();
  }

  //find all instantiation constants that are solved
  bool solved = false;
  //d_eq_find.clear();
  //check if any quantifier's instantiation constants have been solved
  for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
      it !=d_inst_constants.end(); ++it ){
    if( d_choice_counter.find( it->first )==d_choice_counter.end() ){
      d_choice_counter[ it->first ] = 1;
      d_numChoices++;
    }
    bool qSolved = true;
    for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
      if( d_solved_ic[ *it2 ]==Node::null() ){
        if( d_active_ic.find( *it2 )!=d_active_ic.end() ){
          Node ns = find( *it2 );
          if( !ns.hasAttribute(InstantitionConstantAttribute()) ){
            //instantiation constant is solved in the current context
            d_solved_ic[ *it2 ] = getConcreteTerm( ns );
          }else{
            qSolved = false;
          }
        }else{
          //Debug("quant-uf") << *it2 << " is not active in this context. " << std::endl;
        }
      }
    }
    if( d_instEngine->getActive( it->first ) && qSolved ){
      Debug("quant-uf") << "Quantifer " << it->first << " is instantiation-ready: " << std::endl;
      for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
        if( d_active_ic.find( *it2 )==d_active_ic.end() ){
          d_solved_ic[ *it2 ] = NodeManager::currentNM()->mkVar( (*it2).getType() ); 
        }
        Debug("quant-uf") << "   " << d_solved_ic[ *it2 ] << std::endl;
      }
      solved = true;
      break;
    }
  }
  if( !solved ){
    Debug("quant-uf") << "No quantifiers are instantiation ready" << std::endl;

    debugPrint();
    refreshMaps();

    d_best = Node::null();
    for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
         it !=d_inst_constants.end(); ++it ){
      if( d_instEngine->getActive( it->first ) ){
        calculateBestMatch( it->first );
      }
    }
    if( d_best!=Node::null() ){
      Debug("quant-uf") << "The most relevant quantifier is " << d_best << std::endl;
      d_choice_counter[d_best]++;
      d_numChoices++;
      for( int j = 0; j<(int)d_inst_constants[ d_best ].size(); j++ ){
        Node i = d_inst_constants[ d_best ][j];
        Debug("quant-uf") << "   ---> Set " << i << " to " << getGMatch( i )->getMatch() << std::endl;
        Assert( getGMatch( i )->getMatch()!=Node::null() );
        d_solved_ic[ i ] = getGMatch( i )->getMatch();
      }
    }
  }

  return false;
}

void InstantiatorTheoryUf::debugPrint()
{
  refreshMaps();

  Debug("quant-uf") << "Instantiation constants:" << std::endl;
  for( BoolMap::const_iterator it = d_active_ic.begin(); it!=d_active_ic.end(); ++it ){
    Debug("quant-uf") << "   " << (*it).first;
    Debug("quant-uf") << "  ->  " << d_solved_ic[(*it).first];
    Debug("quant-uf") << std::endl;
  }
  Debug("quant-uf") << "Instantiation terms:" << std::endl;
  for( BoolMap::const_iterator it = d_inst_terms.begin(); it!=d_inst_terms.end(); ++it ){
    Debug("quant-uf") << "   " << (*it).first;
    //Debug("quant-uf") << "  ->  " << t->find( (*it).first );
    Debug("quant-uf") << std::endl;
  }
  Debug("quant-uf") << "Concrete terms:" << std::endl;
  for( BoolMap::const_iterator it = d_concrete_terms.begin(); it!=d_concrete_terms.end(); ++it ){
    Debug("quant-uf") << "   " << (*it).first;
    //Debug("quant-uf") << "  ->  " << t->find( (*it).first );
    Debug("quant-uf") << std::endl;
  }
  int counter = 1;
  for( std::map< Node, std::vector< Node > >::iterator it = d_emap.begin(); it!=d_emap.end(); ++it ){
    Debug("quant-uf") << "E" << counter << ": { ";
    for( int i = 0; i<(int)it->second.size(); i++ ){
      if( i!=0 ){
        Debug("quant-uf") << ", ";
      }
      Debug("quant-uf") << it->second[i];
    }
    Debug("quant-uf") << " }, disequal : ";
    std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( it->first );
    if( itd!=d_dmap.end() ){
      for( int i = 0; i<(int)itd->second.size(); i++ ){
        if( i!=0 ){
          Debug("quant-uf") << ", ";
        }
        int counter2 = 1;
        std::map< Node, std::vector< Node > >::iterator it4 = d_emap.begin();
        while( it4!=d_emap.end() && !areEqual( it4->first, itd->second[i] ) ){
          ++it4;
          ++counter2;
        }
        if( it4==d_emap.end() ){
          Debug("quant-uf") << find( itd->second[i] );
        }else{
          Debug("quant-uf") << "E" << counter2;
        }
      }
    }
    ++counter;
    Debug("quant-uf") << std::endl;
  }
  Debug("quant-uf") << std::endl;

  //Debug("quant-uf") << "G-matching: " << std::endl;
  //for( GMatchMap::iterator it = d_gmatches.begin(); it!=d_gmatches.end(); ++it ){
  //  GMatchNode* g = (*it).second;
  //  Debug("quant-uf") << (*it).first;
  //  if( g->getNumObligations( true ) + g->getNumObligations( false )>0 ){
  //    Debug("quant-uf") << ", obligations : ";
  //    for( int d=0; d<2; d++ ){
  //      for( int i=0; i<g->getNumObligations( d==0 ); i++ ){
  //        Debug("quant-uf") << (d==0 ? "= " : "!= ") << g->getObligation( i, d==0 ) << " ";
  //      }
  //    }
  //  }
  //  Debug("quant-uf") << std::endl;
  //  for( int i=0; i<g->getNumParents(); i++ ){
  //    Debug("quant-uf") << "   " << g->getParent( i )->getNode() << std::endl;
  //  }
  //}

  Debug("quant-uf") << std::endl;
}

void InstantiatorTheoryUf::initializeEqClass( Node t ) {
  NodeLists::iterator eqc_i = d_equivalence_class.find( t );
  if( eqc_i == d_equivalence_class.end() ) {
    NodeList* eqc = new(d_th->getContext()->getCMM()) NodeList(true, d_th->getContext(), false,
                                                      ContextMemoryAllocator<Node>(d_th->getContext()->getCMM()));
    eqc->push_back( t );
    d_equivalence_class.insertDataFromContextMemory(t, eqc);
  }
}

void InstantiatorTheoryUf::initializeDisequalityList( Node t )
{
  NodeLists::iterator d_i = d_disequality.find( t );
  if( d_i == d_disequality.end() ) {
    NodeList* d = new(d_th->getContext()->getCMM()) NodeList(true, d_th->getContext(), false,
                                                    ContextMemoryAllocator<Node>(d_th->getContext()->getCMM()));
    d_disequality.insertDataFromContextMemory(t, d);
  }
}

void InstantiatorTheoryUf::refreshMaps()
{
  TheoryUFMorgan* t = ((TheoryUFMorgan*)d_th);
  //copy equivalence class, disequality information to temporary map
  d_emap.clear();
  for( NodeLists::iterator ite = d_equivalence_class.begin(); ite!=d_equivalence_class.end(); ++ite ){
    Node n = (*ite).first;
    if( t->find( n )==n ){
      NodeList* el = (*ite).second;
      for( NodeList::const_iterator it = el->begin(); it!=el->end(); ++it ){
        d_emap[n].push_back( *it );
      }
    }
  }
  d_dmap.clear();
  for( NodeLists::iterator itd = d_disequality.begin(); itd!=d_disequality.end(); ++itd ){
    Node n = (*itd).first;
    if( t->find( n )==n ){
      NodeList* dl = (*itd).second;
      for( NodeList::const_iterator it = dl->begin(); it!=dl->end(); ++it ){
        Node dn = t->find( *it );
        if( std::find( d_dmap[n].begin(), d_dmap[n].end(), dn )==d_dmap[n].end() ){
          d_dmap[n].push_back( dn );
        }
      }
    }
  }
}

bool InstantiatorTheoryUf::areEqual( Node a, Node b ){
  return find( a )==find( b );
}

bool InstantiatorTheoryUf::areDisequal( Node a, Node b ){
  a = find( a );
  b = find( b );
  std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( a );
  if( itd!=d_dmap.end() ){
    for( int i=0; i<(int)itd->second.size(); i++ ){
      if( find( itd->second[i] )==b ){
        return true;
      }
    }
  }
  return false;
}

//bool InstantiatorTheoryUf::decideEqual( Node a, Node b )
//{
//  if( !areEqual( a, b ) && !areDisequal( a, b ) ){
//    if( !a.hasAttribute(InstantitionConstantAttribute()) && b.hasAttribute(InstantitionConstantAttribute()) ){
//      Node t = a;
//      a = b;
//      b = t;
//    }
//    a = find( a );
//    b = find( b );
//
//    if( d_emap.find( a )==d_emap.end() ){
//      d_emap[a].push_back( a );
//    }
//    std::map< Node, std::vector< Node > >::iterator ite = d_emap.find( a );
//    for( int i=0; i<(int)ite->second.size(); i++ ){
//      d_emap[b].push_back( ite->second[i] );
//    }
//    d_emap.erase( ite );
//
//    std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( a );
//    if( itd!=d_dmap.end() ){
//      for( int i=0; i<(int)itd->second.size(); i++ ){
//        if( std::find( d_dmap[b].begin(), d_dmap[b].end(), itd->second[i] )==d_dmap[b].end() ){
//          d_dmap[b].push_back( itd->second[i] );
//        }
//      }
//      d_dmap.erase( itd );
//    }
//
//    d_eq_find[a] = b;
//    return true;
//  }else{
//    return false;
//  }
//}

Node InstantiatorTheoryUf::find( Node a ){
  TheoryUFMorgan* t = ((TheoryUFMorgan*)d_th);
  a = t->find( a );
  //while( d_eq_find[a]!=Node::null() ){
  //  a = d_eq_find[a];
  //}
  return a;
}






void InstantiatorTheoryUf::calculateBestMatch( Node f )
{
  d_model.clear();
  d_interior.clear();
  d_failed_suggestions.clear();
  d_matches.clear();
  d_model_req.clear();
  Debug("quant-uf") << "Try to solve for " << f << "." << std::endl;
  //Debug("quant-uf") << "Terms:" << std::endl;
  //for( BoolMap::const_iterator iti = d_inst_terms.begin(); iti!=d_inst_terms.end(); ++iti ){
  //  if( hasInstantiationConstantsFrom( (*iti).first, f ) ){
  //    Debug("quant-uf") << "   " << (*iti).first << std::endl;
  //  }
  //}
  Debug("quant-uf") << "Obligations:" << std::endl;
  initializeObligationList( f );
  NodeList* ob = (*d_obligations.find( f )).second;
  for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
    Debug("quant-uf") << "   " << *it << std::endl;
  }
  std::vector< Node > ce;
  std::vector< GMatchNode* > curr;
  std::map< Node, std::vector< Node > > matches;
  std::vector< GMatchNode* > unmatched;
  for( int j = 0; j<(int)d_inst_constants[f].size(); j++ ){
    Node i = d_inst_constants[f][j];
    curr.push_back( getGMatch( i ) );
    getMatches( getGMatch( i )->getNode() );
    //add all solved instantiation constants to counterexample
    if( d_solved_ic[ i ]!=Node::null() ){
      addToCounterexample( i, d_solved_ic[ i ], f, ce, curr );
    }
  }
  
  while( !curr.empty() ){
    //this used to be (propagate* (refine propagate*)* decide)*
    //now it is (decide refine)*
    if( !decideCounterexample( f, ce, curr ) ){
      unmatched.insert( unmatched.begin(), curr.begin(), curr.end() );
      curr.clear();
    }else{
      refineCounterexample( f, ce, curr );
    }
  }

  int numMatches = ce.size();
  int numDecisions = 0;
  int numTotal = d_gmatch_size[f];
  Debug("quant-uf") << "**** Here are the matches: " << std::endl;
  for( int j = 0; j<(int)d_inst_constants[f].size(); j++ ){
    Node i = d_inst_constants[f][j];
    Debug("quant-uf") << "   " << i << " : " << getGMatch( i )->getMatch() << std::endl;
  }
  Debug("quant-uf") << "The following terms were matched : " << std::endl;
  for( int i=0; i<(int)ce.size(); i++ ){
    Debug("quant-uf") << "   " << ce[i] << " : " << getGMatch( ce[i] )->getMatch() << std::endl;
    if( !d_model[ ce[i] ].empty() ){
      Debug("quant-uf") << "      This required me to assume: " << std::endl;
      for( int j=0; j<(int)d_model[ ce[i] ].size(); j++ ){
        Debug("quant-uf") << "         " << d_model[ ce[i] ][j] << std::endl;
      }
      numDecisions++;
      numMatches--;
    }
  }
  if( !unmatched.empty() ){
    Debug("quant-uf") << "I gave up on fitting these terms into the counterexample: " << std::endl;
    for( int j=0; j<(int)unmatched.size(); j++ ){
      Debug("quant-uf") << "   " << unmatched[j]->getNode() << std::endl;
    }
  }
  int litEntailed = 0;
  int litNEntailed = 0;
  for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
    Node e = (*it).getKind()==NOT ? (*it)[0] : (*it);
    if( (*it).getKind()==NOT ){
      if( areDisequal( e[0], e[1] ) ){
        litEntailed++;
      }else{
        if( areEqual( e[0], e[1] ) ){
          Debug("quant-uf") << "WARNING: Obligation contradicited: " << *it << std::endl;
        }
        litNEntailed++;
      }
    }else{
      if( areEqual( e[0], e[1] ) ){
        litEntailed++;
      }else{
        if( areDisequal( e[0], e[1] ) ){
          Debug("quant-uf") << "WARNING: Obligation contradicited: " << *it << std::endl;
        }
        litNEntailed++;
      }
    }
  }
  //rank how well we did
  double heuristic = double( numMatches + numDecisions*.5 )/double( numTotal );
  Debug("quant-uf") << "**** Here is a summary of the results: " << std::endl;
  Debug("quant-uf") << "     Terms Matched : " << numMatches << std::endl;
  Debug("quant-uf") << "     Terms Decided : " << numDecisions << std::endl;
  Debug("quant-uf") << "    Terms Unsolved : " << (numTotal - ( numMatches + numDecisions ) ) << std::endl;
  Debug("quant-uf") << std::endl;
  Debug("quant-uf") << "     Lits Entailed : " << litEntailed << std::endl;
  Debug("quant-uf") << " Lits not Entailed : " << litNEntailed << std::endl;
  Debug("quant-uf") << "---------------------" << std::endl;
  Debug("quant-uf") << "         Heuristic : " << heuristic << std::endl;
  Debug("quant-uf") << "      Times Chosen : " << d_choice_counter[f] << " / " << d_numChoices << std::endl;
  Debug("quant-uf") << "---------------------" << std::endl;
  heuristic = heuristic*( 1.0 - double( d_choice_counter[f] )/d_numChoices );
  Debug("quant-uf") << "Adjusted Heuristic : " << heuristic << std::endl;
  if( d_best==Node::null() || heuristic>d_heuristic ){
    d_heuristic = heuristic;
    d_best = f;
  }

  Debug("quant-uf") << std::endl;
}

void InstantiatorTheoryUf::addToCounterexample( Node i, Node c, Node f, std::vector< Node >& ce, 
                                                std::vector< GMatchNode* >& curr )
{
  Debug("quant-uf") << "--> Add " << i << " = " << c << " to the counterexample." << std::endl;
  //set the value of the match in the counterexample
  GMatchNode* g = getGMatch( i );
  //set match
  g->setMatch( c );
  //add to counterexample
  ce.push_back( i );
  //add parents to current
  for( int j=0; j<g->getNumParents(); j++ ){
    //Debug("quant-uf") << "--> Add parent " << g->getParent( j )->getNode() << std::endl;
    Assert( std::find( ce.begin(), ce.end(), g->getParent( j )->getNode() )==ce.end() ); 
    Assert( std::find( curr.begin(), curr.end(), g->getParent( j ) )==curr.end() );
    //make sure all arguments for parent are already solved in the counterexample
    Node n = g->getParent( j )->getNode();
    if( hasInstantiationConstantsFrom( n, f ) ){
      bool add = true;
      for( int k=0; k<(int)n.getNumChildren(); k++ ){
        if( hasInstantiationConstantsFrom( n[k], f ) &&
            std::find( ce.begin(), ce.end(), n[k] )==ce.end() ){
          //have not solved for an argument, wait to add this node
          add = false;
          break;
        }
      }
      if( add ){
        curr.push_back( g->getParent( j ) );
        getMatches( n );
      }
    }
  }
  //remove from current
  std::vector< GMatchNode* >::iterator it = std::find( curr.begin(), curr.end(), g );
  Assert( it!=curr.end() );
  curr.erase( it );
  //add residual equalities/disequalities that this necessitates
  for( int j=0; j<(int)d_model_req[i][c].size(); j++ ){
    Node e = d_model_req[i][c][j].getKind()==NOT ? d_model_req[i][c][j][0] : d_model_req[i][c][j];
    Node ir = getValueInCounterexample( e[0], f, ce );
    Node cr = e[1];
    if( ir!=Node::null() &&
        ( ( d_model_req[i][c][j].getKind()==NOT && !areDisequal( ir, cr ) ) ||
          ( d_model_req[i][c][j].getKind()==EQUAL && !areEqual( ir, cr ) ) ) ){
      Kind knd = ir.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
      Node ep = NodeManager::currentNM()->mkNode( knd, ir, cr );
      ep = d_model_req[i][c][j].getKind()==NOT ? ep.notNode() : ep;
      Debug("quant-uf") << "   Model requires: " << ep << std::endl;
      Debug("quant-uf") << "      (Derived from): " << d_model_req[i][c][j] << std::endl;
      d_model[i].push_back( ep );
    }
  }
  //set nodes to be interior
  for( int j=0; j<(int)i.getNumChildren(); j++ ){
    if( hasInstantiationConstantsFrom( i[j], f ) ){
      //Debug("quant-uf") << "   " << i[j] << " is now interior." << std::endl;
      d_interior[ i[j] ] = true;
    }
  }
}

void InstantiatorTheoryUf::removeFromCounterexample( Node i, Node f, std::vector< Node >& ce, 
                                                     std::vector< GMatchNode* >& curr )
{
  Debug("quant-uf") << "<-- Remove " << i << " from counterexample." << std::endl;
  GMatchNode* g = getGMatch( i );
  //set nodes to be interior
  for( int j=0; j<(int)i.getNumChildren(); j++ ){
    if( hasInstantiationConstantsFrom( i[j], f ) ){
      GMatchNode* ga = getGMatch( i[j] );
      d_interior[ i[j] ] = false;
      //if there are no parents in ce
      for( int k=0; k<ga->getNumParents(); k++ ){
        if( g!=ga->getParent( k ) &&
            std::find( ce.begin(), ce.end(), ga->getParent( k )->getNode() )!=ce.end() ){
          d_interior[ i[j] ] = true;
        }
      }
    }
  }
  //clear model
  d_model[i].clear();
  //add to current
  curr.push_back( g );
  //remove parents from current
  for( int j=0; j<g->getNumParents(); j++ ){
    if( hasInstantiationConstantsFrom( g->getParent( j )->getNode(), f ) ){
      //if parent exists in current, erase it
      std::vector< GMatchNode* >::iterator it = std::find( curr.begin(), curr.end(), g->getParent( j ) );
      if( it!=curr.end() ){
        curr.erase( it );
      }
    }
  }
  //remove from counterexample
  std::vector< Node >::iterator it = std::find( ce.begin(), ce.end(), i );
  Assert( it!=ce.end() );
  ce.erase( it );
  //set match
  g->setMatch( Node::null() );
}

Node InstantiatorTheoryUf::getValueInCounterexample( Node i, Node f, std::vector< Node >& ce )
{
  if( !hasInstantiationConstantsFrom( i, f ) ){
    return i;
  }else if( std::find( ce.begin(), ce.end(), i )!=ce.end() ){
    return getGMatch( i )->getMatch();
  }else{
    return Node::null();
  }
}

Node InstantiatorTheoryUf::getValueInCounterexample( Node i, Node f, std::vector< Node >& ce, 
                                                     std::map< Node, Node >& curr_tasks )
{
  if( curr_tasks.find( i )!=curr_tasks.end() ){
    return curr_tasks[i];
  }else{
    return getValueInCounterexample( i, f, ce );
  }
}

bool InstantiatorTheoryUf::isConsistent( Node i, Node c, Node f, std::vector< Node >& ce,
                                         int& numEntailed, int& numNEntailed ){
  for( int j=0; j<(int)d_model_req[i][c].size(); j++ ){
    Node e = d_model_req[i][c][j].getKind()==NOT ? d_model_req[i][c][j][0] : d_model_req[i][c][j];
    Node ir = getValueInCounterexample( e[0], f, ce );
    Node cr = e[1];
    if( ir!=Node::null() ){
      if( ( d_model_req[i][c][j].getKind()==NOT && areEqual( ir, cr ) ) ||
          ( d_model_req[i][c][j].getKind()==EQUAL && areDisequal( ir, cr ) ) ){
        return false;
      }else if( ( d_model_req[i][c][j].getKind()==NOT && areDisequal( ir, cr ) ) ||
                ( d_model_req[i][c][j].getKind()==EQUAL && areEqual( ir, cr ) ) ){
        numEntailed++;
      }else{
        numNEntailed++;
      }
    }
  }
  return true;
}

bool InstantiatorTheoryUf::isConsistent( Node i, Node c, Node f, std::vector< Node >& ce, 
                                         std::map< Node, Node >& curr_tasks,
                                         int& numEntailed, int& numNEntailed ){
  for( int j=0; j<(int)d_model_req[i][c].size(); j++ ){
    Node e = d_model_req[i][c][j].getKind()==NOT ? d_model_req[i][c][j][0] : d_model_req[i][c][j];
    Node ir = getValueInCounterexample( e[0], f, ce, curr_tasks );
    Node cr = e[1];
    if( ir!=Node::null() ){
      if( ( d_model_req[i][c][j].getKind()==NOT && areEqual( ir, cr ) ) ||
          ( d_model_req[i][c][j].getKind()==EQUAL && areDisequal( ir, cr ) ) ){
        return false;
      }else if( ( d_model_req[i][c][j].getKind()==NOT && areDisequal( ir, cr ) ) ||
                ( d_model_req[i][c][j].getKind()==EQUAL && areEqual( ir, cr ) ) ){
        numEntailed++;
      }else{
        numNEntailed++;
      }
    }
  }
  return true;
}


void InstantiatorTheoryUf::propagateCounterexample( Node f, std::vector< Node >& ce, std::vector< GMatchNode* >& curr )
{
  Debug("quant-uf") << "Propagate counterexample." << std::endl;
  bool success = true;
  while( success ){
    success = false;
    for( int j=0; j<(int)curr.size(); j++ ){
      Node i = curr[j]->getNode();
      for( int j = 0; j<(int)d_matches[i].size(); j++ ){
        Node c = d_matches[i][j];
        int numEntailed, numNEntailed;
        if( isConsistent( i, c, f, ce, numEntailed, numNEntailed ) ){
          if( numNEntailed == 0 ){
            Debug("quant-uf") << "Propagate: " << i << " = " << c << std::endl;
            addToCounterexample( i, c, f, ce, curr );
            success = true;
            break;
          }
        }
      }
      if( success ){
        break;
      }
    }
  }
}

bool InstantiatorTheoryUf::refineCounterexample( Node f, std::vector< Node >& ce, std::vector< GMatchNode* >& curr )
{
  Debug("quant-uf") << "Refine counterexample." << std::endl;

  Debug("quant-uf-refine") << "* Current terms to work into counterexample: " << std::endl;
  for( int j=0; j<(int)curr.size(); j++ ){
    Node i = curr[j]->getNode();
    Debug("quant-uf-refine") << "   " << i << ", matches : ";
    for( int k=0; k<(int)d_matches[i].size(); k++ ){
      Debug("quant-uf-refine") << d_matches[i][k] << " ";
    }
    Debug("quant-uf-refine") << std::endl;
  }

  std::vector< Node > cancelling_tasks;
  std::map< Node, Node > curr_tasks;                              //n1 has been requested to change to n2
  std::map< Node, Node > revert_tasks;                            //if in previous map n1 cannot be changed to n2, then change to this
  std::map< Node, std::map< Node, Node > > tasks;                 //n1 is dependent upon these tasks succeeding
  std::map< Node, bool > processing_tasks;
  bool refine = false;

  bool newSuggestion = true;
  while( newSuggestion ){
    newSuggestion = false;

    //for( std::map< Node, Node >::iterator it = curr_tasks.begin(); it!=curr_tasks.end(); ++it ){
    //  Debug("quant-uf-refine") << "Current task : " << it->first << " = " << it->second << std::endl;
    //}

    //check for failed/succeeded tasks
    bool processTask = true;
    while( processTask ){
      processTask = false;
      for( std::map< Node, std::map< Node, Node > >::iterator it = tasks.begin(); it != tasks.end(); ++it ){
        //Debug("quant-uf") << "Check if task for " << it->first << " is finished" << std::endl;
        bool unfinishedSubtask = false;
        bool failedSubtask = false;
        for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
          if( curr_tasks.find( it2->first )!=curr_tasks.end() ){
            unfinishedSubtask = true;
          }else if( std::find( d_failed_suggestions[ it2->first ].begin(), 
                               d_failed_suggestions[ it2->first ].end(), it2->second )!=
                               d_failed_suggestions[ it2->first ].end() ){
            failedSubtask = true;
          }
        }
        if( !unfinishedSubtask ){
          if( failedSubtask ){
            Debug("quant-uf-refine") << "FAIL: The task " << it->first << " = " << curr_tasks[ it->first ];
            Debug("quant-uf-refine") << " has failed due to a subtask failing." << std::endl;
            d_failed_suggestions[ it->first ].push_back( curr_tasks[ it->first ] );
          }
          //check if the changes succeeded 
          Debug("quant-uf-refine") << "Check update/revert for " << it->first << " ";
          Debug("quant-uf-refine") << revert_tasks[it->first] << " " << curr_tasks[it->first] << std::endl;
          bool canRevert = true;
          bool canUpdate = !failedSubtask;
          for( int i=0; i<(int)it->first.getNumChildren(); i++ ){
            if( hasInstantiationConstantsFrom( it->first[i], f ) ){
              Node val = getValueInCounterexample( it->first[i], f, ce );
              if( val==Node::null() ){
                canRevert = false;
                canUpdate = false;
              }else{
                if( areDisequal( val, revert_tasks[ it->first ][i] ) ){
                  canRevert = false;
                }
                if( areDisequal( val, curr_tasks[ it->first ][i] ) ){
                  canUpdate = false;
                }
              }
            }
          }
          if( canUpdate ){
            Debug("quant-uf-refine") << "SUCCESS: The task " << it->first << " = " << curr_tasks[ it->first ];
            Debug("quant-uf-refine") << " has succeeded." << std::endl;
            //update to new value in counterexample
            addToCounterexample( it->first, curr_tasks[ it->first ], f, ce, curr );
            if( curr_tasks[ it->first ]!=revert_tasks[ it->first ] ){
              refine = true;
            }
          }else if( canRevert ){
            Debug("quant-uf-refine") << "Revert " << it->first << " = " << revert_tasks[ it->first ] << std::endl;
            //revert to previous value in counterexample
            addToCounterexample( it->first, revert_tasks[ it->first ], f, ce, curr );
          }else{
            Debug("quant-uf-refine") << "Abandon " << it->first << std::endl;
          }
          curr_tasks.erase( it->first );
          revert_tasks.erase( it->first );
          tasks.erase( it->first );
          processing_tasks.erase( it->first );
          processTask = true;
          break;
        }else if( failedSubtask ){
          ////try to cancel any outstanding tasks
          //for( std::map< Node, std::map< Node, Node > >::iterator it2 = tasks.begin(); it2 != tasks.end(); ++it2 ){
          //  if( curr_tasks.find( it2->first )!=curr_tasks.end() && !processing_tasks[ it2->first ] ){
          //    curr_tasks.erase( it2->first );
          //    revert_tasks.erase( it2->first );
          //    tasks.erase( it2->first );
          //    processing_tasks.erase( it2->first );
          //    --it2;
          //    processTask = true;
          //    break;
          //  }
          //}
        }
      }
    }

    //check if we can process a new task
    for( std::map< Node, Node >::iterator it = curr_tasks.begin(); it!=curr_tasks.end(); ++it ){
      if( !processing_tasks[ it->first ] &&
          ( d_interior.find( it->first )==d_interior.end() || !d_interior[ it->first ] ) ){
        //it->first is on the exterior of the counterexample, try to change to it->second
        Node node = it->first;
        Node nodeTarget = it->second;
        Debug("quant-uf-refine") << "The task " << node << " = " << nodeTarget << " is ready to process." << std::endl;
        removeFromCounterexample( node, f, ce, curr );
        processing_tasks[ node ] = true;
        //check if it is consistent to switch node to nodeTarget
        int numEntailed, numNEntailed;
        if( isConsistent( node, nodeTarget, f, ce, numEntailed, numNEntailed ) ){
          tasks[node].clear();
          if( node.getKind()!=INST_CONSTANT ){
            Assert( node.getNumChildren()==nodeTarget.getNumChildren() );
            for( int j=0; j<(int)node.getNumChildren(); j++ ){
              if( hasInstantiationConstantsFrom( node[j], f ) ){
                if( curr_tasks.find( node[j] )==curr_tasks.end() && !areEqual( nodeTarget[j], getGMatch( node[j] )->getMatch() ) ){
                  curr_tasks[ node[j] ] = nodeTarget[j];
                  revert_tasks[ node[j] ] = getGMatch( node[j] )->getMatch();
                  processing_tasks[ node[j] ] = false;
                  tasks[ node ][ node[j] ] = nodeTarget[j];
                }else{
                  Assert( !areDisequal( curr_tasks[ node[j] ], nodeTarget[j] ) );
                }
              }
            }
          }
        }else{
          Debug("quant-uf-refine") << "FAIL: the task " << node << " = " << nodeTarget << " has failed due to inconsistency." << std::endl;
          d_failed_suggestions[node].push_back( nodeTarget );
          //revert to previous value in counterexample
          addToCounterexample( node, revert_tasks[ node ], f, ce, curr );
        }
        newSuggestion = true;
        break;
      }
    }
    if( !newSuggestion ){
      Debug("quant-uf-refine") << "No tasks are ready to process." << std::endl;
      Node is;
      Node cs;
      if( getSuggestion( is, cs, f, ce, curr, curr_tasks ) ){
        Debug("quant-uf-refine") << "The suggestion " << is << " = " << cs << " has been made." << std::endl;
        curr_tasks[ is ] = cs;
        revert_tasks[ is ] = getGMatch( is )->getMatch();
        processing_tasks[ is ] = false;
        newSuggestion = true;
      }else if( !curr_tasks.empty() ){
        ////consider that all outstanding suggestions have failed
        for( std::map< Node, bool >::iterator it = processing_tasks.begin(); it!=processing_tasks.end(); ++it ){
          if( !it->second && curr_tasks.find( it->first )!=curr_tasks.end() ){
            Debug("quant-uf-refine") << "FAIL: the task " << it->first << " = " << curr_tasks[ it->first ];
            Debug("quant-uf-refine") << " has failed due to no progress begin made." << std::endl;
            curr_tasks.erase( it->first );
            revert_tasks.erase( it->first );
            tasks.erase( it->first );

            newSuggestion = true;
          }
        }
      }
    }
  }
  return refine;
}

bool InstantiatorTheoryUf::getSuggestion( Node& is, Node& cs, Node f, std::vector< Node >& ce, std::vector< GMatchNode* >& curr, 
                                          std::map< Node, Node >& curr_tasks )
{
#if 0
  //DO_THIS
  //first find if there are suggestions from children
  for( std::map< Node, Node >::iterator it = curr_tasks.begin(); it != curr_tasks.end(); ++it ){
    Node ia = it->first;
    Node ca = it->second;
    GMatchNode* g = getGMatch( ia );
    for( int j=0; j<g->getNumParents(); j++ ){
      Node i = g->getParent( j )->getNode();
      //if i is currently set in the counterexample but not in current tasks
      if( curr_tasks.find( i )==curr_tasks.end() && std::find( ce.begin(), ce.end(), i )!=ce.end() ){
        for( int k = 0; k<(int)d_matches[i].size(); k++ ){
          Node c = d_matches[i][k];
          int numEntailed, numNEntailed;
          if( isConsistent( i, c, f, ce, curr_tasks, numEntailed, numNEntailed ) ){
            //if this node would support ia
          }
        }
      }
    }
  }
#endif

  std::map< Node, std::map< Node, std::vector< Node > > > suggests;
  std::map< Node, std::vector< Node > > demands;
  std::map< Node, std::vector< Node > > supports;
  std::map< Node, std::map< Node, std::vector< Node > > > suggests_t;
  std::map< Node, std::vector< Node > > demands_t;
  std::map< Node, std::vector< Node > > supports_t;
  //find if there any suggestions from parents
  for( int j=0; j<(int)curr.size(); j++ ){
    Node i = curr[j]->getNode();
    for( int k = 0; k<(int)d_matches[i].size(); k++ ){
      Node c = d_matches[i][k];

      //Debug("quant-uf-suggest") << "Check if the match " << i << " = " << c << " is consistent " << std::endl;
      int numEntailed, numNEntailed;
      if( isConsistent( i, c, f, ce, curr_tasks, numEntailed, numNEntailed ) ){
        Kind knd = i.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
        Node m = NodeManager::currentNM()->mkNode( knd, i, c );
        for( int r=0; r<(int)d_model_req[i][c].size(); r++ ){
          //Debug("quant-uf-suggest") << "Check " << i << " " << c << " " << d_model_req[i][c][r] << std::endl;
          Node e = d_model_req[i][c][r].getKind()==NOT ? d_model_req[i][c][r][0] : d_model_req[i][c][r];
          Node ir = e[0];
          Node cr = e[1];
          if( d_interior.find( ir )==d_interior.end() || !d_interior[ir] ){
            Node irv = getValueInCounterexample( ir, f, ce, curr_tasks );
            if( hasInstantiationConstantsFrom( ir, f ) && irv!=Node::null() ){
              if( d_model_req[i][c][r].getKind()==NOT ){
                if( areDisequal( irv, cr ) ){
                  //Debug("quant-uf-suggest") << "  " << m << " SUPPORTS: " << ir << " == " << irv << std::endl;
                  supports[ir].push_back( m );
                  if( std::find( supports_t[ir].begin(), supports_t[ir].end(), i )==supports_t[ir].end() ){
                    supports_t[ir].push_back( i );
                  }
                }else{
                  if( areEqual( irv, cr ) ){
                    //Debug("quant-uf-suggest") << "  " << m << " DEMANDS: " << ir << " != " << irv << std::endl;
                    demands[ir].push_back( m );
                    if( std::find( demands_t[ir].begin(), demands_t[ir].end(), i )==demands_t[ir].end() ){
                      demands_t[ir].push_back( i );
                    }
                  }
                  //if it is a disequality, then convert it to a set of equalities
                  std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( find( cr ) );
                  if( itd!=d_dmap.end() ){
                    for( int d=0; d<(int)itd->second.size(); d++ ){
                      Node crp = find( itd->second[d] );
                      //must find all matches ir/crp
                      for( int j=0; j<(int)d_matches[ir].size(); j++ ){
                        if( areEqual( d_matches[ir][j], crp ) ){
                          //Debug("quant-uf-suggest") << "  " << m << " suggests: " << ir << " = " << d_matches[ir][j] << std::endl;
                          suggests[ir][ d_matches[ir][j] ].push_back( m );
                          if( std::find( suggests_t[ir][ d_matches[ir][j] ].begin(), 
                                         suggests_t[ir][ d_matches[ir][j] ].end(), i )==suggests_t[ir][ d_matches[ir][j] ].end() ){
                            suggests_t[ir][ d_matches[ir][j] ].push_back( i );
                          }
                        }
                      }
                    }
                  }
                }
              }else{
                if( areEqual( irv, cr ) ){
                  //Debug("quant-uf-suggest") << "  " << m << " SUPPORTS: " << ir << " == " << irv << std::endl;
                  supports[ir].push_back( m );
                  if( std::find( supports_t[ir].begin(), supports_t[ir].end(), i )==supports_t[ir].end() ){
                    supports_t[ir].push_back( i );
                  }
                }else{
                  if( areDisequal( irv, cr ) ){
                    //Debug("quant-uf-suggest") << "  " << m << " DEMANDS: " << ir << " != " << irv << std::endl;
                    demands[ir].push_back( m );
                    if( std::find( demands_t[ir].begin(), demands_t[ir].end(), i )==demands_t[ir].end() ){
                      demands_t[ir].push_back( i );
                    }
                  }
                  //TODO: must find all matches ir/cr
                  for( int j=0; j<(int)d_matches[ir].size(); j++ ){
                    if( areEqual( d_matches[ir][j], cr ) ){
                      //Debug("quant-uf-suggest") << "  " << m << " suggests: " << ir << " = " << d_matches[ir][j] << std::endl;
                      suggests[ir][ d_matches[ir][j] ].push_back( m );
                      if( std::find( suggests_t[ir][ d_matches[ir][j] ].begin(), 
                                     suggests_t[ir][ d_matches[ir][j] ].end(), i )==suggests_t[ir][ d_matches[ir][j] ].end() ){
                        suggests_t[ir][ d_matches[ir][j] ].push_back( i );
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


  //for( int i=0; i<(int)ce.size(); i++ ){
  //  Debug("quant-uf-suggest") << "Analysis for " << ce[i] << " (current match: " << getGMatch( ce[i] )->getMatch() << "): ";
  //  Debug("quant-uf-suggest") << std::endl;
  //  if( supports.find( ce[i] )!=supports.end() ){
  //    Debug("quant-uf-suggest") << "   Supported by ";
  //    for( int j=0; j<(int)supports[ ce[i] ].size(); j++ ){
  //      if( j!=0 ){
  //        Debug("quant-uf-suggest") << ", ";
  //      }
  //      Debug("quant-uf-suggest") << supports[ ce[i] ][j];
  //    }
  //    Debug("quant-uf-suggest") << std::endl;
  //  }
  //  if( demands.find( ce[i] )!=demands.end() ){
  //    Debug("quant-uf-suggest") << "   Demanded to change by ";
  //    for( int j=0; j<(int)demands[ ce[i] ].size(); j++ ){
  //      if( j!=0 ){
  //        Debug("quant-uf-suggest") << ", ";
  //      }
  //      Debug("quant-uf-suggest") << demands[ ce[i] ][j];
  //    }
  //    Debug("quant-uf-suggest") << std::endl;
  //  }
  //  if( suggests.find( ce[i] )!=suggests.end() ){
  //    Debug("quant-uf-suggest") << "   Suggested to change to: " << std::endl;
  //    for( std::map< Node, std::vector< Node > >::iterator it = suggests[ ce[i] ].begin();
  //      it!=suggests[ ce[i] ].end(); ++it ){
  //      Debug("quant-uf-suggest") << "      " << it->first << ", (by : ";
  //      for( int j=0; j<(int)it->second.size(); j++ ){
  //        if( j!=0 ){
  //          Debug("quant-uf-suggest") << ", ";
  //        }
  //        Debug("quant-uf-suggest") << it->second[j];
  //      }
  //      Debug("quant-uf-suggest") << ")" << std::endl;
  //    }
  //  }
  //}

  for( int i=0; i<(int)ce.size(); i++ ){
    //check if there exists a suggestion t in which every node n that supports ce[i] also suggests t
    //  and at least one n not supporting ce[i] also suggests it
    int numSupport;
    int numSuggest;
    if( d_interior.find( ce[i] )==d_interior.end() || !d_interior[ ce[i] ] ){
      for( std::map< Node, std::vector< Node > >::iterator it = suggests_t[ ce[i] ].begin();
          it!=suggests_t[ ce[i] ].end(); ++it ){
        //if this suggestion has not failed and it has more suggestors than supporters
        if( std::find( d_failed_suggestions[ ce[i] ].begin(), d_failed_suggestions[ ce[i] ].end(), it->first )==
            d_failed_suggestions[ ce[i] ].end() && it->second.size()>supports_t[ ce[i] ].size() ){
          //find if all supporters also suggest
          bool success = true;
          for( int j=0; j<(int)supports_t[ ce[i] ].size(); j++ ){
            if( std::find( it->second.begin(), it->second.end(), supports_t[ ce[i] ][j] )==it->second.end() ){
              success = false;
              break;
            }
          }
          if( success ){
            int tNumSupport = supports_t[ ce[i] ].size();
            int tNumSuggest = it->second.size();
            if( is==Node::null() || tNumSupport<numSupport || 
                ( tNumSupport==numSupport && tNumSuggest>numSuggest ) ){
              is = ce[i];
              cs = it->first;
              numSupport = tNumSupport;
              numSuggest = tNumSuggest;
            }
          }
        }
      }
    }
  }
  return is!=Node::null();
}

bool InstantiatorTheoryUf::decideCounterexample( Node f, std::vector< Node >& ce, std::vector< GMatchNode* >& curr )
{
  //decide one term to match with another, find the best match
  Node best_i;
  Node best_c;
  int best_E, best_nE;
  std::random_shuffle( curr.begin(), curr.end() );
  for( int j=0; j<(int)curr.size(); j++ ){
    Node i = curr[j]->getNode();
    for( int j = 0; j<(int)d_matches[i].size(); j++ ){
      Node c = d_matches[i][j];
      int numEntailed, numNEntailed;
      if( isConsistent( i, c, f, ce, numEntailed, numNEntailed ) ){
        if( best_i==Node::null() || numNEntailed < best_nE || 
            ( numNEntailed==best_nE && numEntailed > best_E ) ){
          best_i = i;
          best_c = c;
          best_E = numEntailed;
          best_nE = numNEntailed;
        }
      }
    }
  }
  if( best_i!=Node::null() ){
    Debug("quant-uf") << "Decide: " << best_i << " = " << best_c << std::endl;
    addToCounterexample( best_i, best_c, f, ce, curr );
    return true;
  }else{
    for( int j=0; j<(int)curr.size(); j++ ){
      Node i = curr[j]->getNode();
      if( i.getKind()==INST_CONSTANT && ce.empty() ){
        Node c = NodeManager::currentNM()->mkVar( i.getType() ); 
        d_concrete_terms[c] = true;
        Debug("quant-uf") << "Decide, fresh constant: " << i << " = " << c << std::endl;
        addToCounterexample( i, c, f, ce, curr );
        return true;
      }
    }
    return false;
  }
}

void InstantiatorTheoryUf::getMatches( Node i )
{
  if( d_matches.find( i )==d_matches.end() ){
    for( BoolMap::const_iterator itc = d_concrete_terms.begin(); itc!=d_concrete_terms.end(); ++itc ){
      Node c = (*itc).first;
      if( i.getType()==c.getType() && ( i.getKind()!=INST_CONSTANT || find( c )==c ) &&
          !areDisequal( i, c ) ){
        //Debug("quant-uf") << "Get model requirements for " << i << " " << c << std::endl;
        bool success = true;
        if( i.getKind()!=INST_CONSTANT && 
            ( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ) ){
          success = false;
        }else{
          if( !areEqual( i, c ) ){
            d_model_req[i][c].clear();
            GMatchNode* g = getGMatch( i );
            for( int d=0; d<2; d++ ){
              for( int j=0; j<g->getNumObligations( d==0 ); j++ ){
                Node b = g->getObligation( j, d==0 );
                if( ( d==0 && areDisequal( b, c ) ) || ( d==1 && areEqual( b, c ) ) ){
                  success = false;
                }else if( ( d==0 && !areEqual( b, c ) ) || ( d==1 && !areDisequal( b, c ) ) ){
                  Kind knd = i.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
                  Node e = NodeManager::currentNM()->mkNode( knd, b, c );
                  //Debug("quant-uf") << "  R " << e << std::endl;
                  d_model_req[i][c].push_back( d==0 ? e : e.notNode() );
                }
              }
            }
          }
          if( i.getKind()!=INST_CONSTANT ){
            Assert( i.getNumChildren()==c.getNumChildren() );
            for( int j=0; j<(int)i.getNumChildren(); j++ ){
              if( areDisequal( i[j], c[j] ) ){
                success = false;
                break;
              }else if( !areEqual( i[j], c[j] ) ){
                Kind knd = i[j].getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
                Node e = NodeManager::currentNM()->mkNode( knd, i[j], c[j] );
                //Debug("quant-uf") << "  Rarg " << e << std::endl;
                d_model_req[i][c].push_back( e );
              }
            }
          }
        }
        if( success ){
          d_matches[i].push_back( c );
        }else{
          d_model_req[i].erase( c );
        }
      }
    }
    std::random_shuffle( d_matches[i].begin(), d_matches[i].end() );
  }
}

bool InstantiatorTheoryUf::hasInstantiationConstantsFrom( Node i, Node f )
{
  //DO_THIS
  return i.getAttribute(InstantitionConstantAttribute())==f;
}

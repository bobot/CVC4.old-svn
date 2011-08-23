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


GMatchNode::GMatchNode( context::Context* c, Node n ) :
d_parents( c ),
d_obligations( c ),
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

void GMatchNode::addObligation( Node n ) { 
  for( ObList::const_iterator it = d_obligations.begin(); it!=d_obligations.end(); ++it ){
    if( *it == n ){
      return;
    }
  }
  d_obligations.push_back( n ); 
}

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie ),
d_gmatches( c ),
d_gmatch_size( c ),
d_obligations( c ),
d_th(th),
d_inst_terms( c ),
d_concrete_terms( c ),
d_active_ic( c ),
d_equivalence_class( c ),
d_is_rep( c ),
d_disequality( c )
{
  
  d_numChoices = 0;

  d_is_rep[ ((TheoryUF*)d_th)->d_true ] = true;
  d_is_rep[ ((TheoryUF*)d_th)->d_false ] = true;
  initializeEqClass( ((TheoryUF*)d_th)->d_true );
  initializeEqClass( ((TheoryUF*)d_th)->d_false );
  initializeDisequalityList( ((TheoryUF*)d_th)->d_true );
  initializeDisequalityList( ((TheoryUF*)d_th)->d_false );
  (*d_disequality.find( ((TheoryUF*)d_th)->d_true )).second->push_back( ((TheoryUF*)d_th)->d_false );
  (*d_disequality.find( ((TheoryUF*)d_th)->d_false )).second->push_back( ((TheoryUF*)d_th)->d_true );
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
  Assert( ( a.getKind()==EQUAL && b==((TheoryUF*)d_th)->d_false ) ||
          ( a.getKind()!=EQUAL && b.getKind()!=EQUAL ) );

  Debug("inst-uf") << "InstantiatorTheoryUf::equal: " << a << " == " << b << std::endl;
  registerTerm( a );
  registerTerm( b );
  addObligation( a, b );

  //Node sym;
  //if( a.getKind()==EQUAL && !a.hasAttribute(InstantitionConstantAttribute()) ){
  //  Kind knd = a[0].getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  //  sym =  NodeManager::currentNM()->mkNode( knd, a[1], a[0] );
  //  registerTerm( sym );
  //}

  //merge equivalence classes
  Node c = getRepresentative( a );
  initializeEqClass( c );
  NodeList* eqc_c = (*d_equivalence_class.find( c )).second;
  initializeDisequalityList( c );
  NodeList* d_c = (*d_disequality.find( c )).second;
  for( int i=0; i<2; i++ ){
    Node d = i==0 ? a : b;
    if( c!=d ){
      BoolMap::iterator isr_d_i = d_is_rep.find( d );
      if( isr_d_i!=d_is_rep.end() ){
        if( (*isr_d_i).second ){
          //add equalities
          NodeLists::iterator eqc_d_i = d_equivalence_class.find( d );
          NodeList* eqc_d = (*eqc_d_i).second;
          for( NodeList::const_iterator i = eqc_d->begin(); i != eqc_d->end(); i++ ) {
            eqc_c->push_back( *i );
          }
          //add disequalities
          NodeLists::iterator d_d_i = d_disequality.find( d );
          if( d_d_i!=d_disequality.end() ){
            NodeList* d_d = (*d_d_i).second;
            for( NodeList::const_iterator i = d_d->begin(); i != d_d->end(); i++ ) {
              d_c->push_back( *i );
            }
          }
        }
      }else{
        eqc_c->push_back( d );
      }
    }
  }
  //add disequality
  if( a.getKind()==EQUAL ){
    Node c1 = getRepresentative( a[0] );
    Node c2 = getRepresentative( a[1] );

    initializeDisequalityList( c1 );
    NodeList* d_c1 = (*d_disequality.find( c1 )).second;
    d_c1->push_back( c2 );

    initializeDisequalityList( c2 );
    NodeList* d_c2 = (*d_disequality.find( c2 )).second;
    d_c2->push_back( c1 );
  }

  d_is_rep[ a ] = false;
  d_is_rep[ b ] = false;
  d_is_rep[ c ] = true;
}

void InstantiatorTheoryUf::registerTerm( Node n )
{
  if( n.hasAttribute(InstantitionConstantAttribute()) ){
    if( d_inst_terms.find( n )==d_inst_terms.end() ){
      //std::vector< EMatchTreeNode* > active;
      //buildEMatchTree( n, active );
      //set instantiation terms
      setInstTerms( n );
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

void InstantiatorTheoryUf::addObligation( Node n1, Node n2 )
{
  if( n1.hasAttribute(InstantitionConstantAttribute()) ){
    getGMatch( n1 )->addObligation( n2 );
  }
  if( n2.hasAttribute(InstantitionConstantAttribute()) ){
    getGMatch( n2 )->addObligation( n1 );
  }
  if( n1.hasAttribute(InstantitionConstantAttribute()) || n2.hasAttribute(InstantitionConstantAttribute()) ){
    Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
    Node e = NodeManager::currentNM()->mkNode( knd, n1, n2 );
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
    d_inst_terms[n] = true;
  }else{
    if( d_inst_terms.find( n )==d_inst_terms.end() ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
          setInstTerms( n[i] );
        }
      }
      d_inst_terms[n] = true;
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
  Node ns = getRepresentative( rep );
  if( !ns.hasAttribute(InstantitionConstantAttribute()) ){
    return ns;
  }else{
    NodeLists::iterator eqc_ns_i = d_equivalence_class.find( ns );
    if( eqc_ns_i!=d_equivalence_class.end() ){
      NodeList* eqc_ns = (*eqc_ns_i).second;
      for( NodeList::const_iterator it = eqc_ns->begin(); it != eqc_ns->end(); ++it ){
        if( !(*it).hasAttribute(InstantitionConstantAttribute()) ){
          return *it;
        }
      }
    }
    return Node::null();
  }
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
    if( d_instEngine->getActive( it->first ) ){
      if( d_choice_counter.find( it->first )==d_choice_counter.end() ){
        d_choice_counter[ it->first ] = 1;
        d_numChoices++;
      }
      solved = true;
      for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
        if( d_solved_ic[ *it2 ]==Node::null() ){
          if( d_active_ic.find( *it2 )!=d_active_ic.end() ){
            Node ns = getConcreteTerm( *it2 );
            if( ns!=Node::null() ){
              Assert( !ns.hasAttribute(InstantitionConstantAttribute())  );
              //instantiation constant is solved in the current context
              d_solved_ic[ *it2 ] = ns;
            }else{
              solved = false;
            }
          }else{
            //Debug("quant-uf") << "UF: " << *it2 << " is not active in this context. " << std::endl;
          }
        }
      }
      if( solved ){
        Debug("quant-uf") << "UF: Quantifer " << it->first << " is instantiation-ready: " << std::endl;
        for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
          if( d_active_ic.find( *it2 )==d_active_ic.end() ){
            d_solved_ic[ *it2 ] = NodeManager::currentNM()->mkVar( (*it2).getType() ); 
          }
          Debug("quant-uf") << "   " << d_solved_ic[ *it2 ] << std::endl;
        }
        break;
      }
    }
  }
  if( !solved ){
    Debug("quant-uf") << "UF: No quantifiers are instantiation ready" << std::endl;

    debugPrint();
    refreshMaps();

    d_best = Node::null();
    d_heuristic = -1.0;
    for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
         it !=d_inst_constants.end(); ++it ){
      if( d_instEngine->getActive( it->first ) ){
        calculateBestMatch( it->first );
      }
    }
    if( d_best!=Node::null() ){
      Debug("quant-uf") << "UF: The most relevant quantifier is " << d_best << std::endl;
      d_choice_counter[d_best]++;
      d_numChoices++;
      for( int j = 0; j<(int)d_inst_constants[ d_best ].size(); j++ ){
        Node i = d_inst_constants[ d_best ][j];
        Debug("quant-uf") << "   ---> Set " << i << " to " << d_matches[i] << std::endl;
        Assert( d_matches[i]!=Node::null() );
        d_solved_ic[ i ] = d_matches[i];
      }
      exit( -1 );
      return true;
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
    //Debug("quant-uf") << "  ->  " << d_solved_ic[(*it).first];
    Debug("quant-uf") << std::endl;
  }
  Debug("quant-uf") << "Instantiation terms:" << std::endl;
  for( BoolMap::const_iterator it = d_inst_terms.begin(); it!=d_inst_terms.end(); ++it ){
    Debug("quant-uf") << "   " << (*it).first;
    //Debug("quant-uf") << "  ->  " << getRepresentative( (*it).first );
    Debug("quant-uf") << std::endl;
  }
  Debug("quant-uf") << "Concrete terms:" << std::endl;
  for( BoolMap::const_iterator it = d_concrete_terms.begin(); it!=d_concrete_terms.end(); ++it ){
    Debug("quant-uf") << "   " << (*it).first;
    //Debug("quant-uf") << "  ->  " << getRepresentative( (*it).first );
    Debug("quant-uf") << std::endl;
  }
  Debug("quant-uf") << "Equalivalence classes:" << std::endl;
  int counter = 1;
  for( std::map< Node, std::vector< Node > >::iterator it = d_emap.begin(); it!=d_emap.end(); ++it ){
    Debug("quant-uf") << "E" << counter << ": { ";
    for( int i = 0; i<(int)it->second.size(); i++ ){
      if( i!=0 ){
        Debug("quant-uf") << ", ";
      }
      Debug("quant-uf") << it->second[i];
    }
    Debug("quant-uf") << " }";
    Debug("quant-uf") << ", disequal : ";
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
          Debug("quant-uf") << getRepresentative( itd->second[i] );
        }else{
          Debug("quant-uf") << "E" << counter2;
        }
      }
    }
    ++counter;
    Debug("quant-uf") << std::endl;
  }
  Debug("quant-uf") << std::endl;

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
  //copy equivalence class, disequality information to temporary map
  d_emap.clear();
  for( NodeLists::iterator ite = d_equivalence_class.begin(); ite!=d_equivalence_class.end(); ++ite ){
    Node n = (*ite).first;
    if( getRepresentative( n )==n ){
      NodeList* el = (*ite).second;
      for( NodeList::const_iterator it = el->begin(); it!=el->end(); ++it ){
        d_emap[n].push_back( *it );
      }
    }
  }
  d_dmap.clear();
  for( NodeLists::iterator itd = d_disequality.begin(); itd!=d_disequality.end(); ++itd ){
    Node n = (*itd).first;
    if( getRepresentative( n )==n ){
      NodeList* dl = (*itd).second;
      for( NodeList::const_iterator it = dl->begin(); it!=dl->end(); ++it ){
        d_dmap[n].push_back( *it );
      }
    }
  }
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
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.getRepresentative( a );
  }else{
    return a;
  }
}

bool InstantiatorTheoryUf::hasInstantiationConstantsFrom( Node i, Node f )
{
  //DO_THIS
  return i.getAttribute(InstantitionConstantAttribute())==f;
}

//bool InstantiatorTheoryUf::decideEqual( Node a, Node b )
//{
//  if( !areEqual( a, b ) && !areDisequal( a, b ) ){
//    if( !a.hasAttribute(InstantitionConstantAttribute()) && b.hasAttribute(InstantitionConstantAttribute()) ){
//      Node t = a;
//      a = b;
//      b = t;
//    }
//    a = getRepresentative( a );
//    b = getRepresentative( b );
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



void InstantiatorTheoryUf::calculateBestMatch( Node f )
{
  d_ematch.clear();
  d_ematch_mod.clear();
  d_does_ematch.clear();

  Debug("quant-uf") << "Try to solve for " << f << "." << std::endl;
  //Debug("quant-uf") << "Terms:" << std::endl;
  //for( BoolMap::const_iterator iti = d_inst_terms.begin(); iti!=d_inst_terms.end(); ++iti ){
  //  if( hasInstantiationConstantsFrom( (*iti).first, f ) ){
  //    Debug("quant-uf") << "   " << (*iti).first << std::endl;
  //  }
  //}
  std::vector< Node > curr_terms;
  std::map< Node, bool > terms_processed;
  Debug("quant-uf") << "Obligations:" << std::endl;
  initializeObligationList( f );
  NodeList* ob = (*d_obligations.find( f )).second;
  for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
    Debug("quant-uf") << "   " << *it << std::endl;
    for( int i=0; i<2; i++ ){
      if( hasInstantiationConstantsFrom( (*it)[i], f ) ){
        curr_terms.push_back( (*it)[i] );
      }
    }
  }
  std::random_shuffle( curr_terms.begin(), curr_terms.end() );

  std::vector< std::map< Node, Node > > curr_matches;
  std::map< Node, Node > final_matches;
  std::vector< Node >::iterator term_it = curr_terms.begin();
  bool checkEq = true;
  int level = 0;
  bool success = false;
  while( !success ){
    if( addToEMatching( curr_matches, *term_it, f, checkEq ) ){
      //check if some match has all instantiation constants
      for( int i=0; i<(int)curr_matches.size(); i++ ){
        if( curr_matches[i].size()==d_inst_constants[f].size() ){
          success = true;
          for( std::map< Node, Node >::iterator it = curr_matches[i].begin(); 
                it != curr_matches[i].end(); ++it ){
            final_matches[ it->first ] = it->second;
          }
        }
      }
    }
    ++term_it;
    if( term_it==curr_terms.end() ){
      if( !checkEq ){
        //break into subterms
        Debug("quant-uf") << "Breaking into sub-terms..." << std::endl;
        std::vector< Node > newTerms;
        for( std::vector< Node >::iterator it = curr_terms.begin(); it != curr_terms.end(); ++it ){
          Node i = *it;
          if( i.getKind()==INST_CONSTANT ){
            Node c = NodeManager::currentNM()->mkVar( i.getType() ); 
            d_concrete_terms[c] = true;
            Debug("quant-uf") << "Match, fresh constant: " << i << " = " << c << std::endl;
            for( int j=0; j<(int)curr_matches.size(); j++ ){
              if( curr_matches[j].find( i )==curr_matches[j].end() ){
                curr_matches[ j ][ i ] = c;
              }
            }
          }else{
            for( int j=0; j<(int)i.getNumChildren(); j++ ){
              if( hasInstantiationConstantsFrom( i[j], f ) && 
                  terms_processed.find( i[j] )==terms_processed.end() &&
                  std::find( newTerms.begin(), newTerms.end(), i[j] )==newTerms.end() ){
                newTerms.push_back( i[j] );
              }
            }
          }
          terms_processed[ i ] = true;
        }
        curr_terms.clear();
        curr_terms.insert( curr_terms.begin(), newTerms.begin(), newTerms.end() );
        level++;
      }
      term_it = curr_terms.begin();
      checkEq = !checkEq;
    }
  }
  Debug("quant-uf") << "Produced the following E-match: " << std::endl;
  for( std::map< Node, Node >::iterator it = final_matches.begin(); it != final_matches.end(); ++it ){
    Debug("quant-uf") << it->first << " -> " << it->second << std::endl;
    d_matches[ it->first ] = it->second;
  }
  //rank quality?
  //double heuristic;
  double heur = 1.0/double( level );
  heur *= double(d_choice_counter[f])/double(d_numChoices);
  if( heur>d_heuristic ){
    d_heuristic = heur;
    d_matches.clear();
    d_best = f;
    for( std::map< Node, Node >::iterator it = final_matches.begin(); it != final_matches.end(); ++it ){
      d_matches[ it->first ] = it->second;
    }
  }
  
  Debug("quant-uf") << std::endl;
}


bool InstantiatorTheoryUf::addToEMatching( std::vector< std::map< Node, Node > >& curr_matches, Node i, Node f, bool onlyCheckEq ){
  if( onlyCheckEq ){
    Node r = getRepresentative( i );
    std::map< Node, std::vector< Node > >::iterator itr = d_emap.find( r );
    for( int j=0; j<(int)itr->second.size(); j++ ){
      if( !itr->second[j].hasAttribute(InstantitionConstantAttribute()) ){
        doEMatching( i, itr->second[j], f, false );
        if( d_does_ematch[ i ][ itr->second[j] ] ){
          //try to merge with curr_matches
          if( mergeMatch( curr_matches, d_ematch[ i ][ itr->second[j] ] ) ){
            Debug("quant-uf") << i << " = " << itr->second[j] << " was added to E-match." << std::endl;
            return true;
          }
        }
      }
    }
    return false;
  }else{
    for( BoolMap::const_iterator it = d_concrete_terms.begin(); it!=d_concrete_terms.end(); ++it ){
      if( i.getType()==(*it).first.getType() && !areEqual( i, (*it).first ) ){    //already handled for onlyCheckEq = true
        doEMatching( i, (*it).first, f, false );
        if( d_does_ematch[ i ][ (*it).first ] ){
          //try to merge with curr_matches
          if( mergeMatch( curr_matches, d_ematch[ i ][ (*it).first ] ) ){
            //if so, consider the equivalence classes merged (and reset E-matches?) DO_THIS
            Debug("quant-uf") << i << " and " << (*it).first << " were added to E-match." << std::endl;
            return true;
          }
        }
      }
    }
    return false;
  }
}

void InstantiatorTheoryUf::doEMatching( Node i, Node c, Node f, bool moduloEq )
{
  if( !areDisequal( i, c ) ){
    //modulo equality
    if( moduloEq ){
      i = getRepresentative( i );
      c = getRepresentative( c );
      if( d_ematch_mod.find( i )==d_ematch_mod.end() ||
          d_ematch_mod[i].find( c )==d_ematch_mod[i].end() ){
        if( d_emap[i].empty() ){
          d_emap[i].push_back( i );
        }
        if( d_emap[c].empty() ){
          d_emap[c].push_back( c );
        }
        d_ematch_mod[i][c] = std::vector< std::map< Node, Node > >();
        std::map< Node, std::vector< Node > >::iterator iti = d_emap.find( i );
        std::map< Node, std::vector< Node > >::iterator itc = d_emap.find( c );
        for( int j=0; j<(int)iti->second.size(); j++ ){
          for( int k=0; k<(int)itc->second.size(); k++ ){
            Node i1;
            Node c1;
            if( iti->second[j].getAttribute(InstantitionConstantAttribute())==f &&
                !itc->second[k].hasAttribute(InstantitionConstantAttribute()) ){
              i1 = iti->second[j];
              c1 = itc->second[k];
            }else if( itc->second[k].getAttribute(InstantitionConstantAttribute())==f &&
                      !iti->second[j].hasAttribute(InstantitionConstantAttribute()) ){
              i1 = itc->second[k];
              c1 = iti->second[j];
            }
            if( i1!=Node::null() &&
                ( i1.getKind()!=INST_CONSTANT || getRepresentative( c1 )==c1 ) ){
              doEMatching( i1, c1, f, false );
              d_ematch_mod[i][c].insert( d_ematch_mod[i][c].begin(), d_ematch[i1][c1].begin(), d_ematch[i1][c1].end() );
            }
          }
        }
        removeRedundant( d_ematch_mod[i][c] );
      }
    }else{
      Assert( i.getAttribute(InstantitionConstantAttribute())==f && !c.hasAttribute(InstantitionConstantAttribute()) );
      //if not already generated
      if( d_does_ematch.find( i )==d_does_ematch.end() || d_does_ematch[i].find( c )==d_does_ematch[i].end() ){
        if( i.getKind()==INST_CONSTANT ){
          if( areDisequal( i, c ) ){
            d_does_ematch[i][c] = false;
          }else{
            d_ematch[i][c].push_back( std::map< Node, Node >() );
            if( !areEqual( i, c ) ){
              d_ematch[i][c][0][i] = getRepresentative( c );
            }
            d_does_ematch[i][c] = true;
          }
        }else if( i.getKind()==EQUAL ){
          if( c.getKind()!=EQUAL || i[0].getType()!=c[0].getType() ){
            d_does_ematch[i][c] = false;
          }else{
            //check both ways
            bool foundMatch = false;
            std::vector< std::map< Node, Node > > matches;
            for( int s=0; s<2; s++ ){
              Node c1 = s==0 ? c[0] : c[1];
              Node c2 = s==0 ? c[1] : c[0];
              doEMatching( i[0], c1, f, true );
              doEMatching( i[1], c2, f, true );
              if( d_does_ematch[i[0]][c1] && d_does_ematch[i[1]][c2] ){
                if( mergeMatch( matches, d_ematch_mod[i[0]][c1] ) &&
                    mergeMatch( matches, d_ematch_mod[i[1]][c2] ) ){
                  foundMatch = true;
                }
              }
            }
            if( foundMatch ){
              d_does_ematch[i][c] = true;
              d_ematch[i][c].insert( d_ematch[i][c].begin(), matches.begin(), matches.end() );
            }else{
              d_does_ematch[i][c] = false;
            }
          }
        }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
          //equality independent, do nothing
          d_does_ematch[i][c] = false;
        }else{
          Assert( i.getNumChildren()==c.getNumChildren() );
          d_does_ematch[i][c] = true;
          for( int j=0; j<(int)c.getNumChildren(); j++ ){
            if( areDisequal( i[j], c[j] ) ){
              d_does_ematch[i][c] = false;
              return;
            }
          }
          std::vector< std::map< Node, Node > > matches;
          for( int j=0; j<(int)c.getNumChildren(); j++ ){
            if( !areEqual( i[j], c[j] ) ){
              doEMatching( i[j], c[j], f, true );
              if( !d_does_ematch[i][c] || !mergeMatch( matches, d_ematch_mod[i[j]][c[j]] ) ){
                d_does_ematch[i][c] = false;
                //there exists no matches, or in other words, i and c do not E-match
                return;
              }
            }
          }
          d_does_ematch[i][c] = true;
          d_ematch[i][c].insert( d_ematch[i][c].begin(), matches.begin(), matches.end() );
        }
      }
    }
  }else{
    d_does_ematch[i][c] = false;
  }
}

bool InstantiatorTheoryUf::mergeMatch( std::vector< std::map< Node, Node > >& target,
                                       std::vector< std::map< Node, Node > >& matches )
{
  if( target.empty() ){
    target.insert( target.begin(), matches.begin(), matches.end() );
    return true;
  }else{
    std::vector< std::map< Node, Node > > newMatches;
    std::vector< std::map< Node, Node > > tempMatches;
    tempMatches.insert( tempMatches.begin(), target.begin(), target.end() );
    for( int k=0; k<(int)matches.size(); k++ ){
      for( int l=0; l<(int)tempMatches.size(); l++ ){
        if( mergeMatch( tempMatches[l], matches[k] ) ){
          newMatches.push_back( tempMatches[l] );
        }
      }
    }
    if( newMatches.size()>0 ){
      target.clear();
      target.insert( target.begin(), newMatches.begin(), newMatches.end() );
      removeRedundant( target );
      return true;
    }else{
      return false;
    }
  }
}

bool InstantiatorTheoryUf::mergeMatch( std::map< Node, Node >& target, std::map< Node, Node >& matches ){
  for( std::map< Node, Node >::iterator it = matches.begin(); it!=matches.end(); ++it ){
    if( target.find( it->first )!=target.end() ){
      if( target[it->first]!=it->second ){
        return false;
      }
    }else{
      target[ it->first ] = it->second;
    }
  }
  return true;
}

int InstantiatorTheoryUf::numMatches( std::vector< std::map< Node, Node > >& m1, std::vector< std::map< Node, Node > >& m2 )
{
  std::vector< std::map< Node, Node > > m3;
  m3.insert( m3.begin(), m1.begin(), m1.end() );
  mergeMatch( m3, m2 );
  return (int)m3.size();
}

void InstantiatorTheoryUf::removeRedundant( std::vector< std::map< Node, Node > >& matches ){
  std::vector< bool > active;
  active.resize( matches.size(), true );
  for( int k=0; k<(int)matches.size(); k++ ){
    for( int l=(k+1); l<(int)matches.size(); l++ ){
      if( k!=l && active[k] && active[l] ){
        int result = checkSubsume( matches[k], matches[l] );
        if( result==1 ){
          active[k] = false;
        }else if( result==-1 ){
          active[l] = false;
        }
      }
    }
  }
  std::vector< std::map< Node, Node > > temp;
  temp.insert( temp.begin(), matches.begin(), matches.end() );
  matches.clear();
  for( int i=0; i<(int)temp.size(); i++ ){
    if( active[i] ){
      matches.push_back( temp[i] );
    }
  }
}

int InstantiatorTheoryUf::checkSubsume( std::map< Node, Node >& m1, std::map< Node, Node >& m2 ){
  bool nsubset1 = true;
  bool nsubset2 = true;
  for( std::map< Node, Node >::iterator it = m1.begin(); it!=m1.end(); ++it ){
    if( m2.find( it->first )==m2.end() || m2[ it->first ]!=it->second ){
      nsubset1 = false;
      break;
    }
  }
  for( std::map< Node, Node >::iterator it = m2.begin(); it!=m2.end(); ++it ){
    if( m1.find( it->first )==m1.end() || m1[ it->first ]!=it->second ){
      nsubset2 = false;
      break;
    }
  }
  if( nsubset1 ){
    return -1;
  }else if( nsubset2 ){
    return 1;
  }else{
    return 0;
  }
}

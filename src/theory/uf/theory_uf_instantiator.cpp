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
d_inst_terms( c ),
d_concrete_terms( c ),
d_active_ic( c ),
d_equivalence_class( c ),
d_is_rep( c ),
d_disequality( c )
//d_ematch_done( c )
{

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
  Assert( ( ( a.getKind()==EQUAL || a.getKind()==IFF ) && b==((TheoryUF*)d_th)->d_false ) ||
          ( a.getKind()!=EQUAL && a.getKind()!=IFF && b.getKind()!=EQUAL && b.getKind()!=IFF ) );

  Debug("inst-uf") << "InstantiatorTheoryUf::equal: " << a << " == " << b << std::endl;
  registerTerm( a );
  registerTerm( b );
  if( a.hasAttribute(InstantitionConstantAttribute()) || b.hasAttribute(InstantitionConstantAttribute()) ){
    //add to obligation list
    Node formula;
    Node f;
    if( a.hasAttribute(InstantitionConstantAttribute()) ){
      f = a.getAttribute(InstantitionConstantAttribute());
      Kind knd = a.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
      formula = NodeManager::currentNM()->mkNode( knd, a, b );
    }else if( b.hasAttribute(InstantitionConstantAttribute()) ){
      f = b.getAttribute(InstantitionConstantAttribute());
      //swap sides
      Kind knd = a.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
      formula = NodeManager::currentNM()->mkNode( knd, b, a );
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
  if( a.getKind()==EQUAL || a.getKind()==IFF ){
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
  bool recurse = false;
  if( n.hasAttribute(InstantitionConstantAttribute()) ){
    if( d_inst_terms.find( n )==d_inst_terms.end() ){
      d_inst_terms[n] = true;
      recurse = true;
    }
    //buildSubTerms( n );
  }else{
    if( d_concrete_terms.find( n )==d_concrete_terms.end() ){
      d_concrete_terms[n] = true;
      recurse = true;
    }
  }
  if( recurse ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerTerm( n[i] );
    }
  }
}

//void InstantiatorTheoryUf::buildSubTerms( Node n )
//{
//  SubTermMap::iterator it = d_subterms.find( n );
//  if( it==d_subterms.end() ){
//    SubTermNode* g = getSubTerm( n );
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
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
//  Assert( n.hasAttribute(InstantitionConstantAttribute()) );
//  if( n.getKind()==INST_CONSTANT ){
//    d_active_ic[ n ] = true;
//  }else{
//    if( d_inst_terms.find( n )==d_inst_terms.end() ){
//      for( int i=0; i<(int)n.getNumChildren(); i++ ){
//        if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
//          setActiveInstConstants( n[i] );
//        }
//      }
//    }
//  }
//}

void InstantiatorTheoryUf::resetInstantiation()
{
  d_does_ematch.clear();
  d_eq_amb.clear();
  d_did_ematch_mod.clear();
  for( std::map< Node, std::map< Node, InstMatchGroup* > >::iterator it = d_ematch.begin();
      it != d_ematch.end(); ++it ){
    for( std::map< Node, InstMatchGroup* >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
      it2->second->clear();
    }
  }
  for( std::map< Node, std::map< Node, InstMatchGroup* > >::iterator it = d_ematch_mod.begin();
      it != d_ematch_mod.end(); ++it ){
    for( std::map< Node, InstMatchGroup* >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
      it2->second->clear();
    }
  }
  refreshMaps();
}

bool InstantiatorTheoryUf::prepareInstantiation( Effort e )
{
  if( e==MIN_EFFORT ){
    debugPrint();
  }
  Debug("quant-uf") << "Search (" << e << ") for instantiation for UF: " << std::endl;

  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    if( d_instEngine->getActive( it->first ) ){
      calculateMatches( it->first, e );
    }
  }
  if( d_inst_matches.getNumMatches()>0 ){
    Debug("quant-uf") << "*** I produced these matches (" << e << ") : " << std::endl;
    d_inst_matches.debugPrint("quant-uf");
    Debug("quant-uf") << std::endl;
  }

  return false;
}

void InstantiatorTheoryUf::debugPrint()
{
  //Debug("quant-uf") << "Instantiation constants:" << std::endl;
  //for( BoolMap::const_iterator it = d_active_ic.begin(); it!=d_active_ic.end(); ++it ){
  //  Debug("quant-uf") << "   " << (*it).first;
  //  //Debug("quant-uf") << "  ->  " << d_solved_ic[(*it).first];
  //  Debug("quant-uf") << std::endl;
  //}
  //Debug("quant-uf") << "Instantiation terms:" << std::endl;
  //for( BoolMap::const_iterator it = d_inst_terms.begin(); it!=d_inst_terms.end(); ++it ){
  //  Debug("quant-uf") << "   " << (*it).first;
  //  //Debug("quant-uf") << "  ->  " << getRepresentative( (*it).first );
  //  Debug("quant-uf") << std::endl;
  //}
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

  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    Node f = it->first;
    Debug("quant-uf") << f << std::endl;
    Debug("quant-uf") << "   Obligations:" << std::endl;
    NodeLists::iterator ob_i = d_obligations.find( f );
    if( ob_i!=d_obligations.end() ){
      NodeList* ob = (*ob_i).second;
      for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
        Debug("quant-uf") << "      " << *it << std::endl;
      }
    }
  }

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

void InstantiatorTheoryUf::refreshMaps(){
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



void InstantiatorTheoryUf::calculateMatches( Node f, Effort e )
{
  Debug("quant-uf") << "Try to solve (" << e << ") for " << f << "... " << std::endl;
  //calculate base matches
  InstMatch* base = new InstMatch( f, d_instEngine );
  //check if any instantiation constants are solved for
  for( int j = 0; j<(int)d_instEngine->d_inst_constants[f].size(); j++ ){
    Node i = d_instEngine->d_inst_constants[f][j];
    Node ns = getRepresentative( i );
    Node c;
    if( !ns.hasAttribute(InstantitionConstantAttribute()) ){
      c = ns;
    }else{
      NodeLists::iterator eqc_ns_i = d_equivalence_class.find( ns );
      if( eqc_ns_i!=d_equivalence_class.end() ){
        NodeList* eqc_ns = (*eqc_ns_i).second;
        for( NodeList::const_iterator it = eqc_ns->begin(); it != eqc_ns->end(); ++it ){
          if( !(*it).hasAttribute(InstantitionConstantAttribute()) ){
            c = *it;
            break;
          }
        }
      }
    }
    if( c!=Node::null() ){
      base->setMatch( i, c );
    }
  }
  if( base->isComplete() ){
    //f is instantiation ready
    d_inst_matches.d_matches.push_back( base );
  }else{
    if( e>MIN_EFFORT ){
      NodeLists::iterator ob_i = d_obligations.find( f );
      if( ob_i!=d_obligations.end() ){
        NodeList* ob = (*ob_i).second;
        std::map< Node, InstMatchGroup* > obMatches;
        // for each literal asserted about the negation of the body of f
        for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
          Assert( (*it).getKind()==IFF || (*it).getKind()==EQUAL );
          Debug("quant-uf-alg") << "Process obligation " << (*it) << std::endl;
          obMatches[ (*it) ] = new InstMatchGroup;
          if( !(*it)[1].hasAttribute(InstantitionConstantAttribute()) ){
            // E-match on the LHS of the equality
            if( e<FULL_EFFORT ){
              //build E-matches with terms in the same equivalence class
              addEMatch( obMatches[ (*it) ], (*it)[0], (*it)[0], f, e==STANDARD_EFFORT );
            }else{
              //build E-matches with any term
              addEMatch( obMatches[ (*it) ], (*it)[0], f, true );
            }
          }else{
            // E-match both sides of the equality
            if( e<FULL_EFFORT ){
              //build E-matches with 2 terms in same equivalence class
              addEqualityEMatch( obMatches[ (*it) ], (*it), f, e==STANDARD_EFFORT );
            }else{
              //E-match any two terms
              addEMatch( obMatches[ (*it) ], (*it)[0], f, true );
              addEMatch( obMatches[ (*it) ], (*it)[1], f, true );
            }
          }
          Debug("quant-uf-alg") << "Finished creating obligation matches" << std::endl;
          obMatches[ (*it) ]->removeRedundant();
          if( obMatches[ (*it) ]->d_matches.size()>0 ){
            Debug("quant-uf") << "(Partial) matches for " << (*it) << " : " << std::endl;
            obMatches[ (*it) ]->debugPrint( "quant-uf" );
          }
          for( int i=0; i<(int)obMatches[ (*it) ]->getNumMatches(); i++ ){
            obMatches[ (*it) ]->getMatch( i )->add( base );
          }
        }
        Debug("quant-uf-alg") << "Build combined matches..." << std::endl;
        //build complete matches
        InstMatchGroup* combined = new InstMatchGroup;
        for( std::map< Node, InstMatchGroup* >::iterator it = obMatches.begin(); it != obMatches.end(); ++it ){
          if( combined->getNumMatches()==0 ){
            combined->add( it->second );
          }else{
            InstMatchGroup* temp = new InstMatchGroup( combined );
            if( temp->merge( it->second ) ){
              temp->add( combined );
            }
            temp->add( it->second );
            combined = temp;
            combined->removeDuplicate();
          }
        }
        Debug("quant-uf") << "Combined matches : " << std::endl;
        combined->debugPrint( "quant-uf" );
        d_inst_matches.addComplete( combined );
      }
    }
  }


  Debug("quant-uf") << std::endl;
}

void InstantiatorTheoryUf::doEMatching( Node i, Node c, Node f, bool moduloEq ){
  //Node oi = i;
  //Node oc = c;
  //std::cout << "--> " << oi << " " << oc << " " << moduloEq << std::endl;

  bool alreadyProcessed = false;
  if( moduloEq ){
    i = getRepresentative( i );
    c = getRepresentative( c );
    alreadyProcessed = ( d_did_ematch_mod.find( i )!=d_did_ematch_mod.end() &&
                         d_did_ematch_mod[i].find( c )!=d_did_ematch_mod[i].end() );
  }else{
    alreadyProcessed = ( d_does_ematch.find( i )!=d_does_ematch.end() &&
                         d_does_ematch[i].find( c )!=d_does_ematch[i].end() );
  }
  if( alreadyProcessed ){
    Debug("quant-uf-ematch") << "already processed " << i << " " << c << std::endl;
  }else{
    Debug("quant-uf-ematch") << "do E-matching " << i << " " << c << " " << moduloEq << std::endl;
    if( !areDisequal( i, c ) ){
      //modulo equality
      if( moduloEq ){
        d_did_ematch_mod[i][c] = true;
        //Debug("quant-uf-ematch") << "doEMM " << i << " " << c << std::endl;
        if( d_emap[i].empty() ){
          d_emap[i].push_back( i );
        }
        if( d_emap[c].empty() ){
          d_emap[c].push_back( c );
        }
        d_ematch_mod[i][c] = d_ematch_mod[i][c] ? d_ematch_mod[i][c] : new InstMatchGroup;
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
            //Debug("quant-uf-ematch") << "mod-doEM : " << i1 << " " << c1 << std::endl;
            if( i1!=Node::null() &&
                ( i1.getKind()!=INST_CONSTANT || getRepresentative( c1 )==c1 ) ){
              doEMatching( i1, c1, f );
              if( d_does_ematch[i1][c1] ){
                d_ematch_mod[i][c]->add( d_ematch[i1][c1] );
              }
            }
            //Debug("quant-uf-ematch") << "mod-doEM done " << i1 << " " << c1 << std::endl;
          }
        }
        //Debug("quant-uf-ematch") << "doEMM done " << i << " " << c << std::endl;
        d_ematch_mod[i][c]->removeRedundant();
        Assert( d_did_ematch_mod[i][c] && d_ematch_mod[i][c]!=NULL );
      }else{
        Assert( i.getAttribute(InstantitionConstantAttribute())==f && !c.hasAttribute(InstantitionConstantAttribute()) );
        //if not already generated
        if( i.getKind()==INST_CONSTANT ){
          if( areDisequal( i, c ) ){
            Debug("quant-uf-ematch") << i << " and " << c << " FAILED disequal iconst." << std::endl;
            d_does_ematch[i][c] = false;
            d_eq_amb[i][c] = false;
          }else{
            InstMatch* m = new InstMatch( f, d_instEngine );
            if( !areEqual( i, c ) ){
              m->setMatch( i, getRepresentative( c ) );
            }
            Debug("quant-uf-ematch") << i << " and " << c << " Ematched." << std::endl;
            d_does_ematch[i][c] = true;
            d_ematch[i][c] = d_ematch[i][c] ? d_ematch[i][c] : new InstMatchGroup;
            d_ematch[i][c]->d_matches.push_back( m );
          }
        }else if( i.getKind()==EQUAL || i.getKind()==IFF ){
          if( c.getKind()!=i.getKind() || i[0].getType()!=c[0].getType() ){
            Debug("quant-uf-ematch") << i << " and " << c << " FAILED kinds." << std::endl;
            d_does_ematch[i][c] = false;
            d_eq_amb[i][c] = false;
          }else{
            //check both ways
            bool foundMatch = false;
            d_does_ematch[i][c] = true;
            d_ematch[i][c] = d_ematch[i][c] ? d_ematch[i][c] : new InstMatchGroup;
            for( int s=0; s<2; s++ ){
              Node c1 = s==0 ? c[0] : c[1];
              Node c2 = s==0 ? c[1] : c[0];
              doEMatching( i[0], c1, f, true );
              doEMatching( i[1], c2, f, true );
              if( d_does_ematch[i[0]][c1] && d_does_ematch[i[1]][c2] ){
                d_ematch[i][c]->add( d_ematch_mod[i[0]][c1] );
                if( d_ematch[i][c]->merge( d_ematch_mod[i[1]][c2] ) ){
                  foundMatch = true;
                  break;
                }else{
                  d_ematch[i][c]->clear();
                }
              }
            }
            if( !foundMatch ){
              Debug("quant-uf-ematch") << i << " and " << c << " FAILED incompat equal." << std::endl;
              d_does_ematch[i][c] = false;
              d_eq_amb[i][c] = true;
            }
          }
        }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
          //equality independent, do nothing
          d_does_ematch[i][c] = false;
          d_eq_amb[i][c] = false;
          Debug("quant-uf-ematch") << i << " and " << c << " FAILED operators." << std::endl;
        }else{
          Assert( i.getNumChildren()==c.getNumChildren() );
          d_does_ematch[i][c] = true;
          d_eq_amb[i][c] = true;
          d_ematch[i][c] = d_ematch[i][c] ? d_ematch[i][c] : new InstMatchGroup;
          d_ematch[i][c]->d_matches.push_back( new InstMatch( f, d_instEngine ) );
          for( int j=0; j<(int)c.getNumChildren(); j++ ){
            if( areDisequal( i[j], c[j] ) ){
              Debug("quant-uf-ematch") << i << " and " << c << " FAILED disequal arg." << std::endl;
              d_does_ematch[i][c] = false;
              d_eq_amb[i][c] = false;
              break;
            }else if( !areEqual( i[j], c[j] ) ){
              if( d_does_ematch[i][c] ){
                doEMatching( i[j], c[j], f, true );
                if( d_does_ematch[i[j]][c[j]] ){
                  if( !d_ematch[i][c]->merge( d_ematch_mod[i[j]][c[j]] ) ){
                    Debug("quant-uf-ematch") << i << " and " << c << " FAILED incompatible match. " << j << std::endl;
                    d_does_ematch[i][c] = false;
                  }
                }else{
                  Debug("quant-uf-ematch") << i << " and " << c << " FAILED argument. " << j << std::endl;
                  d_does_ematch[i][c] = false;
                }
              }
            }
          }
        }
        Assert( d_does_ematch.find( i )!=d_does_ematch.end() );
        Assert( d_does_ematch[i].find( c )!=d_does_ematch[i].end() );
        Assert( !d_does_ematch[i][c] || d_ematch[i][c]!=NULL );
        Assert( d_does_ematch[i][c] || ( d_eq_amb.find( i )!=d_eq_amb.end() && d_eq_amb[i].find( c )!=d_eq_amb[i].end() ) );
      }
    }else{
      Debug("quant-uf-ematch") << i << " and " << c << " FAILED disequal." << std::endl;
      d_does_ematch[i][c] = false;
      d_eq_amb[i][c] = false;
    }
  }
  //std::cout << "<-- " << oi << " " << oc << " " << moduloEq << std::endl;
}

void InstantiatorTheoryUf::getPartialMatches( Node i, Node c, Node f, InstMatchGroup* mg ){
  //std::cout << "get pm " << i << " " << c << std::endl;
  doEMatching( i, c, f );
  if( d_does_ematch[i][c] ){
    mg->add( d_ematch[i][c] );
  }else if( d_eq_amb[i][c] ){
    Assert( i.getNumChildren()==c.getNumChildren() );
    for( int j=0; j<(int)i.getNumChildren(); j++ ){
      if( !areEqual( i[j], c[j] ) && i[j].getAttribute(InstantitionConstantAttribute())==f ){
        getPartialMatches( i[j], c[j], f, mg );
      }
    }
    if( i.getKind()==EQUAL || i.getKind()==IFF ){
      getPartialMatches( i[0], c[1], f, mg );
      getPartialMatches( i[1], c[0], f, mg );
    }
  }
}
void InstantiatorTheoryUf::partialMerge( InstMatchGroup* m1, InstMatchGroup* m2, InstMatchGroup* prod ){
  //do partial merge DO_THIS
  for( int i=0; i<(int)m1->getNumMatches(); i++ ){
    for( int j=0; j<(int)m2->getNumMatches(); j++ ){
      if( isIntersectionConsistent( m1->getMatch( i ), m2->getMatch( j ) ) ){

      }else{
        prod->d_matches.push_back( m1->getMatch( i ) );
        prod->d_matches.push_back( m2->getMatch( j ) );
      }
    }
  }
}
bool InstantiatorTheoryUf::isIntersectionConsistent( InstMatch* m1, InstMatch* m2 ){
  for( int i=0; i<(int)m1->d_vars.size(); i++ ){
    Assert( m1->d_vars[i]==m2->d_vars[i] );
    if( m1->d_map[ m1->d_vars[i] ]!=Node::null() &&
        m2->d_map[ m2->d_vars[i] ]!=Node::null() && 
        m1->d_map[ m1->d_vars[i] ]!=m2->d_map[ m2->d_vars[i] ] &&
        areDisequal( m1->d_map[ m1->d_vars[i] ], m2->d_map[ m1->d_vars[i] ] ) ){
      return false;
    }
  }
  return true;
}

void InstantiatorTheoryUf::addEMatch( InstMatchGroup* mg, Node i, Node c, Node f, bool partialMatch ){
  std::map< Node, std::vector< Node > >::iterator itr = d_emap.find( getRepresentative( c ) );
  for( int k=0; k<(int)itr->second.size(); k++ ){
    if( !itr->second[k].hasAttribute(InstantitionConstantAttribute()) ){
      doEMatching( i, itr->second[k], f, false );
      if( d_does_ematch[ i ][ itr->second[k] ] ){
        Debug("quant-uf-ematch") << i << " and " << itr->second[k] << " were E-matched." << std::endl;
        mg->add( d_ematch[ i ][ itr->second[k] ] );
      }else if( partialMatch && d_eq_amb[ i ][ itr->second[k] ] ){
        Debug("quant-uf-ematch") << i << " and " << itr->second[k] << " were partially E-matched." << std::endl;
        getPartialMatches( i, itr->second[k], f, mg );
      }else{
        Debug("quant-uf-ematch") << i << " and " << itr->second[k] << " FAILED to E-match." << std::endl;
      }
    }
  }
}

void InstantiatorTheoryUf::addEMatch( InstMatchGroup* mg, Node i, Node f, bool partialMatch ){
  for( BoolMap::const_iterator it = d_concrete_terms.begin(); it!=d_concrete_terms.end(); ++it ){
    if( i.getType()==(*it).first.getType() && !areEqual( i, (*it).first ) ){    //already handled for STANDARD_EFFORT
      doEMatching( i, (*it).first, f, false );
      if( d_does_ematch[ i ][ (*it).first ] ){
        Debug("quant-uf-ematch") << i << " and " << (*it).first << " were E-matched." << std::endl;
        mg->add( d_ematch[ i ][ (*it).first ] );
      }else if( partialMatch && d_eq_amb[ i ][ (*it).first ] ){
        Debug("quant-uf-ematch") << i << " and " << (*it).first << " were partially E-matched." << std::endl;
        getPartialMatches( i, (*it).first, f, mg );
      }
    }
  }
}

void InstantiatorTheoryUf::addEqualityEMatch( InstMatchGroup* mg, Node i, Node f, bool partialMatch ){
  for( BoolMap::iterator it = d_is_rep.begin(); it!=d_is_rep.end(); ++it ){
    if( (*it).second ){
      InstMatchGroup* mgt1 = new InstMatchGroup;
      addEMatch( mgt1, i[0], (*it).first, f, partialMatch );
      InstMatchGroup* mgt2 = new InstMatchGroup;
      addEMatch( mgt2, i[1], (*it).first, f, partialMatch );
      if( mgt1->merge( mgt2 ) ){
        mg->add( mgt1 );
      }
      //delete mgt1;
      //delete mgt2;
    }
  }
}

void InstantiatorTheoryUf::filterInconsistent( InstMatchGroup* mg ){
  for( int i=0; i<(int)mg->d_matches.size(); i++ ){
    if( !isConsistent( mg->d_matches[i] ) ){
      //delete mg->d_matches[i];
      mg->d_matches.erase( mg->d_matches.begin() + i, mg->d_matches.begin() + i + 1 );
      i--;
    }
  }
}

bool InstantiatorTheoryUf::isConsistent( InstMatch* m ){
  Node f = m->getQuantifier();
  NodeLists::iterator ob_i = d_obligations.find( f );
  if( ob_i!=d_obligations.end() ){
    NodeList* ob = (*ob_i).second;
    for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
      
    }
  }
  return true;
}
//
//void InstantiatorTheoryUf::setEmatchDone( Node i, Node c ){
//  NodeLists::iterator emdi_i = d_ematch_done.find( i );
//  NodeList* emdi;
//  if( emdi_i == d_ematch_done.end() ) {
//    emdi = new(d_th->getContext()->getCMM()) NodeList(true, d_th->getContext(), false,
//                                                      ContextMemoryAllocator<Node>(d_th->getContext()->getCMM()));
//    d_ematch_done.insertDataFromContextMemory(i, emdi);
//  }else{
//    emdi = (*emdi_i).second;
//  }
//  emdi->push_back( c );
//  Assert( isEmatchDone( i, c ) );
//}
//
//bool InstantiatorTheoryUf::isEmatchDone( Node i, Node c ){
//  NodeLists::iterator emdi_i = d_ematch_done.find( i );
//  if( emdi_i != d_ematch_done.end() ){
//    NodeList* emdi = (*emdi_i).second;
//    for( NodeList::const_iterator it = emdi->begin(); it != emdi->end(); it++ ) {
//      if( *it == c ){
//        return true;
//      }
//    }
//  }
//  return false;
//}
//
//bool InstantiatorTheoryUf::isGeneralization( Node i1, Node i2 )
//{
//  if( i1==i2 ){
//    return true;
//  }else if( i1.getKind()==INST_CONSTANT ){
//    return i2.getKind()!=INST_CONSTANT;
//  }else if( i1.getKind()==APPLY_UF ){
//    if( i2.getKind()==APPLY_UF && i1.getOperator()==i2.getOperator() ){
//      for( int i=0; i<(int)i1.getNumChildren(); i++ ){
//        if( !isGeneralization( i1[i], i2[i] ) ){
//          return false;
//        }
//      }
//      return true;
//    }
//  }
//  return false;
//}

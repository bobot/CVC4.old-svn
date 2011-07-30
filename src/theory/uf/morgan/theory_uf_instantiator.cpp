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
//
//EMatchTreeNode::EMatchTreeNode( context::Context* c, EMatchTreeNode* p ) : 
//d_parent( p ),
//d_nodes( c ),
//d_children( c ){
//
//}
//
//void EMatchTreeNode::debugPrint( int ind )
//{
//  for( IndexMap::iterator it = d_nodes.begin(); it!=d_nodes.end(); ++it ){
//    for( int i=0; i<ind; i++ ) { Debug("quant-uf") << " "; }
//    Debug("quant-uf") << (*it).first << ": ";
//    IndexList* il = (*it).second;
//    for( IndexList::const_iterator it2 = il->begin(); it2!=il->end(); ++it2 ){
//      Debug("quant-uf") << (*it2) << " ";
//    }
//    Debug("quant-uf") << std::endl;
//  }
//  for( ChildMap::const_iterator it = d_children.begin(); it!=d_children.end(); ++it ){
//    for( int i=0; i<ind; i++ ) { Debug("quant-uf") << " "; }
//    Debug("quant-uf") << (*it).first << ": " << std::endl;
//    (*it).second->debugPrint( ind+1 );
//  }
//}

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
Instantiatior( c, ie ),
d_th(th),
//d_ematch( c ),
//d_ematch_list( c ),
d_inst_terms( c ),
d_concrete_terms( c ),
d_active_ic( c ),
d_equivalence_class( c ),
d_disequality( c ){
  
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

//void InstantiatorTheoryUf::buildEMatchTree( Node n, std::vector< EMatchTreeNode* >& active )
//{
//  if( n.getKind()==INST_CONSTANT ){
//    if( d_ematch.find( n )==d_ematch.end() ){
//      d_ematch[n] = new EMatchTreeNode( d_th->getContext() );
//    }
//    active.push_back( d_ematch[n] );
//  }else if( n.hasAttribute(InstantitionConstantAttribute()) ){
//    Assert( n.getKind()==APPLY_UF );
//    Node op = n.getOperator();
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      //build e-match tree for the child
//      if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
//        std::vector< EMatchTreeNode* > cactive;
//        buildEMatchTree( n[i], cactive );
//        
//        EMatchList* eml;
//        if( d_inst_terms.find( n )==d_inst_terms.end() ){
//          EMatchListMap::iterator eml_i = d_ematch_list.find( n );
//          if( eml_i==d_ematch_list.end() ){
//            eml = new(d_th->getContext()->getCMM()) EMatchList(true, d_th->getContext(), false,
//                                                    ContextMemoryAllocator<EMatchTreeNode*>(d_th->getContext()->getCMM()));
//            d_ematch_list.insertDataFromContextMemory(n, eml);
//          }else{
//            eml = (*eml_i).second;
//          }
//        }
//        //for each e-match tree that we are extending
//        for( int j=0; j<(int)cactive.size(); j++ ){
//          //this node at argument i is dependent upon cactive[j]
//          if( d_inst_terms.find( n )==d_inst_terms.end() ){
//            //add argument index
//            EMatchTreeNode::IndexList* nodes;
//            EMatchTreeNode::IndexMap::iterator n_i = cactive[j]->d_nodes.find(n);
//            if( n_i==cactive[j]->d_nodes.end() ){
//              nodes = new(d_th->getContext()->getCMM()) EMatchTreeNode::IndexList(true, d_th->getContext(), false,
//                                                        ContextMemoryAllocator<int>(d_th->getContext()->getCMM()));
//              cactive[j]->d_nodes.insertDataFromContextMemory(n, nodes);
//            }else{
//              nodes = (*n_i).second;
//            }
//            nodes->push_back( i );
//            //add child node
//            if( cactive[j]->d_children.find( op )==cactive[j]->d_children.end() ){
//              EMatchTreeNode* em = new EMatchTreeNode( d_th->getContext(), cactive[j] );
//              cactive[j]->d_children[op] = em;
//              //add this node to list of ematch tree nodes for n
//              eml->push_back( em );
//            }
//          }
//          EMatchTreeNode* emtn = cactive[j]->d_children[op];
//          //add it to active if not already done so
//          if( std::find( active.begin(), active.end(), emtn )==active.end() ){
//            active.push_back( emtn );
//          }
//        }
//      }
//    }
//    d_inst_terms[n] = true;
//  }
//}
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
    bool qSolved = true;
    for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
      if( d_solved_ic[ *it2 ]==Node::null() ){
        if( d_active_ic.find( *it2 )==d_active_ic.end() ){
          Debug("quant-uf") << *it2 << " is not active in this context. " << std::endl;
          //instantiation constant does not exist in the current context
          d_solved_ic[ *it2 ] = NodeManager::currentNM()->mkVar( (*it2).getType() ); 
        }else{
          Node ns = find( *it2 );
          if( !ns.hasAttribute(InstantitionConstantAttribute()) ){
            //instantiation constant is solved in the current context
            d_solved_ic[ *it2 ] = getConcreteTerm( ns );
          }else{
            qSolved = false;
          }
        }
      }
    }
    if( d_ie->getActive( it->first ) && qSolved ){
      Debug("quant-uf") << "Quantifer " << it->first << " is instantiation-ready: " << std::endl;
      for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
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
    d_equalArgs.clear();
    d_eq_independent.clear();
    for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
        it !=d_inst_constants.end(); ++it ){
      if( d_ie->getActive( it->first ) ){
        d_ematch.clear();
        d_ematch_mod.clear();
        d_eq_independent_em.clear();
        calculateBestMatch( it->first );
      }
    }
    Debug("quant-uf") << "The best instantiation is for " << d_best;
    Debug("quant-uf") << ", heuristic = " << d_heuristic << std::endl;
    for( std::map< Node, Node >::iterator it = d_best_subs.begin(); it!=d_best_subs.end(); ++it ){
      Debug("quant-uf") << "      " << it->first << " -> " << it->second << std::endl;
    }
    for( int j = 0; j<(int)d_inst_constants[d_best].size(); j++ ){
      Node i = d_inst_constants[d_best][j];
      if( d_best_subs.find( i )!=d_best_subs.end() ){
        Debug("quant-uf") << "Set " << i << " to " << d_best_subs[i] << std::endl;
        d_solved_ic[ i ] = d_best_subs[i];
      }else{
        Node c = NodeManager::currentNM()->mkVar( i.getType() );
        Debug("quant-uf") << "Set " << i << " to random ground term " << c << std::endl;
        d_solved_ic[ i ] = c; 
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

  //Debug("quant-uf") << "E-matching: " << std::endl;
  //for( BoolMap::const_iterator iti = d_inst_terms.begin(); iti!=d_inst_terms.end(); ++iti ){
  //  for( BoolMap::const_iterator itc = d_concrete_terms.begin(); itc!=d_concrete_terms.end(); ++itc ){
  //    if( (*iti).first.getType()==(*itc).first.getType() ){
  //      doEMatching( (*iti).first, (*itc).first, false );
  //    }
  //  }
  //}
  ////print e-matching
  //for( std::map< Node, std::map< Node, std::vector< std::map< Node, Node > > > >::iterator it = d_ematch.begin();
  //     it!=d_ematch.end(); ++it ){
  //  Debug("quant-uf") << it->first << ":" << std::endl;
  //  for( std::map< Node, std::vector< std::map< Node, Node > > >::iterator it2 = it->second.begin();
  //       it2!=it->second.end(); ++it2 ){
  //    if( !d_eq_independent[it->first][it2->first] ){
  //      Debug("quant-uf") << "   " << it2->first << ": ";
  //      if( it2->second.empty() ){
  //        Debug("quant-uf") << "none.";
  //      }else{
  //        for( int i=0; i<(int)it2->second.size(); i++ ){
  //          if( i!=0 ){
  //            Debug("quant-uf") << ", or ";
  //          }
  //          for( std::map< Node, Node >::iterator it3 = it2->second[i].begin(); it3!=it2->second[i].end(); ++it3 ){
  //            if( it3!=it2->second[i].begin() ){
  //              Debug("quant-uf") << ", ";
  //            }
  //            Debug("quant-uf") << it3->first << " = " << it3->second;
  //          }
  //        }
  //      }
  //      Debug("quant-uf") << std::endl;
  //    }
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
  d_ematch.clear();
  d_ematch_mod.clear();
  d_eq_independent.clear();
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

int InstantiatorTheoryUf::getNumSharedDisequalities( Node a, Node b )
{
  int numD = 0;
  std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( find( a ) );
  if( itd!=d_dmap.end() ){
    for( int i=0; i<(int)itd->second.size(); i++ ){
      if( areDisequal( itd->second[i], b ) ){
        numD++;
      }
    }
  }
  return numD;
}

bool InstantiatorTheoryUf::eqClassContainsInstConstantsFromFormula( Node c, Node f )
{
  if( c.getAttribute(InstantitionConstantAttribute())==f ){
    return true;
  }else{
    std::map< Node, std::vector< Node > >::iterator itd = d_emap.find( find( c ) );
    if( itd!=d_emap.end() ){
      for( int i=0; i<(int)itd->second.size(); i++ ){
        if( itd->second[i].getAttribute(InstantitionConstantAttribute())==f ){
          return true;
        }
      }
    }
    return false;
  }
}












void InstantiatorTheoryUf::calculateBestMatch( Node f )
{
  Debug("quant-uf") << "Try to solve for " << f << "." << std::endl;
  Debug("quant-uf") << "Terms:" << std::endl;
  std::vector< Node > terms;   //list of terms for f
  std::vector< Node > origTerms;
  std::map< Node, int > gmatchScore;
  std::map< Node, std::vector< Node > > contradict;  //map from ematches to other ematches that they contradict
  std::map< Node, std::vector< Node > > support;  //map from ematches to other ematches that they support
  std::map< Node, std::vector< Node > > support_terms;
  for( BoolMap::const_iterator iti = d_inst_terms.begin(); iti!=d_inst_terms.end(); ++iti ){
    if( (*iti).first.getAttribute(InstantitionConstantAttribute())==f ){
      Debug("quant-uf") << "   " << (*iti).first << std::endl;
      terms.push_back( (*iti).first );
      origTerms.push_back( (*iti).first );
      addToGraphMatchScore( (*iti).first, gmatchScore, contradict, support, support_terms );
    }
  }
  //for( std::map< Node, int >::iterator it = gmatchScore.begin(); it!=gmatchScore.end(); ++it ){
  //  Debug("quant-uf") << "   GM: " << it->first << " score: " << it->second << std::endl;
  //}


  int level = 0;
  std::vector< std::map< Node, Node > > ematches;
  std::vector< Node > gmatches;
  std::map< Node, Node > term_gmatches;
  std::map< Node, int > term_level;
  std::map< Node, bool > terms_ematched;
  while( !terms.empty() ){
    Node best;
    int heuristics[5];    //add heuristic for "this term generalizes the other"
    for( std::map< Node, int >::iterator it = gmatchScore.begin(); it!=gmatchScore.end(); ++it ){
      bool setBest = false;
      for( int h=0; h<5; h++ ){
        int val;
        switch( h ){
          case 0: val = (int)(it->first[0].getKind()!=INST_CONSTANT);break;
          case 1: val = it->second;break;
          case 2: 
            doEMatching( it->first[0], it->first[1], f, false );
            val = (int)( numMatches( ematches, d_ematch[ it->first[0] ][ it->first[1] ] )>0 );
            break;
          case 3: val = (d_equalArgs[it->first[0]][it->first[1]] - it->first[0].getNumChildren());break;
          case 4: val = d_equalArgs[it->first[0]][it->first[1]];break;
        }
        if( best==Node::null() || setBest || val>heuristics[h] ){
          setBest = true;
          heuristics[h] = val;
        }else if( val<heuristics[h] ){
          break;
        }
      }
      if( setBest ){
        best = it->first;
      }
    }
    bool doNextLevel = false;
    if( best!=Node::null() ){
      Debug("quant-uf-alg") << "Best current graph match is " << best << std::endl;
      //for( int h=0; h<4; h++ ){
      //  switch( h ){
      //    case 0: Debug("quant-uf-alg") << " IsInstConstant: ";break;
      //    case 1: Debug("quant-uf-alg") << "          Score: ";break;
      //    case 2: Debug("quant-uf-alg") << "      E-matches: ";break;
      //    case 3: Debug("quant-uf-alg") << "  NumNEqualArgs: ";break;
      //    case 4: Debug("quant-uf-alg") << "   NumEqualArgs: ";break;
      //  }
      //  Debug("quant-uf-alg") << heuristics[h] << std::endl;
      //}
      //store in term matches
      Assert( std::find( gmatches.begin(), gmatches.end(), best )==gmatches.end() );
      Assert( term_gmatches.find( best[0] )==term_gmatches.end() );
      gmatches.push_back( best );
      term_gmatches[ best[0] ] = best[1];
      term_level[ best[0] ] = level;
      //terms have been E-matched
      Assert( d_eq_independent_em.find( best[0] )!=d_eq_independent_em.end() &&
              d_eq_independent_em[ best[0] ].find( best[1] )!=d_eq_independent_em[ best[0] ].end() );
        //Debug("quant-uf") << "Remove from terms" << std::endl;
      //remove best[0] from terms
      for( int i=0; i<(int)terms.size(); i++ ){
        if( terms[i]==best[0] ){
          terms.erase( terms.begin() + i, terms.begin() + i + 1 );
          break;
        }
      }
        //Debug("quant-uf") << "Remove from graph score" << std::endl;
      //update all matches in gmatchScore      
      removeFromGraphMatchScore( best, gmatchScore, contradict, support, support_terms );
      //Debug("quant-uf") << "Scores are now: " << std::endl;
      //for( std::map< Node, int >::iterator it = gmatchScore.begin(); it!=gmatchScore.end(); ++it ){
      //  Debug("quant-uf") << it->first << " " << it->second << std::endl;
      //}
      if( terms.empty() ){
        Debug("quant-uf-alg") << "All terms graph matched, now try to E-match." << std::endl;
        doNextLevel = true;
      }
    }else{
      Assert( gmatchScore.empty() && contradict.empty() && support.empty() && support_terms.empty() );
      Debug("quant-uf-alg") << "No graph matches for ";
      for( int i=0; i<(int)terms.size(); i++ ){
        if( i!=0 ){
          Debug("quant-uf-alg") << ", ";
        }
        Debug("quant-uf-alg") << terms[i];
      }
      Debug("quant-uf-alg") << ", break up into arguments" << std::endl;
      doNextLevel = true;
    }
    if( doNextLevel ){
      std::vector< Node > newTerms;
      //attempt to unify each term at current level
      //DO_THIS smarter: decide first by consensus
      std::vector< Node > eqs;
      for( int j=0; j<(int)gmatches.size(); j++ ){
        if( term_level[ gmatches[j][0] ]==level ){
          eqs.push_back( gmatches[j] );
        }
      }
      doEMatchMerge( eqs, ematches, terms, terms_ematched );

      if( !terms.empty() ){
        //add all previous matches back in for the sake of relevance finding (they will be immediately removed)
        for( int i=0; i<(int)gmatches.size(); i++ ){
          newTerms.push_back( gmatches[i][0] );
          addToGraphMatchScore( gmatches[i][0], gmatches[i][1], gmatchScore, contradict, support, support_terms );
        }
        //break up all terms into arguments
        for( int i=0; i<(int)terms.size(); i++ ){
          for( int j=0; j<(int)terms[i].getNumChildren(); j++ ){
            if( terms[i][j].getAttribute(InstantitionConstantAttribute())==f ){
              if( std::find( newTerms.begin(), newTerms.end(), terms[i][j] )==newTerms.end() &&
                  term_level.find( terms[i][j] )==term_level.end() ){
                newTerms.push_back( terms[i][j] );
                addToGraphMatchScore( terms[i][j], gmatchScore, contradict, support, support_terms );
              }
            }
          }
        }
        //remove all previous matches
        for( int i=0; i<(int)gmatches.size(); i++ ){
          removeFromGraphMatchScore( gmatches[i], gmatchScore, contradict, support, support_terms );
          for( int j=0; j<(int)newTerms.size(); j++ ){
            if( newTerms[j]==gmatches[i][0] ){
              newTerms.erase( newTerms.begin() + j, newTerms.begin() + j + 1 );
              break;
            }
          }
        }

        terms.clear();
        terms.insert( terms.begin(), newTerms.begin(), newTerms.end() );

        level++;
        //Debug("quant-uf") << "Terms are now ";
        //for( int i=0; i<(int)terms.size(); i++ ){
        //  if( i!=0 ){
        //    Debug("quant-uf") << ", ";
        //  }
        //  Debug("quant-uf") << terms[i];
        //}
        //Debug("quant-uf") << std::endl;
      }
    }
  }

  Debug("quant-uf") << "Graph matches for each term: " << std::endl;
  for( std::map< Node, Node >::iterator it = term_gmatches.begin(); it!=term_gmatches.end(); ++it ){
    Debug("quant-uf") << "   ";
    if( term_level[it->first]>0 ){
      Debug("quant-uf") << "(Level " << term_level[it->first]+1 << "): ";
    }
    Debug("quant-uf") << it->first << " -> " << it->second << std::endl;
  }

  //calculate the quality of the graph match
  int irrelevant = 0;
  int irrelevantSum = 0;
  int gscore = 0;
  int gscoreSum = 0;
  int escore = 0;
  int escoreSum = 0;
  // note this is difficult to do well.  technically, rewards should be given for larger portions of the graph
  for( int i=0; i<(int)origTerms.size(); i++ ){
    //check its relationship between it and other terms in this eq class
    for( int j=i+1; j<(int)origTerms.size(); j++ ){
      if( areEqual( origTerms[i], origTerms[j] ) ){
        if( term_gmatches[ origTerms[i] ]!=Node::null() &&
            term_gmatches[ origTerms[j] ]!=Node::null() && 
            areEqual( term_gmatches[ origTerms[i] ], term_gmatches[ origTerms[j] ] ) ){
          gscore += 2;
        }else{
          Debug("quant-uf-alg") << "  --->Does not match with " << origTerms[i] << " = " << origTerms[j] << std::endl;
        }
        gscoreSum += 2;
      }else if( areDisequal( origTerms[i], origTerms[j] ) ){
        if( term_gmatches[ origTerms[i] ]!=Node::null() &&
            term_gmatches[ origTerms[j] ]!=Node::null() && 
            areDisequal( term_gmatches[ origTerms[i] ], term_gmatches[ origTerms[j] ] ) ){
          gscore += 2;
        }else{
          Debug("quant-uf-alg") << "  --->Does not match with " << origTerms[i] << " != " << origTerms[j] << std::endl;
        }
        gscoreSum += 2;
      }
    }
    if( term_gmatches[ origTerms[i] ]!=Node::null() &&
        areEqual( origTerms[i], term_gmatches[ origTerms[i] ] ) ){
      gscore += 1;
      gscoreSum += 1;
    }
    //check its relationship with disequalities with ground terms
    std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( find( origTerms[i] ) );
    if( itd!=d_dmap.end() ){
      for( int j=0; j<(int)itd->second.size(); j++ ){
        if( !eqClassContainsInstConstantsFromFormula( itd->second[j], f ) ){
          if( term_gmatches[ origTerms[i] ]!=Node::null() &&
              areDisequal( term_gmatches[ origTerms[i] ], itd->second[j] ) ){
            gscore += 1;
          }else{
            Debug("quant-uf-alg") << "  --->Does not match with " << origTerms[i] << " != " << itd->second[j] << std::endl;
          }
          gscoreSum += 1;
        }
      }
    }
    if( term_gmatches[ origTerms[i] ]==Node::null() ){
      irrelevant++;
    }else{
      Assert( terms_ematched.find( origTerms[i] )!=terms_ematched.end() );
      escore += (int)terms_ematched[ origTerms[i] ];
    }
    irrelevantSum++;
    escoreSum++;
  }
  Debug("quant-uf") << "Graph Match score is " << gscore << " / " << gscoreSum;
  Debug("quant-uf") <<  ", E-match score = " << escore << " / " << escoreSum;
  Debug("quant-uf") <<  ", irrelevant score = " << irrelevant << " / " << irrelevantSum;
  Debug("quant-uf") << std::endl;
  double heuristic = 0.0;
  if( irrelevantSum>0 ){
    double graphFactor = gscoreSum>0 ? double( gscore )/double( gscoreSum ) : 1.0;
    double ematchFactor = ( 1.0 + (escoreSum>0 ? double( escore )/double( escoreSum ) : 1.0 ))/2.0;
    heuristic = graphFactor * ematchFactor * double( irrelevantSum - irrelevant )/double(irrelevantSum);
  }
  Debug("quant-uf") << "Unified heuristic = " << heuristic << std::endl;

  Debug("quant-uf") << "Here are the ground substitutions: " << std::endl;
  for( int i=0; i<(int)ematches.size(); i++ ){
    Debug("quant-uf") << "   Substitution #" << (i+1) << ":" << std::endl;
    for( std::map< Node, Node >::iterator it = ematches[i].begin(); it!=ematches[i].end(); ++it ){
      Debug("quant-uf") << "      " << it->first << " -> " << it->second << std::endl;
    }
  }

  Debug("quant-uf") << std::endl;
  if( d_best==Node::null() || heuristic>d_heuristic ){
    d_best = f;
    d_heuristic = heuristic;
    d_best_subs.clear();
    if( !ematches.empty() ){
      d_best_subs = ematches[0];
    }
  }
}

void InstantiatorTheoryUf::getNumEqualArgs( Node i, Node c )
{
  Assert( i.hasAttribute(InstantitionConstantAttribute()) && !c.hasAttribute(InstantitionConstantAttribute()) );
  //if not already generated
  if( d_eq_independent.find( i )==d_eq_independent.end() || 
      d_eq_independent[i].find( c )==d_eq_independent[i].end() ){
    d_eq_independent[i][c] = false;
    if( i.getKind()==INST_CONSTANT ){
      if( !areDisequal( i, c ) ){
        d_equalArgs[i][c] = 0;
      }else{
        d_eq_independent[i][c] = true;
      }
    }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
      //equality independent, do nothing
      d_eq_independent[i][c] = true;
    }else{
      Assert( i.getNumChildren()==c.getNumChildren() );
      int numEqArgs = 0;
      for( int j=0; j<(int)c.getNumChildren(); j++ ){
        if( areDisequal( i[j], c[j] ) ){
          d_eq_independent[i][c] = true;
          break;
        }else if( areEqual( i[j], c[j] ) ){
          numEqArgs++;
        }
      }
      if( !d_eq_independent[i][c] ){
        d_equalArgs[i][c] = numEqArgs;
      }
    }
  }
}

void InstantiatorTheoryUf::addToGraphMatchScore( Node i,
                                                 std::map< Node, int >& gmatchScore,
                                                 std::map< Node, std::vector< Node > >& contradict,
                                                 std::map< Node, std::vector< Node > >& support,
                                                 std::map< Node, std::vector< Node > >& support_terms )
{
  //get terms that are not equality-independent (i.e. there is a chance that this term is equal to it in a real model
  for( BoolMap::const_iterator itc = d_concrete_terms.begin(); itc!=d_concrete_terms.end(); ++itc ){
    if( i.getType()==(*itc).first.getType() && !areDisequal( i, (*itc).first ) &&
        ( i.getKind()!=INST_CONSTANT || find( (*itc).first )==(*itc).first ) ){
      //Debug("quant-uf") << "Do equality independence check for " << terms[i] << " " << (*itc).first << std::endl;
      getNumEqualArgs( i, (*itc).first );
      if( !d_eq_independent[ i ][ (*itc).first ] ){
        addToGraphMatchScore( i, (*itc).first, gmatchScore, contradict, support, support_terms );
      }
    }
  }
}

void InstantiatorTheoryUf::addToGraphMatchScore( Node i, Node c,
                                                 std::map< Node, int >& gmatchScore,
                                                 std::map< Node, std::vector< Node > >& contradict,
                                                 std::map< Node, std::vector< Node > >& support,
                                                 std::map< Node, std::vector< Node > >& support_terms )
{
  Kind k = i.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  Node e = NodeManager::currentNM()->mkNode( k, i, c );
  //get the score. note if areEqual holds, shared disequalities is maximized
  int score = ( areEqual( i, c ) + getNumSharedDisequalities( i, c ) )*2;   

  //combine with other scores in gmatchScore
  for( std::map< Node, int >::iterator it = gmatchScore.begin(); it!=gmatchScore.end(); ++it ){
    if( i != it->first[0] ){
      if( ( areEqual( i, it->first[0] ) && areEqual( c, it->first[1] ) ) ||
          ( areDisequal( i, it->first[0] ) && areDisequal( c, it->first[1] ) ) ){
        //Debug("quant-uf") << i << " " << it->first << " are supportive" << std::endl;
        //if not already in support, then up the score
        for( int r=0; r<2; r++ ){
          Node n1 = (r==0) ? e : it->first;
          Node n2 = (r==0) ? it->first : e;
          if( std::find( support_terms[ n1 ].begin(), support_terms[ n1 ].end(), n2[0] )==support_terms[ n1 ].end() ){
            support_terms[ n1 ].push_back( n2[0] );
            //Debug("quant-uf") << n1 << " is supported by matches from term " << n2[0] << std::endl;
            if( r==0 ){
              score = score + 1;
            }else{
              it->second = it->second + 1;
            }
          }
          support[ n1 ].push_back( n2 );
        }
      }else if( ( areEqual( i, it->first[0] ) && areDisequal( c, it->first[1] ) ) ||
                ( areDisequal( i, it->first[0] ) && areEqual( c, it->first[1] ) ) ){
        //Debug("quant-uf") << it1->first << " " << it->first << " are contradictory" << std::endl;
        contradict[ e ].push_back( it->first );
        contradict[ it->first ].push_back( e );
      }
    }
  }
  gmatchScore[ e ] = score;
}

void InstantiatorTheoryUf::removeFromGraphMatchScore( Node eq,
                                                      std::map< Node, int >& gmatchScore,
                                                      std::map< Node, std::vector< Node > >& contradict,
                                                      std::map< Node, std::vector< Node > >& support,
                                                      std::map< Node, std::vector< Node > >& support_terms )
{
  //enhance scores for those that are supported
  for( int i=0; i<(int)support[eq].size(); i++ ){
    if( gmatchScore.find( support[eq][i] )!=gmatchScore.end() ){
      gmatchScore[ support[eq][i] ] = gmatchScore[ support[eq][i] ] + 3;
    }
  }
  //remove all irrelevant matches
  std::map< Node, int > gmatchTemp;
  gmatchTemp = gmatchScore;
  for( std::map< Node, int >::iterator it = gmatchTemp.begin(); it!=gmatchTemp.end(); ++it ){
    if( it->first!=eq ){
      //removed if the term is being set or the graph match is now contradicted
      bool remove = ( it->first[0]== eq[0] || 
                      std::find( contradict[eq].begin(), contradict[eq].end(), it->first )!=contradict[eq].end() );
      if( remove ){
        contradict.erase( it->first );
        support.erase( it->first );
        support_terms.erase( it->first );
        gmatchScore.erase( it->first );
      }else{
        //diminish scores for those previously supported but no more
        if( std::find( support_terms[eq].begin(), support_terms[eq].end(), it->first[0] )!=support_terms[eq].end() ){
          it->second = it->second - 1;
        }
      }
    }
  }
  contradict.erase( eq );
  support.erase( eq );
  support_terms.erase( eq );
  gmatchScore.erase( eq );

  for( std::map< Node, int >::iterator it = gmatchScore.begin(); it!=gmatchScore.end(); ++it ){
    if( it->first[0]==eq[0] ){
      Debug("quant-uf") << "While breaking up " << eq << ", " << it->first << std::endl;
    }
    Assert( it->first[0]!=eq[0] );
  }
}

void InstantiatorTheoryUf::doEMatchMerge( std::vector< Node >& eqs, std::vector< std::map< Node, Node > >& ematches,
                                          std::vector< Node >& terms, std::map< Node, bool >& terms_ematched )
{
  for( int j=0; j<(int)eqs.size(); j++ ){
    Node i = eqs[j][0];
    Node c = eqs[j][1];
    //terms have been E-matched
    Assert( d_eq_independent_em.find( i )!=d_eq_independent_em.end() &&
            d_eq_independent_em[ i ].find( c )!=d_eq_independent_em[ i ].end() );

    Debug("quant-uf-alg") << "E-matching for " << i << " " << c << " : ";
    Assert( !d_eq_independent_em[i][c] );
    if( d_ematch[i][c].empty() ){
      Debug("quant-uf-alg") << "none.";
    }else{
      for( int k=0; k<(int)d_ematch[i][c].size(); k++ ){
        if( k!=0 ){
          Debug("quant-uf-alg") << ", or ";
        }
        for( std::map< Node, Node >::iterator it = d_ematch[i][c][k].begin(); 
            it!=d_ematch[i][c][k].end(); ++it ){
          if( it!=d_ematch[i][c][k].begin() ){
            Debug("quant-uf-alg") << ", ";
          }
          Debug("quant-uf-alg") << it->first << " = " << it->second;
        }
      }
    }
    Debug("quant-uf-alg") << std::endl;
    terms_ematched[ i ] = (numMatches( ematches, d_ematch[ i ][ c ] )>0);
    if( terms_ematched[ i ] ){
      unify( ematches, d_ematch[ i ][ c ] );
      Assert( ematches.size()>0 );
    }else{
      Debug("quant-uf-alg") << "Could not unify " << eqs[j] << "." << std::endl;
      Assert( std::find( terms.begin(), terms.end(), i )==terms.end() );
      if( i.getKind()!=INST_CONSTANT ){
        terms.push_back( i );
      }
    }
  }
}





void InstantiatorTheoryUf::doEMatching( Node i, Node c, Node f, bool moduloEq )
{
  if( !areDisequal( i, c ) ){
    //modulo equality
    if( moduloEq ){
      i = find( i );
      c = find( c );
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
                ( i1.getKind()!=INST_CONSTANT || find( c1 )==c1 ) ){
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
      if( d_eq_independent_em.find( i )==d_eq_independent_em.end() || 
          d_eq_independent_em[i].find( c )==d_eq_independent_em[i].end() ){
        if( i.getKind()==INST_CONSTANT ){
          if( areDisequal( i, c ) ){
            d_eq_independent_em[i][c] = true;
          }else{
            d_ematch[i][c].push_back( std::map< Node, Node >() );
            if( !areEqual( i, c ) ){
              d_ematch[i][c][0][i] = find( c );
            }
            d_eq_independent_em[i][c] = false;
          }
        }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
          //equality independent, do nothing
          d_eq_independent_em[i][c] = true;
        }else{
          Assert( i.getNumChildren()==c.getNumChildren() );
          d_eq_independent_em[i][c] = false;
          for( int j=0; j<(int)c.getNumChildren(); j++ ){
            if( areDisequal( i[j], c[j] ) ){
              d_eq_independent_em[i][c] = true;
            }
          }
          if( !d_eq_independent_em[i][c] ){
            std::vector< std::map< Node, Node > > matches;
            for( int j=0; j<(int)c.getNumChildren(); j++ ){
              if( !areEqual( i[j], c[j] ) ){
                doEMatching( i[j], c[j], f, true );
                unify( matches, d_ematch_mod[i[j]][c[j]] );
                if( matches.empty() ){
                  //there exists no matches, or in other words, i and c do not E-match
                  break;
                }
              }
            }
            d_ematch[i][c].insert( d_ematch[i][c].begin(), matches.begin(), matches.end() );
          }
        }
      }
    }
  }
}

void InstantiatorTheoryUf::unify( std::vector< std::map< Node, Node > >& target,
                                  std::vector< std::map< Node, Node > >& matches )
{
  if( target.empty() ){
    target.insert( target.begin(), matches.begin(), matches.end() );
  }else{
    std::vector< std::map< Node, Node > > newMatches;
    std::vector< std::map< Node, Node > > tempMatches;
    tempMatches.insert( tempMatches.begin(), target.begin(), target.end() );
    for( int k=0; k<(int)matches.size(); k++ ){
      for( int l=0; l<(int)tempMatches.size(); l++ ){
        if( unify( tempMatches[l], matches[k] ) ){
          newMatches.push_back( tempMatches[l] );
        }
      }
    }
    target.clear();
    target.insert( target.begin(), newMatches.begin(), newMatches.end() );
    removeRedundant( target );
  }
}

bool InstantiatorTheoryUf::unify( std::map< Node, Node >& target, std::map< Node, Node >& matches ){
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
  unify( m3, m2 );
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

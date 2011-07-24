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

EMatchTreeNode::EMatchTreeNode( context::Context* c, EMatchTreeNode* p ) : 
d_parent( p ),
d_nodes( c ),
d_children( c ){

}

void EMatchTreeNode::debugPrint( int ind )
{
  for( IndexMap::iterator it = d_nodes.begin(); it!=d_nodes.end(); ++it ){
    for( int i=0; i<ind; i++ ) { Debug("quant-uf") << " "; }
    Debug("quant-uf") << (*it).first << ": ";
    IndexList* il = (*it).second;
    for( IndexList::const_iterator it2 = il->begin(); it2!=il->end(); ++it2 ){
      Debug("quant-uf") << (*it2) << " ";
    }
    Debug("quant-uf") << std::endl;
  }
  for( ChildMap::const_iterator it = d_children.begin(); it!=d_children.end(); ++it ){
    for( int i=0; i<ind; i++ ) { Debug("quant-uf") << " "; }
    Debug("quant-uf") << (*it).first << ": " << std::endl;
    (*it).second->debugPrint( ind+1 );
  }
}

TheoryUfInstantiatior::TheoryUfInstantiatior(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
TheoryInstantiatior( c, ie ),
d_th(th),
d_ematch( c ),
d_ematch_list( c ),
d_inst_terms( c ),
d_concrete_terms( c ){
  
  
}

Theory* TheoryUfInstantiatior::getTheory() { 
  return d_th; 
}

void TheoryUfInstantiatior::check( Node assertion )
{
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  Debug("quant-uf") << "TheoryUfInstantiatior::check: " << assertion << std::endl;
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

void TheoryUfInstantiatior::assertEqual( Node a, Node b )
{
  registerTerm( a );
  registerTerm( b );
}

void TheoryUfInstantiatior::assertDisequal( Node a, Node b )
{
  registerTerm( a );
  registerTerm( b );
}

void TheoryUfInstantiatior::registerTerm( Node n )
{
  if( n.hasAttribute(InstantitionConstantAttribute()) ){
    if( d_inst_terms.find( n )==d_inst_terms.end() ){
      std::vector< EMatchTreeNode* > active;
      buildEMatchTree( n, active );
      //collect instantiation constants
      std::vector< Node > ics;
      collectInstConstants( n, ics );
    }
  }else{
    if( n.getNumChildren()>0 ){
      d_concrete_terms[n] = true;
    }
  }
}

void TheoryUfInstantiatior::collectInstConstants( Node n, std::vector< Node >& ics ){
  if( n.getKind()==INST_CONSTANT ){
    ics.push_back( n );
  }else if( n.hasAttribute(InstantitionConstantAttribute()) ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
        std::vector< Node > cics;
        collectInstConstants( n[i], cics );
        ics.insert( ics.end(), cics.begin(), cics.end() );
      }
    }
    for( int i=0; i<(int)ics.size(); i++ ){
      if( std::find( d_term_ics[n].begin(), d_term_ics[n].end(), ics[i] )==d_term_ics[n].end() ){
        d_term_ics[n].push_back( ics[i] );
      }
    }
  }
}

void TheoryUfInstantiatior::buildEMatchTree( Node n, std::vector< EMatchTreeNode* >& active )
{
  if( n.getKind()==INST_CONSTANT ){
    if( d_ematch.find( n )==d_ematch.end() ){
      d_ematch[n] = new EMatchTreeNode( d_th->getContext() );
    }
    active.push_back( d_ematch[n] );
  }else if( n.hasAttribute(InstantitionConstantAttribute()) ){
    Assert( n.getKind()==APPLY_UF );
    Node op = n.getOperator();
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      //build e-match tree for the child
      if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
        std::vector< EMatchTreeNode* > cactive;
        buildEMatchTree( n[i], cactive );
        
        EMatchList* eml;
        if( d_inst_terms.find( n )==d_inst_terms.end() ){
          EMatchListMap::iterator eml_i = d_ematch_list.find( n );
          if( eml_i==d_ematch_list.end() ){
            eml = new(d_th->getContext()->getCMM()) EMatchList(true, d_th->getContext(), false,
                                                    ContextMemoryAllocator<EMatchTreeNode*>(d_th->getContext()->getCMM()));
            d_ematch_list.insertDataFromContextMemory(n, eml);
          }else{
            eml = (*eml_i).second;
          }
        }
        //for each e-match tree that we are extending
        for( int j=0; j<(int)cactive.size(); j++ ){
          //this node at argument i is dependent upon cactive[j]
          if( d_inst_terms.find( n )==d_inst_terms.end() ){
            //add argument index
            EMatchTreeNode::IndexList* nodes;
            EMatchTreeNode::IndexMap::iterator n_i = cactive[j]->d_nodes.find(n);
            if( n_i==cactive[j]->d_nodes.end() ){
              nodes = new(d_th->getContext()->getCMM()) EMatchTreeNode::IndexList(true, d_th->getContext(), false,
                                                        ContextMemoryAllocator<int>(d_th->getContext()->getCMM()));
              cactive[j]->d_nodes.insertDataFromContextMemory(n, nodes);
            }else{
              nodes = (*n_i).second;
            }
            nodes->push_back( i );
            //add child node
            if( cactive[j]->d_children.find( op )==cactive[j]->d_children.end() ){
              EMatchTreeNode* em = new EMatchTreeNode( d_th->getContext(), cactive[j] );
              cactive[j]->d_children[op] = em;
              //add this node to list of ematch tree nodes for n
              eml->push_back( em );
            }
          }
          EMatchTreeNode* emtn = cactive[j]->d_children[op];
          //add it to active if not already done so
          if( std::find( active.begin(), active.end(), emtn )==active.end() ){
            active.push_back( emtn );
          }
        }
      }
    }
    d_inst_terms[n] = true;
  }
}

bool TheoryUfInstantiatior::prepareInstantiation()
{
  Debug("quant-uf") << "Search for instantiation for UF:" << std::endl;
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;

  //for( EMatchMap::const_iterator it = d_ematch.begin(); it!=d_ematch.end(); ++it ){
  //  Debug("quant-uf") << (*it).first << ": " << std::endl;
  //  (*it).second->debugPrint( 1 );
  //  Debug("quant-uf") << std::endl;
  //}
  Debug("quant-uf") << "Instantiation terms:" << std::endl;
  for( BoolMap::const_iterator it = d_inst_terms.begin(); it!=d_inst_terms.end(); ++it ){
    Debug("quant-uf") << "   " << (*it).first;
    Debug("quant-uf") << "  ->  " << t->find( (*it).first );
    Debug("quant-uf") << std::endl;
  }
  Debug("quant-uf") << "Concrete terms:" << std::endl;
  for( BoolMap::const_iterator it = d_concrete_terms.begin(); it!=d_concrete_terms.end(); ++it ){
    Debug("quant-uf") << "   " << (*it).first;
    Debug("quant-uf") << "  ->  " << t->find( (*it).first );
    Debug("quant-uf") << std::endl;
  }

  //find all instantiation constants that are solved
  bool solved = false;
  for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
       it !=d_inst_constants.end(); ++it ){
    bool qSolved = true;
    for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
      if( !qSolved ){
        d_solved_ic[ *it2 ] = Node::null();
      }else{
        if( d_ematch.find( *it2 )==d_ematch.end() ){
          //instantiation constant does not exist in the current context
          d_solved_ic[ *it2 ] = (*it2).getType().mkGroundTerm(); 
        }else{
          Node ns = t->find( *it2 );
          if( !ns.hasAttribute(InstantitionConstantAttribute()) ){
            //instantiation constant is solved in the current context
            d_solved_ic[ *it2 ] = ns;
          }else{
            //instantiation constant is unsolved in the current context
            qSolved = false;
            d_solved_ic[ *it2 ] = Node::null();
          }
        }
      }
    }
    if( qSolved ){
      Debug("quant-uf") << "Quantifer " << it->first << " is instantiation-ready: " << std::endl;
      for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
        Debug("quant-uf") << "   " << d_solved_ic[ *it2 ] << std::endl;
      }
      solved = true;
      break;
    }
  }

  //we're done if some node is instantiation-ready
  if( !solved ){
    Debug("quant-uf") << "No quantifier is instantiation-ready." << std::endl;
    //otherwise, add possible splitting lemma
    
    //process ambiguity between concrete term and instantiation term
    d_best = Node::null();
    for( BoolMap::const_iterator iit = d_inst_terms.begin(); iit!=d_inst_terms.end(); ++iit ){
      for( BoolMap::const_iterator cit = d_concrete_terms.begin(); cit!=d_concrete_terms.end(); ++cit ){
        bool eq = areEqual( (*cit).first, (*iit).first );
        bool diseq = areDisequal( (*cit).first, (*iit).first );
        Debug("quant-uf-amb-detail") << "Process ambiguity " << (*cit).first << " " << (*iit).first << std::endl;
        Debug("quant-uf-amb-detail") << "Equal, Disequal: " << eq << " " << diseq << std::endl;
        processAmbiguity( (*cit).first, (*iit).first, eq, diseq );
      }
    }
    //if not satisfied, process ambiguity between instantiation terms
    for( BoolMap::const_iterator iit = d_inst_terms.begin(); iit!=d_inst_terms.end(); ++iit ){
      BoolMap::const_iterator iit2 = iit;
      ++iit2;
      for( ; iit2!=d_inst_terms.end(); ++iit2 ){
        bool eq = areEqual( (*iit).first, (*iit2).first );
        bool diseq = areDisequal( (*iit).first, (*iit2).first );
        processAmbiguity( (*iit).first, (*iit2).first, eq, diseq );
      }
    }
    if( d_best!=Node::null() ){
      NodeBuilder<> nb(kind::OR);
      nb << d_best << d_best.notNode();
      d_best = nb;
      d_lemmas.push_back( d_best );
      Debug("quant-uf") << "lemma is " << d_best << std::endl;
    }
  }
  return false;
}

void TheoryUfInstantiatior::processAmbiguity( Node c, Node i, bool eq, bool diseq, int depth )
{
  Assert( !eq || !diseq );
  if( c.getKind()!=APPLY_UF || i.getKind()!=APPLY_UF ){
    Debug("quant-uf-amb-detail") << "-> Variable." << std::endl;
  }else{
    if( c.getOperator()!=i.getOperator() ){
      Debug("quant-uf-amb-detail") << "-> Equality independent, operators " << c.getOperator() << ", " << i.getOperator() << std::endl;
    }else{
      Assert( c.getNumChildren()==i.getNumChildren() );
      int nEqArgs = 0;
      Node argC, argI;
      for( int j=0; j<(int)c.getNumChildren(); j++ ){
        if( areDisequal( c[j], i[j] ) ){
          Debug("quant-uf-amb-detail") << "-> Equality independent, arguments" << std::endl;
          return;
        }else if( areEqual( c[j], i[j] ) ){
          nEqArgs++;
        }else{
          processAmbiguity( c[j], i[j], eq, diseq, depth+1 );
          argC = c[j];
          argI = i[j];
        }
      }
      if( nEqArgs!=c.getNumChildren() ){
        Debug("quant-uf-amb") << c << " and " << i << " are equality-ambiguous." << std::endl;
        bool isSlvC = isSolved( c );
        bool isSlvI = isSolved( i );
        int nNEqArgs = c.getNumChildren()-nEqArgs;
        Debug("quant-uf-amb") << "Heuristics = " << !diseq << " " << !isSlvI << " " << isSlvC << " ";
        Debug("quant-uf-amb") << eq << " " << nNEqArgs << "< " << nEqArgs << " ";
        Debug("quant-uf-amb") << depth << " ?" << std::endl;
        bool setBest = false;
        for( int i=0; i<7; i++ ){
          int val;
          switch( i ){
            case 0: val = (int)!diseq;break;
            case 1: val = (int)!isSlvI;break;
            case 2: val = (int)isSlvC;break;
            case 3: val = (int)eq;break;
            case 4: val = -nNEqArgs;break;
            case 5: val = nEqArgs;break;
            case 6: val = depth;break;
          }
          if( d_best==Node::null() || setBest || val>d_best_heuristic[i] ){
            d_best_heuristic[i] = val;
            setBest = true;
          }else if( val<d_best_heuristic[i] ){
            break;
          }
        }
        if( setBest ){
          if( argC.getType()==NodeManager::currentNM()->booleanType() ){
            d_best = NodeManager::currentNM()->mkNode( IFF, argC, argI );
          }else{
            d_best = NodeManager::currentNM()->mkNode( EQUAL, argC, argI );
          }
          Debug("quant-uf-amb") << "Set best " << d_best << std::endl;
        }
      }else{
        Debug("quant-uf-amb-detail") << "-> Equality compatible" << std::endl;
      }
    }
  }
}
//
//int TheoryUfInstantiatior::maximumDepthAmbiguity( Node c, Node i, Node& ci, Node& ii, int& depth )
//{
//  if( c.getKind()!=APPLY_UF || i.getKind()!=APPLY_UF || c.getOperator()!=i.getOperator() ){
//    depth = 0;
//    ci = c;
//    ii = i;
//    return -1;
//  }else{
//    int nEqArgs = 0;
//    depth = -1;
//    Assert( c.getNumChildren()==i.getNumChildren() );
//    for( int j=0; j<(int)c.getNumChildren(); j++ ){
//      if( areDisequal( c[j], i[j] ) ){
//        return -1;
//      }else if( areEqual( c[j], i[j] ) ){
//        nEqArgs++;
//      }else{
//        int tempDepth;
//        Node tempCi;
//        Node tempIi;
//        maximumDepthAmbiguity( c[j], i[j], tempCi, tempIi, tempDepth );
//        if( tempDepth>depth ){
//          ci = tempCi;
//          ii = tempIi;
//          depth = tempDepth + 1;
//        }
//      }
//    }
//    return nEqArgs;
//  }
//}

bool TheoryUfInstantiatior::areEqual( Node a, Node b ){
  TheoryUFMorgan* t = ((TheoryUFMorgan*)d_th);
  return t->find( a )==t->find( b );
}

bool TheoryUfInstantiatior::areDisequal( Node a, Node b ){
  TheoryUFMorgan* t = ((TheoryUFMorgan*)d_th);
  a = t->find( a );
  b = t->find( b );
  if( a==b ){
    return false;
  }else{
    TheoryUFMorgan::EqLists::iterator deq_i = t->d_disequalities.find(a);
    if(deq_i != t->d_disequalities.end()) {
      TheoryUFMorgan::EqList* deq = (*deq_i).second;
      for(TheoryUFMorgan::EqList::const_iterator j = deq->begin(); j != deq->end(); ++j) {
        TNode deqn = *j;
        Assert( t->find( deqn[0] )==a || t->find( deqn[1] )==a );
        if( t->find( deqn[0] )==b || t->find( deqn[1] )==b ){
          return true;
        }
      }
    }
    return false;
  }
}

bool TheoryUfInstantiatior::isSolved( Node n )
{
  if( d_term_ics.find( n )!=d_term_ics.end() ){
    for( int i=0; i<(int)d_term_ics[n].size(); i++ ){
      if( d_solved_ic[ d_term_ics[n][i] ]==Node::null() ){
        return false;
      }
    }
  }
  return true;
}

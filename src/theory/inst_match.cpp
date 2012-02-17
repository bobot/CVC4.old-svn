/*********************                                                        */
/*! \file inst_match.cpp
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
 ** \brief Implementation of inst match class
 **/

#include "theory/inst_match.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/uf/theory_uf_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

int InstMatch::d_im_count = 0;

InstMatch::InstMatch(){
  d_im_count++;
  //if( d_im_count%1000==0 ){
  //  std::cout << "im count = " << d_im_count << " " << InstMatchCalculator::d_imcCount << " " << InstMatchGenerator::d_imgCount << " " << Trigger::trCount << std::endl;
  //}
}

InstMatch::InstMatch( InstMatch* m ){
  d_map = m->d_map;
  d_im_count++;
  //if( d_im_count%1000==0 ){
  //  std::cout << "im count = " << d_im_count << " " << InstMatchCalculator::d_imcCount << " " << InstMatchGenerator::d_imgCount << std::endl;
  //}
}

bool InstMatch::setMatch( EqualityQuery* q, Node v, Node m ){ 
  if( d_map.find( v )==d_map.end() ){
    d_map[v] = m; 
    return true;
  }else{
    return q->areEqual( d_map[v], m );
  }
}

bool InstMatch::add( InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( d_map.find( it->first )==d_map.end() ){
      d_map[it->first] = it->second;
    }
  }
  return true;
}

bool InstMatch::merge( EqualityQuery* q, InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( d_map.find( it->first )==d_map.end() ){
      d_map[ it->first ] = it->second;
    }else{
      if( it->second!=d_map[it->first] ){
        if( !q->areEqual( it->second, d_map[it->first] ) ){
          d_map.clear();
          return false;
        }
      }
    }
  }
  return true;
}

void InstMatch::debugPrint( const char* c ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    Debug( c ) << "   " << it->first << " -> " << it->second << std::endl;
  }
  //if( !d_splits.empty() ){
  //  Debug( c ) << "   Conditions: ";
  //  for( std::map< Node, Node >::iterator it = d_splits.begin(); it !=d_splits.end(); ++it ){
  //    Debug( c ) << it->first << " = " << it->second << " ";
  //  }
  //  Debug( c ) << std::endl;
  //}
}

void InstMatch::computeTermVec( QuantifiersEngine* ie, std::vector< Node >& vars, std::vector< Node >& match ){
  for( int i=0; i<(int)vars.size(); i++ ){
    if( d_map.find( vars[i] )!=d_map.end() ){
      match.push_back( d_map[ vars[i] ] );
    }else{
      match.push_back( ie->getFreeVariableForInstConstant( vars[i] ) );
    }
  }
}




InstMatchGenerator::InstMatchGenerator( Node pat, QuantifiersEngine* qe, bool isLitMatch ) : d_isLitMatch( isLitMatch ){
  initializePattern( pat, qe );
}

InstMatchGenerator::InstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe, bool isLitMatch ) : d_isLitMatch( isLitMatch ){
  if( pats.size()==1 ){
    initializePattern( pats[0], qe );
  }else{
    initializePatterns( pats, qe );
  }
}

void InstMatchGenerator::initializePattern( Node pat, QuantifiersEngine* qe ){
  Assert( pat.hasAttribute(InstConstantAttribute()) );
  d_pattern = pat;
  d_match_pattern = pat;
  if( d_match_pattern.getKind()==NOT ){
    //we want to add the children of the NOT
    d_match_pattern = d_pattern[0];
  }
  if( d_match_pattern.getKind()==IFF || d_match_pattern.getKind()==EQUAL ){
    if( !d_match_pattern[0].hasAttribute(InstConstantAttribute()) ){
      Assert( d_match_pattern[1].hasAttribute(InstConstantAttribute()) );
      //swap sides
      d_pattern = NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), d_match_pattern[1], d_match_pattern[0] );
      d_pattern = pat.getKind()==NOT ? d_pattern.notNode() : d_pattern;
      //set match pattern
      d_match_pattern = d_match_pattern[1];
    }else if( !d_match_pattern[1].hasAttribute(InstConstantAttribute()) ){
      Assert( d_match_pattern[0].hasAttribute(InstConstantAttribute()) );
      //set match pattern
      d_match_pattern = d_match_pattern[0];
    }
  }
  for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
    if( d_match_pattern[i].hasAttribute(InstConstantAttribute()) ){
      if( d_match_pattern[i].getKind()!=INST_CONSTANT ){
        d_children.push_back( new InstMatchGenerator( d_match_pattern[i], qe, d_isLitMatch ) );
        d_children_index.push_back( i );
      }
    }
  }
  //if lit match, reform boolean predicate as an equality
  if( d_isLitMatch && d_match_pattern.getKind()==APPLY_UF ){
    bool pol = pat.getKind()!=NOT;
    d_pattern = NodeManager::currentNM()->mkNode( IFF, d_match_pattern, NodeManager::currentNM()->mkConst<bool>(pol) );
  }
  Debug("inst-match-gen") << "Pattern is " << d_pattern << ", match pattern is " << d_match_pattern << std::endl;
  //get the equality engine
  Theory* th_uf = qe->getTheoryEngine()->getTheory( theory::THEORY_UF ); 
  uf::InstantiatorTheoryUf* ith = (uf::InstantiatorTheoryUf*)th_uf->getInstantiator();
  //create candidate generator
  if( d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==IFF ){
    Assert( d_isLitMatch );
    //we will be producing candidates via literal matching heuristics
    d_cg = new uf::CandidateGeneratorTheoryUfEq( ith, d_pattern, d_match_pattern );
  }else{
    if( d_pattern.getKind()!=NOT ){
      //we will be scanning lists trying to find d_match_pattern.getOperator()
      d_cg = new uf::CandidateGeneratorTheoryUf( ith, d_match_pattern.getOperator() );
    }else{
      Assert( d_isLitMatch );
      d_cg = new uf::CandidateGeneratorTheoryUfDisequal( ith, d_match_pattern.getOperator() );
    }
  }
}

void InstMatchGenerator::initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe ){
  for( int i=0; i<(int)pats.size(); i++ ){
    d_children.push_back( new InstMatchGenerator( pats[i], qe, d_isLitMatch ) );
  }
  d_pattern = Node::null();
  d_match_pattern = Node::null();
  d_cg = NULL;
}

/** get match (not modulo equality) */
bool InstMatchGenerator::getMatch( Node t, InstMatch& m, QuantifiersEngine* qe ){
  EqualityQuery* q = qe->getEqualityQuery();
  //add m to partial match vector
  std::vector< InstMatch > partial;
  partial.push_back( InstMatch( &m ) );
  //if t is null
  Assert( !t.isNull() );
  Assert( !d_match_pattern.isNull() );
  Assert( !t.hasAttribute(InstConstantAttribute()) );
  Assert( t.getKind()==d_match_pattern.getKind() );
  Assert( t.getOperator()==d_match_pattern.getOperator() );
  //first, check if ground arguments are not equal, or a match is in conflict
  for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
    if( d_match_pattern[i].hasAttribute(InstConstantAttribute()) ){
      if( d_match_pattern[i].getKind()==INST_CONSTANT ){
        if( !partial[0].setMatch( q, d_match_pattern[i], t[i] ) ){
          //match is in conflict
          return false;
        }
      }
    }else{
      if( !q->areEqual( d_match_pattern[i], t[i] ) ){
        //ground arguments are not equal
        return false;
      }
    }
  }
  //now, fit children into match
  //we will be requesting candidates for matching terms for each child
  for( int i=0; i<(int)d_children.size(); i++ ){
    Node rep = q->getRepresentative( t[ d_children_index[i] ] );
    d_children[i]->d_cg->reset( rep );
  }
  //combine child matches
  int index = 0;
  while( index>=0 && index<(int)d_children.size() ){
    partial.push_back( InstMatch( &partial[index] ) );
    if( d_children[index]->getNextMatch2( partial[index+1], qe ) ){
      index++;
    }else{
      partial.pop_back();
      index--;
    }
  }
  if( index>=0 ){
    m = partial[index];
    return true;
  }else{
    return false;
  }
}

bool InstMatchGenerator::getNextMatch2( InstMatch& m, QuantifiersEngine* qe ){
  bool success = false;
  Node t;
  do{
    //get the next candidate term t
    t = d_cg->getNextCandidate();
    //if t not null, try to fit it into match m
    if( !t.isNull() ){
      success = getMatch( t, m, qe );
    }
  }while( !success && !t.isNull() );
  return success;
}


/** reset instantiation round */
void InstMatchGenerator::resetInstantiationRound( QuantifiersEngine* qe ){
  if( d_match_pattern.isNull() ){
    for( int i=0; i<(int)d_children.size(); i++ ){
      d_children[i]->resetInstantiationRound( qe );
    }
  }else{
    //DO_THIS?
  }
}

void InstMatchGenerator::reset( Node eqc, QuantifiersEngine* qe ){
  if( d_match_pattern.isNull() ){
    for( int i=0; i<(int)d_children.size(); i++ ){
      d_children[i]->reset( eqc, qe );
    }
    d_partial.clear();
  }else{
    if( d_pattern.getKind()==APPLY_UF || !eqc.isNull() || d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==IFF ){
      d_cg->reset( eqc );
    }else{
      //otherwise, we have a specific equivalence class in mind
      //we are producing matches for f(E) ~ t, where E is a non-ground vector of terms, and t is a ground term 
      //just look in equivalence class of the RHS
      d_cg->reset( d_pattern.getKind()==NOT ? d_pattern[0][1] : d_pattern[1] );
    }
  }
}

bool InstMatchGenerator::getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
  if( d_match_pattern.isNull() ){
    int index = (int)d_partial.size();
    while( index>=0 && index<(int)d_children.size() ){
      if( index>0 ){
        d_partial.push_back( InstMatch( &d_partial[index-1] ) );
      }else{
        d_partial.push_back( InstMatch() );
      }
      if( d_children[index]->getNextMatch( d_partial[index], qe ) ){
        index++;
      }else{
        d_children[index]->reset( Node::null(), qe );
        d_partial.pop_back();
        index--;
      }
    }
    if( index>=0 ){
      m = d_partial.back();
      d_partial.pop_back();
      return true;
    }else{
      return false;
    }
  }else{
    return getNextMatch2( m, qe );
  }
}

Trigger* Trigger::TrTrie::getTrigger2( std::vector< Node >& nodes ){
  if( nodes.empty() ){
    return d_tr;
  }else{
    Node n = nodes.back();
    nodes.pop_back();
    if( d_children.find( n )!=d_children.end() ){
      d_children[n]->getTrigger2( nodes );
    }else{
      return NULL;
    }
  }
}
void Trigger::TrTrie::addTrigger2( std::vector< Node >& nodes, Trigger* t ){
  if( nodes.empty() ){
    d_tr = t;
  }else{
    Node n = nodes.back();
    nodes.pop_back();
    if( d_children.find( n )==d_children.end() ){
      d_children[n] = new TrTrie;
    }
    d_children[n]->addTrigger2( nodes, t );
  }
}

/** trigger static members */
std::map< Node, std::vector< Node > > Trigger::d_var_contains;
int Trigger::trCount = 0;
Trigger::TrTrie Trigger::d_tr_trie;

/** trigger class constructor */
Trigger::Trigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, bool isLitMatch ) : d_quantEngine( qe ), d_f( f ){
  trCount++;
  d_nodes.insert( d_nodes.begin(), nodes.begin(), nodes.end() );
  d_candidates.insert( d_candidates.begin(), nodes.begin(), nodes.end() );
  d_mg = new InstMatchGenerator( d_nodes, qe, isLitMatch );
  //std::cout << "Trigger: ";
  //for( int i=0; i<(int)d_nodes.size(); i++ ){
  //  std::cout << d_nodes[i] << " ";
  //}
  //std::cout << std::endl;
}

void Trigger::computeVarContains2( Node n, Node parent ){
  if( n.getKind()==INST_CONSTANT ){
    if( std::find( d_var_contains[parent].begin(), d_var_contains[parent].end(), n )==d_var_contains[parent].end() ){
      d_var_contains[parent].push_back( n );
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeVarContains2( n[i], parent );
    }
  }
}

void Trigger::resetInstantiationRound(){
  d_mg->resetInstantiationRound( d_quantEngine );
}

void Trigger::reset( Node eqc ){
  d_mg->reset( eqc, d_quantEngine );
}

bool Trigger::getNextMatch( InstMatch& m ){
  return d_mg->getNextMatch( m, d_quantEngine );
}

int Trigger::addInstantiations( InstMatch& baseMatch, bool addSplits ){
  //reset the match generator
  reset( Node::null() );
  //now, try to add instantiation for each match produced
  bool success = true;
  int addedLemmas = 0;
  do{
    InstMatch m;
    if( getNextMatch( m ) ){
      m.add( baseMatch );
      if( d_quantEngine->addInstantiation( d_f, &m, addSplits ) ){
        //std::cout << "Trigger was ";
        //for( int i=0; i<(int)d_nodes.size(); i++ ){
        //  std::cout << d_nodes[i] << " ";
        //}
        //std::cout << std::endl;
        addedLemmas++;
      }
    }else{
      success = false;
    }
  }while( success );
  //return number of lemmas added
  return addedLemmas;
}

Trigger* Trigger::mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, bool isLitMatch, bool keepAll, int trPolicy ){
  bool success = false;
  int counter = 0;
  std::vector< Node > trNodes;
  while( !success ){
    if( !keepAll ){
      //only take nodes that contribute variables to the trigger when added
      std::vector< Node > temp;
      temp.insert( temp.begin(), nodes.begin(), nodes.end() );
      std::random_shuffle( temp.begin(), temp.end() );
      std::map< Node, bool > vars;
      for( int i=0; i<(int)temp.size(); i++ ){
        bool foundVar = false;
        computeVarContains( temp[i] );
        for( int j=0; j<(int)d_var_contains[ temp[i] ].size(); j++ ){
          Node v = d_var_contains[ temp[i] ][j];
          if( vars.find( v )==vars.end() ){
            vars[ v ] = true;
            foundVar = true;
          }
        }
        if( foundVar ){
          trNodes.push_back( temp[i] );
        }
      }
    }else{
      trNodes.insert( trNodes.begin(), nodes.begin(), nodes.end() );
    }
    //check for duplicate?
    if( trPolicy==TRP_MAKE_NEW ){
      success = true;
    }else{
      Trigger* t = d_tr_trie.getTrigger( trNodes );
      if( t ){
        if( trPolicy==TRP_GET_OLD ){
          //just return old trigger
          return t;
        }else{
          counter++;
          if( counter>=3 || keepAll ){  
            //try three random triggers before returning null
            return NULL; 
          }
        }
      }else{
        success = true;
      }
    }
    if( !success ){
      trNodes.clear();
    }
  }
  Trigger* t = new Trigger( qe, f, trNodes, isLitMatch );
  //d_tr_trie.addTrigger( trNodes, t );
  return t;
}

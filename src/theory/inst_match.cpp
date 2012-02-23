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

void InstMatch::makeInternal( EqualityQuery* q ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    if( it->second.hasAttribute(InstConstantAttribute()) ){
      d_map[ it->first ] = q->getInternalRepresentative( it->second );
    }
  }
}

void InstMatch::computeTermVec( QuantifiersEngine* ie, std::vector< Node >& vars, std::vector< Node >& match ){
  for( int i=0; i<(int)vars.size(); i++ ){
    std::map< Node, Node >::iterator it = d_map.find( vars[i] );
    if( it!=d_map.end() && !it->second.isNull() ){
      match.push_back( it->second );
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
    //record arithmetic information?
    if( !initializePatternArithmetic( d_match_pattern ) ){
      if( d_match_pattern.getKind()!=APPLY_UF ){
        Debug("pattern-debug") << "(?) Unknown matching pattern is " << d_match_pattern << std::endl;
      }
    }
    Node op = d_match_pattern.getKind()==APPLY_UF ? d_match_pattern.getOperator() : Node::null();
    if( d_pattern.getKind()!=NOT ){
      //we will be scanning lists trying to find d_match_pattern.getOperator()
      d_cg = new uf::CandidateGeneratorTheoryUf( ith, op );
    }else{
      Assert( d_isLitMatch );
      d_cg = new uf::CandidateGeneratorTheoryUfDisequal( ith, op );
    }
  }
}

bool InstMatchGenerator::initializePatternArithmetic( Node n ){
  if( n.getKind()==PLUS ){
    Assert( d_arith_coeffs.empty() );
    NodeBuilder<> t(kind::PLUS);
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n[i].hasAttribute(InstConstantAttribute()) ){
        if( n[i].getKind()==INST_CONSTANT ){
          d_arith_coeffs[ n[i] ] = Node::null();
        }else if( !initializePatternArithmetic( n[i] ) ){
          Debug("pattern-debug") << "(?) Bad arith pattern = " << n << std::endl;
          d_arith_coeffs.clear();
          return false;
        }
      }else{
        t << n[i];
      }
    }
    if( t.getNumChildren()==0 ){
      d_arith_coeffs[ Node::null() ] = NodeManager::currentNM()->mkConst( Rational(0) ); 
    }else if( t.getNumChildren()==1 ){
      d_arith_coeffs[ Node::null() ]  = t.getChild( 0 );
    }else{
      d_arith_coeffs[ Node::null() ]  = t;
    }
    return true;
  }else if( n.getKind()==MULT ){
    if( n[0].getKind()==INST_CONSTANT ){
      Assert( !n[1].hasAttribute(InstConstantAttribute()) );
      d_arith_coeffs[ n[0] ] = n[1];
      return true;
    }else if( n[1].getKind()==INST_CONSTANT ){
      Assert( !n[0].hasAttribute(InstConstantAttribute()) );
      d_arith_coeffs[ n[1] ] = n[0];
      return true;
    }
  }
  return false;
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
  Assert( !d_match_pattern.isNull() );
  if( d_match_pattern.getKind()!=APPLY_UF ){
    Debug("matching-arith") << "Matching " << t << " " << d_match_pattern << std::endl;
    if( !d_arith_coeffs.empty() ){
      NodeBuilder<> tb(kind::PLUS);
      Node ic = Node::null();
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        Debug("matching-arith") << it->first << " -> " << it->second << std::endl;
        if( !it->first.isNull() ){
          if( m.d_map.find( it->first )==m.d_map.end() ){
            //see if we can choose this to set
            if( ic.isNull() && ( it->second.isNull() || !it->first.getType().isInteger() ) ){
              ic = it->first;
            }
          }else{
            Debug("matching-arith") << "already set " << m.d_map[ it->first ] << std::endl;
            Node tm = m.d_map[ it->first ];
            if( !it->second.isNull() ){
              tm = NodeManager::currentNM()->mkNode( MULT, it->second, tm );
            }
            tb << tm;
          }
        }else{
          tb << it->second;
        }
      }
      if( !ic.isNull() ){
        Node tm;
        if( tb.getNumChildren()==0 ){
          tm = t;
        }else{
          tm = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
          tm = NodeManager::currentNM()->mkNode( MINUS, t, tm );
        }
        if( !d_arith_coeffs[ ic ].isNull() ){
          Assert( !ic.getType().isInteger() );
          Node coeff = NodeManager::currentNM()->mkConst( Rational(1) / d_arith_coeffs[ ic ].getConst<Rational>() );
          tm = NodeManager::currentNM()->mkNode( MULT, coeff, tm );
        }
        m.d_map[ ic ] = Rewriter::rewrite( tm );
        //set the rest to zeros
        for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
          if( !it->first.isNull() ){
            if( m.d_map.find( it->first )==m.d_map.end() ){
              m.d_map[ it->first ] = NodeManager::currentNM()->mkConst( Rational(0) ); 
            }
          }
        }
        Debug("matching-arith") << "Setting " << ic << " to " << tm << std::endl;
        return true;
      }else{
        return false;
      }
    }else{
      return false;
    }
  }else{
    EqualityQuery* q = qe->getEqualityQuery();
    //add m to partial match vector
    std::vector< InstMatch > partial;
    partial.push_back( InstMatch( &m ) );
    //if t is null
    Assert( !t.isNull() );
    Assert( !t.hasAttribute(InstConstantAttribute()) );
    Assert( t.getKind()==APPLY_UF );
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
    if( d_cg ){
      d_cg->resetInstantiationRound();
    }
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
      return d_children[n]->getTrigger2( nodes );
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
  bool retVal = d_mg->getNextMatch( m, d_quantEngine );
  //m.makeInternal( d_quantEngine->getEqualityQuery() );
  return retVal;
}

int Trigger::addInstantiations( InstMatch& baseMatch, int instLimit, bool addSplits ){
  //now, try to add instantiation for each match produced
  bool success = true;
  int addedLemmas = 0;
  do{
    InstMatch m;
    if( getNextMatch( m ) ){
      //m.makeInternal( d_quantEngine->getEqualityQuery() );
      m.add( baseMatch );
      if( d_quantEngine->addInstantiation( d_f, &m, addSplits ) ){
        //std::cout << "Trigger was ";
        //for( int i=0; i<(int)d_nodes.size(); i++ ){
        //  std::cout << d_nodes[i] << " ";
        //}
        //std::cout << std::endl;
        addedLemmas++;
#if 0
        if( instLimit>0 && addedLemmas==instLimit ){
          return addedLemmas;
        }
#endif
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
      std::map< Node, std::vector< Node > > patterns;
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
          for( int j=0; j<(int)d_var_contains[ temp[i] ].size(); j++ ){
            Node v = d_var_contains[ temp[i] ][j];
            patterns[ v ].push_back( temp[i] );
          }
        }
      }
      //now, minimalize the trigger 
      for( int i=0; i<(int)trNodes.size(); i++ ){
        bool keepPattern = false;
        Node n = trNodes[i];
        for( int j=0; j<(int)d_var_contains[ n ].size(); j++ ){
          Node v = d_var_contains[ n ][j];
          if( patterns[v].size()==1 ){
            keepPattern = true;
            break;
          }
        }
        if( !keepPattern ){
          //remove from pattern vector
          for( int j=0; j<(int)d_var_contains[ n ].size(); j++ ){
            Node v = d_var_contains[ n ][j];
            for( int k=0; k<(int)patterns[v].size(); k++ ){
              if( patterns[v][k]==n ){
                patterns[v].erase( patterns[v].begin() + k, patterns[v].begin() + k + 1 );
                break;
              }
            }
          }
          //remove from trigger nodes
          trNodes.erase( trNodes.begin() + i, trNodes.begin() + i + 1 );
          i--;
        }
      }
    }else{
      trNodes.insert( trNodes.begin(), nodes.begin(), nodes.end() );
    }
    //check for duplicate?
    if( trPolicy==TRP_MAKE_NEW ){
      success = true;
      //static int trNew = 0;
      //static int trOld = 0;
      //Trigger* t = d_tr_trie.getTrigger( trNodes );
      //if( t ){
      //  trOld++;
      //}else{
      //  trNew++;
      //}
      //if( (trNew+trOld)%100==0 ){
      //  std::cout << "Trigger new old = " << trNew << " " << trOld << std::endl;
      //}
    }else{
      Trigger* t = d_tr_trie.getTrigger( trNodes );
      if( t ){
        if( trPolicy==TRP_GET_OLD ){
          //just return old trigger
          return t;
        }else{
          return NULL; 
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
  d_tr_trie.addTrigger( trNodes, t );
  return t;
}


bool Trigger::isUsableTrigger( std::vector< Node >& nodes, Node f ){
  for( int i=0; i<(int)nodes.size(); i++ ){
    if( !isUsableTrigger( nodes[i], f ) ){
      return false;
    }
  }
  return true;
}

bool Trigger::isUsable( Node n, Node f ){
  if( n.getAttribute(InstConstantAttribute())==f ){
    if( n.getKind()!=APPLY_UF && n.getKind()!=INST_CONSTANT ){
      return false;
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( !isUsable( n[i], f ) ){
          return false;
        }
      }
      return true;
    }
  }else{
    return true;
  }
}

bool Trigger::isUsableTrigger( Node n, Node f ){
  return n.getAttribute(InstConstantAttribute())==f && n.getKind()==APPLY_UF;
  //return n.hasAttribute(InstConstantAttribute()) && n.getKind()==APPLY_UF && isUsable( n, f );
}
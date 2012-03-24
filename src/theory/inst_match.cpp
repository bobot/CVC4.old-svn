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
#include "theory/uf/theory_uf_candidate_generator.h"
#include "theory/uf/equality_engine_impl.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

void CandidateGeneratorQueue::reset( Node eqc ){
  if( !eqc.isNull() ){
    d_candidates.push_back( eqc );
  }
}
Node CandidateGeneratorQueue::getNextCandidate(){
  if( d_candidates.empty() ){
    return Node::null();
  }else{
    Node n = d_candidates[0];
    d_candidates.erase( d_candidates.begin(), d_candidates.begin() + 1 );
    return n;
  }
}

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
    Debug("matching") << "Add partial " << v << "->" << m << std::endl;
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

void InstMatch::makeComplete( Node f, QuantifiersEngine* qe ){
  for( int i=0; i<(int)qe->d_inst_constants[f].size(); i++ ){
    if( d_map.find( qe->d_inst_constants[f][i] )==d_map.end() ){
      d_map[ qe->d_inst_constants[f][i] ] = qe->getFreeVariableForInstConstant( qe->d_inst_constants[f][i] );
    }
  }
}

void InstMatch::makeInternal( EqualityQuery* q ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    if( it->second.hasAttribute(InstConstantAttribute()) ){
      d_map[ it->first ] = q->getInternalRepresentative( it->second );
    }
  }
}

void InstMatch::makeRepresentative( EqualityQuery* q ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    d_map[ it->first ] = q->getInternalRepresentative( it->second );
  }
}

void InstMatch::computeTermVec( QuantifiersEngine* ie, const std::vector< Node >& vars, std::vector< Node >& match ){
  for( int i=0; i<(int)vars.size(); i++ ){
    std::map< Node, Node >::iterator it = d_map.find( vars[i] );
    if( it!=d_map.end() && !it->second.isNull() ){
      match.push_back( it->second );
    }else{
      match.push_back( ie->getFreeVariableForInstConstant( vars[i] ) );
    }
  }
}
void InstMatch::computeTermVec( const std::vector< Node >& vars, std::vector< Node >& match ){
  for( int i=0; i<(int)vars.size(); i++ ){
    match.push_back( d_map[ vars[i] ] );
  }
}


/** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
void InstMatchTrie::addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index, ImtIndexOrder* imtio ){
  if( index<f[0].getNumChildren() ){
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.d_map[ qe->getInstantiationConstant( f, i_index ) ];
    d_data[n].addInstMatch2( qe, f, m, index+1, imtio );
  }
}

/** exists match */
bool InstMatchTrie::existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, int index, ImtIndexOrder* imtio ){
  if( index==f[0].getNumChildren() ){
    return true;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.d_map[ qe->getInstantiationConstant( f, i_index ) ];
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      if( it->second.existsInstMatch( qe, f, m, modEq, index+1, imtio ) ){
        return true;
      }
    }
    if( modEq ){
      //check modulo equality if any other instantiation match exists
      if( ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine()->hasTerm( n ) ){
        uf::EqClassIterator eqc = uf::EqClassIterator( qe->getEqualityQuery()->getRepresentative( n ), 
                                ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en!=n ){
            std::map< Node, InstMatchTrie >::iterator itc = d_data.find( en );
            if( itc!=d_data.end() ){
              if( itc->second.existsInstMatch( qe, f, m, modEq, index+1, imtio ) ){
                return true;
              }
            }
          }
          ++eqc;
        }
      }
      //for( std::map< Node, InstMatchTrie >::iterator itc = d_data.begin(); itc != d_data.end(); ++itc ){
      //  if( itc->first!=n && qe->getEqualityQuery()->areEqual( n, itc->first ) ){
      //    if( itc->second.existsInstMatch( qe, f, m, modEq, index+1 ) ){
      //      return true;
      //    }
      //  }
      //}
    }
    return false;
  }
}

bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, ImtIndexOrder* imtio ){
  if( !existsInstMatch( qe, f, m, modEq, 0, imtio ) ){
    //std::cout << "~Exists, add." << std::endl;
    addInstMatch2( qe, f, m, 0, imtio );
    return true;
  }else{
    //std::cout << "Exists, fail." << std::endl;
    return false;
  }
}

InstMatchGenerator::InstMatchGenerator( Node pat, QuantifiersEngine* qe, int matchPolicy ) : d_matchPolicy( matchPolicy ){
  initializePattern( pat, qe );
}

InstMatchGenerator::InstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe, int matchPolicy ) : d_matchPolicy( matchPolicy ){
  if( pats.size()==1 ){
    initializePattern( pats[0], qe );
  }else{
    initializePatterns( pats, qe );
  }
}

void InstMatchGenerator::initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe ){
  int childMatchPolicy = d_matchPolicy==MATCH_GEN_EFFICIENT_E_MATCH ? 0 : d_matchPolicy;
  for( int i=0; i<(int)pats.size(); i++ ){
    d_children.push_back( new InstMatchGenerator( pats[i], qe, childMatchPolicy ) );
  }
  d_pattern = Node::null();
  d_match_pattern = Node::null();
  d_cg = NULL;
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
      d_match_pattern = d_match_pattern[1];
    }else if( !d_match_pattern[1].hasAttribute(InstConstantAttribute()) ){
      Assert( d_match_pattern[0].hasAttribute(InstConstantAttribute()) );
      d_match_pattern = d_match_pattern[0];
    }
  }
  int childMatchPolicy = d_matchPolicy==MATCH_GEN_EFFICIENT_E_MATCH ? MATCH_GEN_DEFAULT : d_matchPolicy;
  for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
    if( d_match_pattern[i].hasAttribute(InstConstantAttribute()) ){
      if( d_match_pattern[i].getKind()!=INST_CONSTANT ){
        d_children.push_back( new InstMatchGenerator( d_match_pattern[i], qe, childMatchPolicy ) );
        d_children_index.push_back( i );
      }
    }
  }
  //if lit match, reform boolean predicate as an equality
  if( d_matchPolicy==MATCH_GEN_LIT_MATCH && d_match_pattern.getKind()==APPLY_UF ){
    bool pol = pat.getKind()!=NOT;
    d_pattern = NodeManager::currentNM()->mkNode( IFF, d_match_pattern, NodeManager::currentNM()->mkConst<bool>(pol) );
  }

  Debug("inst-match-gen") << "Pattern is " << d_pattern << ", match pattern is " << d_match_pattern << std::endl;

  //get the equality engine
  Theory* th_uf = qe->getTheoryEngine()->getTheory( theory::THEORY_UF );
  uf::InstantiatorTheoryUf* ith = (uf::InstantiatorTheoryUf*)th_uf->getInstantiator();
  //create candidate generator
  if( d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==IFF ){
    Assert( d_matchPolicy==MATCH_GEN_LIT_MATCH );
    //we will be producing candidates via literal matching heuristics
    d_cg = new uf::CandidateGeneratorTheoryUfEq( ith, d_pattern, d_match_pattern );
  }else if( d_pattern.getKind()==NOT ){
    Node op = d_match_pattern.getKind()==APPLY_UF ? d_match_pattern.getOperator() : Node::null();
    Assert( d_matchPolicy==MATCH_GEN_LIT_MATCH );
    d_cg = new uf::CandidateGeneratorTheoryUfDisequal( ith, op );
    d_eq_class = d_pattern.getKind()==NOT ? d_pattern[0][1] : d_pattern[1];
  }else if( d_match_pattern.getKind()==APPLY_UF ){
    Node op = d_match_pattern.getOperator();
    if( d_matchPolicy==MATCH_GEN_EFFICIENT_E_MATCH ){
      d_cg = new CandidateGeneratorQueue;
      ith->registerCandidateGenerator( d_cg, pat );
    }else{
      //we will be scanning lists trying to find d_match_pattern.getOperator()
      d_cg = new uf::CandidateGeneratorTheoryUf( ith, op );
    }
  }else{
    d_cg = new CandidateGeneratorQueue;
    if( !initializePatternArithmetic( d_match_pattern ) ){
      Debug("inst-match-gen") << "(?) Unknown matching pattern is " << d_match_pattern << std::endl;
    }else{
      Debug("matching-arith") << "Generated arithmetic pattern for " << d_match_pattern << ": " << std::endl;
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
      }
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
          Debug("matching-arith") << "(?) Bad arith pattern = " << n << std::endl;
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

bool InstMatchGenerator::getMatchArithmetic( Node t, InstMatch& m, QuantifiersEngine* qe ){
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
}

/** get match (not modulo equality) */
bool InstMatchGenerator::getMatch( Node t, InstMatch& m, QuantifiersEngine* qe ){
  Debug("matching") << "Matching " << t << " " << d_match_pattern << " ("
                    << m.d_map.size() << ")" << ", " << d_children.size() << std::endl;
  Assert( !d_match_pattern.isNull() );
  if( d_match_pattern.getKind()!=APPLY_UF ){
    return getMatchArithmetic( t, m, qe );
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
            Debug("matching") << "Match in conflict " << t[i] << " and "
                              << d_match_pattern[i] << " because "
                              << partial[0].d_map[d_match_pattern[i]]
                              << std::endl;
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
    std::vector< Node > reps;
    for( int i=0; i<(int)d_children.size(); i++ ){
      Node rep = q->getRepresentative( t[ d_children_index[i] ] );
      reps.push_back( rep );
      d_children[i]->d_cg->reset( rep );
    }

    //combine child matches
    int index = 0;
    while( index>=0 && index<(int)d_children.size() ){
      partial.push_back( InstMatch( &partial[index] ) );
      if( d_children[index]->getNextMatch2( partial[index+1], qe ) ){
        index++;
      }else{
        d_children[index]->d_cg->reset( reps[index] );
        partial.pop_back();
        if( !partial.empty() ){
          partial.pop_back();
        }
        index--;
      }
    }
    if( index>=0 ){
      m = partial.back();
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
    if( !d_eq_class.isNull() ){
      //we have a specific equivalence class in mind
      //we are producing matches for f(E) ~ t, where E is a non-ground vector of terms, and t is a ground term
      //just look in equivalence class of the RHS
      d_cg->reset( d_eq_class );
    }else{
      d_cg->reset( eqc );
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
        if( !d_partial.empty() ){
          d_partial.pop_back();
        }
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



// Currently the implementation doesn't take into account that
// variable should have the same value given.
// TODO use the d_children way perhaps
// TODO replace by a real dictionnary
// We should create a real substitution? slower more precise
// We don't do that often
bool InstMatchGenerator::nonunifiable( TNode t0, const std::vector<Node> & vars){
  if(d_match_pattern.isNull()) return true;

  typedef std::vector<std::pair<TNode,TNode> > tstack;
  tstack stack(1,std::make_pair(t0,d_match_pattern)); // t * pat

  while(!stack.empty()){
    const std::pair<TNode,TNode> p = stack.back(); stack.pop_back();
    const TNode & t = p.first;
    const TNode & pat = p.second;

    // t or pat is a variable currently we consider that can match anything
    if( find(vars.begin(),vars.end(),t) != vars.end() ) continue;
    if( pat.getKind() == INST_CONSTANT ) continue;

    // t and pat are nonunifiable
    if( t.getKind() != APPLY_UF || pat.getKind() != APPLY_UF ) {
      if(t == pat) continue;
      else return true;
    };
    if( t.getOperator() != pat.getOperator() ) return true;

    //put the children on the stack
    for( size_t i=0; i < pat.getNumChildren(); i++ ){
      stack.push_back(std::make_pair(t[i],pat[i]));
    };
  }
  // The heuristic can't find non-unifiability
  return false;
}

/** constructors */
InstMatchGeneratorMulti::InstMatchGeneratorMulti( Node f, std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption ) : 
d_f( f ), d_calculate_matches( false ){
  for( int i=0; i<(int)pats.size(); i++ ){
    d_children.push_back( new InstMatchGenerator( pats[i], qe, matchOption ) );
  }
}

/** reset instantiation round (call this whenever equivalence classes have changed) */
void InstMatchGeneratorMulti::resetInstantiationRound( QuantifiersEngine* qe ){
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i]->resetInstantiationRound( qe );
  }
}

/** reset, eqc is the equivalence class to search in (any if eqc=null) */
void InstMatchGeneratorMulti::reset( Node eqc, QuantifiersEngine* qe ){
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i]->reset( eqc, qe );
  }
  d_calculate_matches = true;
}

void InstMatchGeneratorMulti::calculateMatches( QuantifiersEngine* qe ){
  for( int i=0; i<(int)d_children.size(); i++ ){
    std::vector< InstMatch > newMatches;
    InstMatch m;
    while( d_children[i]->getNextMatch( m, qe ) ){
      newMatches.push_back( m );
    }
    //see if these produce new matches
    
  }
}

/** get the next match.  must call reset( eqc ) before this function. */
bool InstMatchGeneratorMulti::getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
  if( d_calculate_matches ){
    calculateMatches( qe );
    d_calculate_matches = false;
  }
  if( !d_curr_matches.empty() ){
    m = d_curr_matches[0];
    d_curr_matches.erase( d_curr_matches.begin(), d_curr_matches.begin() + 1 );
    return true;
  }else{
    return false;
  }
}

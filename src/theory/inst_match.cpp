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
void InstMatchTrie::addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index ){
  if( index<f[0].getNumChildren() ){
    Node n = m.d_map[ qe->getInstantiationConstant( f, index ) ];
    d_data[n].addInstMatch2( qe, f, m, index+1 );
  }
}

/** exists match */
bool InstMatchTrie::existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, int index ){
  if( index==f[0].getNumChildren() ){
    return true;
  }else{
    Node n = m.d_map[ qe->getInstantiationConstant( f, index ) ];
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      if( it->second.existsInstMatch( qe, f, m, modEq, index+1 ) ){
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
              if( itc->second.existsInstMatch( qe, f, m, modEq, index+1 ) ){
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

bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq ){
  if( !existsInstMatch( qe, f, m, modEq, 0 ) ){
    //std::cout << "~Exists, add." << std::endl;
    addInstMatch2( qe, f, m, 0 );
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
Trigger::Trigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, int matchOption ) : d_quantEngine( qe ), d_f( f ){
  trCount++;
  d_nodes.insert( d_nodes.begin(), nodes.begin(), nodes.end() );
  d_mg = new InstMatchGenerator( d_nodes, qe, matchOption );
  Debug("trigger") << "Trigger for " << f << ": " << std::endl;
  for( int i=0; i<(int)d_nodes.size(); i++ ){
    Debug("trigger") << "   " << d_nodes[i] << std::endl;
  }
  Debug("trigger") << std::endl;
  if( d_nodes.size()==1 ){
    ++(qe->d_statistics.d_triggers);
  }else{
    ++(qe->d_statistics.d_multi_triggers);
  }
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

bool Trigger::getMatch( Node t, InstMatch& m ){
  d_mg->getMatch( t, m, d_quantEngine );
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
      if( d_quantEngine->addInstantiation( d_f, m, addSplits ) ){
        Debug("inst-trigger") << "Trigger was ";
        for( int i=0; i<(int)d_nodes.size(); i++ ){
          Debug("inst-trigger") << d_nodes[i] << " ";
        }
        Debug("inst-trigger") << std::endl;
        //std::cout << "Trigger was ";
        //for( int i=0; i<(int)d_nodes.size(); i++ ){
        //  std::cout  << d_nodes[i] << " ";
        //}
        //std::cout  << std::endl;
        addedLemmas++;
        if( instLimit>0 && addedLemmas==instLimit ){
          return addedLemmas;
        }
      }
    }else{
      success = false;
    }
  }while( success );
  //return number of lemmas added
  return addedLemmas;
}

Trigger* Trigger::mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, int matchOption, bool keepAll, int trOption ){
  std::vector< Node > trNodes;
  if( !keepAll ){
    //only take nodes that contribute variables to the trigger when added
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
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
  if( trOption==TR_MAKE_NEW ){
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
      if( trOption==TR_GET_OLD ){
        //just return old trigger
        return t;
      }else{
        return NULL;
      }
    }
  }
  Trigger* t = new Trigger( qe, f, trNodes, matchOption );
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
/** filter all nodes that have instances */
void Trigger::filterInstances( std::vector< Node >& nodes ){
  std::vector< bool > active;
  active.resize( nodes.size(), true );
  for( int i=0; i<(int)nodes.size(); i++ ){
    for( int j=i+1; j<(int)nodes.size(); j++ ){
      if( active[i] && active[j] ){
        int result = isInstanceOf( nodes[i], nodes[j] );
        if( result==1 ){
          active[j] = false;
        }else if( result==-1 ){
          active[i] = false;
        }
      }
    }
  }
  std::vector< Node > temp;
  for( int i=0; i<(int)nodes.size(); i++ ){
    if( active[i] ){
      temp.push_back( nodes[i] );
    }
  }
  nodes.clear();
  nodes.insert( nodes.begin(), temp.begin(), temp.end() );
}

/** is n1 an instance of n2 or vice versa? */
int Trigger::isInstanceOf( Node n1, Node n2 ){
  if( n1==n2 ){
    return 1;
  }else if( n1.getKind()==n2.getKind() ){
    if( n1.getKind()==APPLY_UF ){
      if( n1.getOperator()==n2.getOperator() ){
        int result = 0;
        for( int i=0; i<(int)n1.getNumChildren(); i++ ){
          if( n1[i]!=n2[i] ){
            int cResult = isInstanceOf( n1[i], n2[i] );
            if( cResult==0 ){
              return 0;
            }else if( cResult!=result ){
              if( result!=0 ){
                return 0;
              }else{
                result = cResult;
              }
            }
          }
        }
        return result;
      }
    }
    return 0;
  }else if( n2.getKind()==INST_CONSTANT ){
    computeVarContains( n1 );
    if( std::find( d_var_contains[ n1 ].begin(), d_var_contains[ n1 ].end(), n2 )!=d_var_contains[ n1 ].end() ){
      return 1;
    }
  }else if( n1.getKind()==INST_CONSTANT ){
    computeVarContains( n2 );
    if( std::find( d_var_contains[ n2 ].begin(), d_var_contains[ n2 ].end(), n1 )!=d_var_contains[ n2 ].end() ){
      return -1;
    }
  }
  return 0;
}

bool Trigger::isVariableSubsume( Node n1, Node n2 ){
  computeVarContains( n1 );
  computeVarContains( n2 );
  for( int i=0; i<(int)d_var_contains[n2].size(); i++ ){
    if( std::find( d_var_contains[n1].begin(), d_var_contains[n1].end(), d_var_contains[n2][i] )==d_var_contains[n1].end() ){
      return false;
    }
  }
  return true;
}

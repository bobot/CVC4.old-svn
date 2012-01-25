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
#include "theory/instantiation_engine.h"
#include "theory/uf/theory_uf_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

InstMatch::InstMatch( InstMatch* m ){
  d_map = m->d_map;
  d_splits = m->d_splits;
}

void InstMatch::setMatch( TNode v, TNode m ){ 
  d_map[v] = m; 
}

bool InstMatch::add( InstMatch& m ){
  for( std::map< TNode, TNode >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( d_map.find( it->first )==d_map.end() ){
      setMatch( it->first, it->second );
    }
  }
  return true;
}

bool InstMatch::merge( uf::InstantiatorTheoryUf* itu, InstMatch& m, bool allowSplit ){
  for( std::map< TNode, TNode >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( d_map.find( it->first )==d_map.end() ){
      setMatch( it->first, it->second );
    }else{
      if( it->second!=d_map[it->first] ){
        if( !itu->areEqual( it->second, d_map[it->first] ) ){
          //split?
          if( allowSplit ){
            addSplit( d_map[ it->first ], it->second );
          }else{
            d_map.clear();
            return false;
          }
        }
      }
    }
  }
  if( allowSplit ){
    //also add splits
    for( std::map< TNode, TNode >::iterator it = m.d_splits.begin(); it != m.d_splits.end(); ++it ){
      addSplit( it->first, it->second );
    }
  }
  return true;
}

//// -1 : keep this, 1 : keep m, 0 : keep both
//int InstMatch::checkSubsume( InstMatch& m ){
//  bool nsubset1 = true;
//  bool nsubset2 = true;
//  for( int i=0; i<(int)d_vars.size(); i++ ){
//    if( m.d_map[ d_vars[i] ]!=d_map[ d_vars[i] ] ){
//      if( d_map[ d_vars[i] ]!=Node::null() ){
//        nsubset1 = false;
//        if( !nsubset2 ) break;
//      }
//      if( m.d_map[ d_vars[i] ]!=Node::null() ){
//        nsubset2 = false;
//        if( !nsubset1 ) break;
//      }
//    }
//  }
//  if( nsubset1 ){
//    return -1;
//  }else if( nsubset2 ){
//    return 1;
//  }else{
//    return 0;
//  }
//}
bool InstMatch::isEqual( InstMatch& m ){
  if( d_map.size()==m.d_map.size() ){
    for( std::map< TNode, TNode >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
      if( d_map.find( it->first )==d_map.end() || it->second!=d_map[ it->first ] ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}
void InstMatch::debugPrint( const char* c ){
  for( std::map< TNode, TNode >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    Debug( c ) << "   " << it->first << " -> " << it->second << std::endl;
  }
  if( !d_splits.empty() ){
    Debug( c ) << "   Conditions: ";
    for( std::map< TNode, TNode >::iterator it = d_splits.begin(); it !=d_splits.end(); ++it ){
      Debug( c ) << it->first << " = " << it->second << " ";
    }
    Debug( c ) << std::endl;
  }
}

void InstMatch::computeTermVec( InstantiationEngine* ie, std::vector< Node >& vars, std::vector< Node >& match ){
  for( int i=0; i<(int)vars.size(); i++ ){
    if( d_map.find( vars[i] )!=d_map.end() ){
      match.push_back( d_map[ vars[i] ] );
    }else{
      match.push_back( ie->getFreeVariableForInstConstant( vars[i] ) );
    }
  }
}

void InstMatch::addSplit( TNode n1, TNode n2 ){
  if( n2<n1 ){
    TNode ntemp = n1;
    n1 = n2;
    n2 = ntemp;
  }
  if( d_splits.find( n1 )!=d_splits.end() ){
    if( d_splits[n1]!=n2 ){
      addSplit( d_splits[n1], n2 );
    }
  }else{
    d_splits[n1] = n2;
  }
}

std::map< TNode, std::vector< InstMatchGenerator* > > InstMatchGenerator::d_iter[3];
int InstMatchGenerator::d_imgCount = 0;

/** InstMatchGenerator constructor */
InstMatchGenerator::InstMatchGenerator( int op, TNode eq ) : d_operation( op ), d_eq( eq ), d_mg_i(-1){
  d_imgCount++;
  //if( d_imgCount%1000==0 ){
  //  std::cout << "img count = " << d_imgCount << std::endl;
  //}
  if( op==0 ){
    if( eq!=Node::null() && eq.getKind()!=NOT && eq[0].getKind()==INST_CONSTANT && !eq[1].hasAttribute(InstConstantAttribute()) ){
      InstMatch m;
      d_partial.push_back( m );
      d_partial[0].setMatch( eq[0], eq[1] );
    }
  }else if( op==1 ){
    //if we are merging the arguments in eq, calculate children now
    InstMatch m;
    d_partial.push_back( m );
    if( eq!=Node::null() ){
      for( int j=0; j<(int)eq[0].getNumChildren(); j++ ){
        if( eq[0][j].hasAttribute(InstConstantAttribute()) ){
          if( eq[0][j].getKind()==APPLY_UF ){
            d_children.push_back( mkInstMatchGeneratorModEq( eq[0][j], eq[1][j], true ) );
          }else if( eq[0][j].getKind()==INST_CONSTANT ){
            d_partial[0].setMatch( eq[0][j], eq[1][j] );
          }
        }
      }
    }
  }
  d_can_produce_matches = true;
  d_index = 0;
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( int op, TNode eq ){
  Debug( "quant-uf-iter" ) << "mkInstMatchGenerator " << eq << " " << op << std::endl;
  InstMatchGenerator* mi = new InstMatchGenerator( op, eq );
  d_iter[op][eq].push_back( mi );
  return mi;
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( bool isCombine){
  Node nl;
  return mkInstMatchGenerator( isCombine ? 0 : 1, nl );
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGeneratorModEq( TNode t, TNode s, bool isEq ){
  Debug( "quant-uf-iter" ) << "mkInstMatchGenerator " << t << " " << s << " " << isEq << std::endl;
  Assert( t.hasAttribute(InstConstantAttribute()) ); 
  Kind knd = t.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  Node eq = NodeManager::currentNM()->mkNode( knd, t, s );
  return mkInstMatchGenerator( 0, isEq ? eq : eq.notNode() );
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( TNode t, TNode s ){
  Debug( "quant-uf-iter" ) << "mkInstMatchGenerator " << t << " " << s << std::endl;
  Assert( t.hasAttribute(InstConstantAttribute()) ); 
  if( t.getKind()==INST_CONSTANT ){
    return mkInstMatchGeneratorModEq( t, s, true );
  }else{
    Assert( t.getKind()==APPLY_UF );
    Assert( s.getKind()==APPLY_UF );
    Assert( t.getOperator()==s.getOperator() );
    Kind knd = t.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
    Node eq = NodeManager::currentNM()->mkNode( knd, t, s );
    return mkInstMatchGenerator( 1, eq );
  }
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGeneratorAny( TNode t ){
  Assert( t.getKind()==APPLY_UF );
  Assert( t.hasAttribute(InstConstantAttribute()) ); 
  return mkInstMatchGenerator( 2, t );
}

void InstMatchGenerator::addAnyMatchPair( TNode t, TNode g ){
  InstMatchGenerator* mg;
  if( d_iter[2][t].empty() ){
    mg = mkInstMatchGeneratorAny( t );
  }else{
    mg = d_iter[2][t][0];
  }
  mg->d_children.push_back( mkInstMatchGenerator( t, g ) );
}

//void InstMatchGenerator::resetInstantiationRoundAll( uf::InstantiatorTheoryUf* itu ){
//  for( int i=0; i<3; i++ ){
//    for( std::map< Node, std::vector< InstMatchGenerator* > >::iterator it = d_iter[i].begin(); it != d_iter[i].end(); ++it ){
//      for( int j=0; j<(int)it->second.size(); j++ ){
//        it->second[j]->d_valid = true;
//      }
//    }
//  }
//  for( int i=0; i<3; i++ ){
//    for( std::map< Node, std::vector< InstMatchGenerator* > >::iterator it = d_iter[i].begin(); it != d_iter[i].end(); ++it ){
//      for( int j=0; j<(int)it->second.size(); j++ ){
//        it->second[j]->resetInstantiationRound( itu );
//      }
//    }
//  }
//}


//if equivalence classes change, this function should be called at least once before getNextMatch( itu ) is called
void InstMatchGenerator::resetInstantiationRound( uf::InstantiatorTheoryUf* itu ){
  Debug("quant-uf-iter") << "reset instantiation round " << d_operation << " " << d_eq << " " << (getMaster()==this) << std::endl;
  if( getMaster()==this ){
    if( d_eq!=Node::null() ){
      if( d_operation==0 ){
        //invalidate children
        bool isEq = d_eq.getKind()==NOT;
        Node eq = d_eq.getKind()==NOT ? d_eq[0] : d_eq;
        Node f = eq[0].getAttribute(InstConstantAttribute());
        for( std::map< TNode, InstMatchGenerator* >::iterator it = d_lit_children_map.begin(); it != d_lit_children_map.end(); ++it ){
          d_children_valid[ it->second ] = true;
          if( isEq ){
            if( eq[1].getAttribute(InstConstantAttribute())!=f ){
              d_children_valid[ it->second ] = itu->areEqual( it->first, eq[1] );
            }
          }else{
            if( eq[1].getAttribute(InstConstantAttribute())==f ){
              d_children_valid[ it->second ] = itu->areDisequal( it->first[0], it->first[1] );
            }else{
              d_children_valid[ it->second ] = itu->areDisequal( it->first, eq[1] );
            }
          }
        }
      }else if( d_operation==1 ){
        //if a ground argument is not equal, then this is currently invalid
        for( int j=0; j<(int)d_eq[0].getNumChildren(); j++ ){
          if( !d_eq[0][j].hasAttribute(InstConstantAttribute()) &&
              !itu->areEqual( d_eq[0][j], d_eq[0][j] ) ){
            d_can_produce_matches = false;
            return;
          }
        }
      }
      //else if( d_operation==2 ){
      //  //DO_THIS?
      //}
    }
    Debug("quant-uf-iter") << "reset instantiation round (2)" << std::endl;
    if( d_mg_i+1<getNumCurrentMatches() ){
      d_can_produce_matches = true;
    }else if( !d_can_produce_matches ){
      //if we had completed all matches previously, then at least one child must produce a new match
      for( int i=0; i<(int)d_children.size(); i++ ){
        if( isChildValid( i ) ){
          d_children[i]->resetInstantiationRound( itu );
          if( d_children[i]->d_can_produce_matches ){
            d_can_produce_matches = true;
          }
        }
      }
      if( !d_can_produce_matches ){
        //or, if we can produce new children
        d_can_produce_matches = calculateChildren( itu );
      }
    }
    Debug("quant-uf-iter") << "can produce matches = " << d_can_produce_matches << std::endl;
    if( d_can_produce_matches ){
      //take necessary action for preparing for new matches
      if( isCombine() ){
        //start over from first child
        d_index = 0;
      }else{
        //must reset all children
        for( int i=0; i<(int)d_children.size(); i++ ){
          d_children[i]->reset();
        }
        if( !d_partial.empty() ){
          d_partial.erase( d_partial.begin() + 1, d_partial.end() );
        }
      }
    }
  }else{
    if( d_mg_i+1<getNumCurrentMatches() ){
      d_can_produce_matches = true;
    }else{
      getMaster()->resetInstantiationRound( itu );
      d_can_produce_matches = getMaster()->d_can_produce_matches;
    }
  }
  Debug("quant-uf-iter") << "done reset instantiation round." << std::endl;
}

//reset the inst match generator (repeat the matches is says it has generated)
void InstMatchGenerator::reset(){
  d_mg_i = -1;
}

/** get current match */
InstMatch* InstMatchGenerator::getCurrent(){
  if( d_mg_i>=0 && d_mg_i<(int)getMaster()->getNumCurrentMatches() ){
    return getMaster()->getCurrentMatch( d_mg_i ); 
  }else{
    return NULL;
  }
}

/** get next match */
//pre condition -1 <= d_mg_i < (int)getMaster()->getNumCurrentMatches()
//post condition: return=true, then 0 <= d_mg_i < (int)getMaster()->getNumCurrentMatches()
bool InstMatchGenerator::getNextMatch( uf::InstantiatorTheoryUf* itu ){
  if( d_can_produce_matches ){
    d_mg_i++;
    Debug( "quant-uf-iter" ) << d_eq << " " << d_operation << " getNextMatch ";
    Debug( "quant-uf-iter" ) << this << " " << d_mg_i << " " << getNumCurrentMatches() << std::endl;
    //std::cout << d_eq << " " << d_operation << " getNextMatch ";
    //std::cout << this << " " << d_mg_i << " " << getNumCurrentMatches() << std::endl;
    if( d_mg_i<getNumCurrentMatches() ){
      Debug( "quant-uf-iter" ) << d_eq << " " << d_operation << "  returned (existing) match " << d_mg_i << std::endl;
      //std::cout << d_eq << " " << d_operation << " returned (existing) match " << d_mg_i << std::endl;
      getCurrent()->debugPrint( "quant-uf-iter" );
      return true;
    }else if( getMaster()->calculateNextMatch( itu ) ){
      Debug( "quant-uf-iter" ) << d_eq << " " << d_operation << " " << d_mg_i << " " << getNumCurrentMatches() << std::endl;
      //std::cout << d_eq << " " << d_operation << " calculated next match, ";
      //std::cout << this << " " << d_mg_i << " " << getNumCurrentMatches() << std::endl;
      Assert( d_mg_i<getNumCurrentMatches() );
      Debug( "quant-uf-iter" ) << this << " returned match " << d_mg_i << std::endl;
      getCurrent()->debugPrint( "quant-uf-iter" );
      return true;
    }else{
      d_mg_i--;
      d_can_produce_matches = false;
    }
  }
  return false;
}

/** add instantiation match to vector, return true if not redundant */
bool InstMatchGenerator::addInstMatch( InstMatch& m ){
  Assert( getMaster()==this );
  for( int i=0; i<getNumCurrentMatches(); i++ ){
    if( getCurrentMatch( i )->isEqual( m ) ){
      return false;
    }
  }
  d_mg.push_back( m );
  return true;
}

/** get num current matches */
int InstMatchGenerator::getNumCurrentMatches(){
  if( getMaster()==this ){
    return (int)d_mg.size();
  }else{
    return getMaster()->getNumCurrentMatches();
  }
}
/** get current match */
InstMatch* InstMatchGenerator::getCurrentMatch( int i ){
  if( getMaster()==this ){
    return &d_mg[i];
  }else{
    return getMaster()->getCurrentMatch( i );
  }
}

//post-condition: if return=true, then d_children must have grown by at least one
bool InstMatchGenerator::calculateChildren( uf::InstantiatorTheoryUf* itu ){
  Assert( getMaster()==this );
  if( d_operation==0 && d_eq!=Node::null() ){
    if( d_eq.getKind()!=NOT && d_eq[0].getKind()==INST_CONSTANT && !d_eq[1].hasAttribute(InstConstantAttribute()) ){
      return false;
    }
    Debug( "quant-uf-iter" ) << "calulcate children " << d_eq << std::endl;
    //see if there are any new match candidates
    bool isEq = d_eq.getKind()!=NOT;
    Node eq = d_eq.getKind()==NOT ? d_eq[0] : d_eq;
    Node f = eq[0].getAttribute(InstConstantAttribute());
    itu->calculateEIndLitCandidates( eq[0], eq[1], f, isEq );
    int index = isEq ? 0 : 1;
    bool childAdded = false;
    for( int i=0; i<(int)itu->d_litMatchCandidates[index][eq[0]][eq[1]].size(); i++ ){
      Node m = itu->d_litMatchCandidates[index][eq[0]][eq[1]][i];
      //std::cout << "lit match candidate " << m << " for " << d_eq << std::endl;
      if( d_lit_children_map.find( m )==d_lit_children_map.end() ){
        InstMatchGenerator* mg;
        if( isEq ){
          if( eq[1].getAttribute(InstConstantAttribute())==f ){
            // equality between two patterns
            // found m, where eq[0],eq[1] share top symbol with a term in eq_class( m )
            mg = mkInstMatchGenerator( false );
            mg->d_children.push_back( mkInstMatchGeneratorModEq( eq[0], m, true ) );
            mg->d_children.push_back( mkInstMatchGeneratorModEq( eq[1], m, true ) );
          }else{
            // equality between pattern and ground term
            // found m = eq[1], eq[0] and m share top symbol
            mg = mkInstMatchGenerator( eq[0], m );
            //only valid on subsequent iterations if m = eq[1]
          }
        }else{
          if( eq[1].getAttribute(InstConstantAttribute())==f ){
            // disequality between two patterns
            // we found m[0] != m[1], where eq[i] shares top symbol with a term in eq_class( m[i] ), for i=0,1
            mg = mkInstMatchGenerator( false );
            mg->d_children.push_back( mkInstMatchGeneratorModEq( eq[0], m[0], true ) );
            mg->d_children.push_back( mkInstMatchGeneratorModEq( eq[1], m[1], true ) );
            //only valid on subsequent iterations if m[0] != m[1]
          }else{
            // disequality between pattern and ground term
            // we found m != eq[1], eq[0] and m share top symbol
            mg = mkInstMatchGeneratorModEq( eq[0], m, true );
            //only valid on subsequent iterations if m != eq[1]
          }
        }
        d_children.push_back( mg );
        d_lit_children_map[m] = mg;
        childAdded = true;
      }
    }
    return childAdded;
  }else{
    return false;
  }
}

bool InstMatchGenerator::calculateNextMatch( uf::InstantiatorTheoryUf* itu ){
  Assert( getMaster()==this );
  Debug( "quant-uf-iter" ) << "calc next match " << d_operation << " " << d_eq << std::endl;
  if( isCombine() ){
    Debug( "quant-uf-iter" ) << d_index << " " << (int)d_children.size() << std::endl;
    //get the next match
    bool success;
    do{
      if( d_index==(int)d_children.size() ){
        //get more children
        if( !calculateChildren( itu ) ){
          return false;
        }
      }
      //std::cout << "check child " << d_children[d_index] << std::endl;
      success = isChildValid( d_index ) ? d_children[d_index]->getNextMatch( itu ) : false;
      if( !success ){
        d_index++;
      }
    }while( !success );
    Assert( d_children[d_index]->getCurrent()!=NULL );
    if( addInstMatch( *d_children[d_index]->getCurrent() ) ){  //if we have not seen this match before
      return true;
    }else{
      return calculateNextMatch( itu );
    }
  }else{
    if( d_partial.empty() ){
      Assert( d_children.empty() );
      return false;
    }else{
      // i is the index of the child we are trying to fit into our merged match
      int i = (int)d_partial.size()-1;
      //until we have created a merge for all children
      while( i!=(int)d_children.size() ){
        InstMatch combined;
        bool success = false;
        //get the next match
        while( !success && d_children[i]->getNextMatch( itu ) ){
          combined = InstMatch( *d_children[i]->getCurrent() );
          //see if it merges into the current built merge (stored in d_partial)
          success = combined.merge( itu, d_partial[i] );
        }
        //Assert( !d_children[i]->empty() );
        if( !success ){
          if( i==0 ){  //we will not produce any more matches
            return false;
          }else{  //backtrack
            d_children[i]->reset();
            d_partial.pop_back();
            i--;
          }
        }else{  //proceed to next match
          d_partial.push_back( InstMatch( &combined ) );
          i++;
        }
      }
      bool addedMatch = addInstMatch( d_partial[ d_children.size() ] );
      d_partial.pop_back();
      if( addedMatch ){ 
        return true;
      }else{
        return calculateNextMatch( itu );
      }
    }
  }
}

/** trigger static members */
std::map< Node, std::vector< Node > > Trigger::d_var_contains;

/** trigger class constructor */
Trigger::Trigger( InstantiationEngine* ie, Node f, std::vector< Node >& nodes, bool keepAll ) : d_instEngine( ie ), d_f( f ){
  if( keepAll ){
    d_nodes.insert( d_nodes.begin(), nodes.begin(), nodes.end() );
  }else{
    for( int i=0; i<(int)nodes.size(); i++ ){
      addNode( nodes[i] );
    }
  }
  d_candidates.insert( d_candidates.begin(), nodes.begin(), nodes.end() );
  d_valid = true;
  d_mg = mkMatchGenerator( ie, f, d_nodes );
  d_next = NULL;
}

/** trigger class constructor */
Trigger::Trigger( InstantiationEngine* ie, Node f, std::vector< Node >& candidates, Trigger* prev ) : d_instEngine( ie ), d_f( f ){
  Debug("trigger") << "constructing trigger..." << std::endl;
  //make this the next unique trigger from prev
  if( prev->d_nodes.size()==candidates.size() ){
    //if prev has all nodes from candidates, make subset of candidates 
    // that contribute a new variable
    for( int i=0; i<(int)candidates.size(); i++ ){
      addNode( candidates[i] );
    }
    //valid if resulting trigger is a strict subset of candidates
    d_valid = d_nodes.size()<candidates.size();
  }else{
    d_valid = false;
  }
  d_candidates.insert( d_candidates.begin(), candidates.begin(), candidates.end() );
  d_mg = mkMatchGenerator( ie, f, d_nodes );
  d_next = NULL;
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

bool Trigger::addNode( Node n ){
  Assert( std::find( d_nodes.begin(), d_nodes.end(), n )==d_nodes.end() );
  bool success = false;
  computeVarContains( n );
  for( int i=0; i<(int)d_var_contains[n].size(); i++ ){
    Node v = d_var_contains[n][i];
    if( d_vars.find( v )==d_vars.end() ){
      d_vars[ v ] = true;
      success = true;
    }
  }
  if( success ){
    d_nodes.push_back( n );
  }
  return success;
}

Trigger* Trigger::getNextTrigger(){
  if( !d_next && d_valid ){
    d_next = new Trigger( d_instEngine, d_f, d_candidates, this );
  }
  return d_next;
}

InstMatchGenerator* Trigger::mkMatchGenerator( InstantiationEngine* ie, Node f, std::vector< Node >& nodes ){
  if( nodes.size()==1 ){
    return mkMatchGenerator( ie, f, nodes[0] );
  }else{
    InstMatchGenerator* emg = InstMatchGenerator::mkInstMatchGenerator( false );
    for( int i=0; i<(int)nodes.size(); i++ ){
      emg->d_children.push_back( mkMatchGenerator( ie, f, nodes[i] ) );
    }
    return emg;
  }
}

InstMatchGenerator* Trigger::mkMatchGenerator( InstantiationEngine* ie, Node f, Node n ){
  if( n.getKind()==APPLY_UF && n.getType()!=NodeManager::currentNM()->booleanType() ){
    return InstMatchGenerator::mkInstMatchGeneratorAny( n );
  }else{
    bool pol = n.getKind()!=NOT;
    Node eq = n.getKind()==NOT ? n[0] : n;
    Node t[2];
    if( eq.getKind()==EQUAL || eq.getKind()==IFF ){
      bool swap = eq[0].getAttribute(InstConstantAttribute())!=f;
      t[0] = eq[swap ? 1 : 0];
      t[1] = eq[swap ? 0 : 1];
    }else{
      t[0] = eq;
      t[1] = NodeManager::currentNM()->mkConst<bool>(pol);
      pol = true;
    }
    Assert( t[0].getAttribute(InstConstantAttribute())==f );
    if( ie->isPhaseReq( eq ) ){
      //we know this literal must be matched with this polarity
      return InstMatchGenerator::mkInstMatchGeneratorModEq( t[0], t[1], pol );
    }else{
      //this literal can be matched with either polarity
      if( false ){ //if( t[0].getType()==NodeManager::currentNM()->booleanType() ) {
        //for boolean apply uf, just use an any match generator
        return InstMatchGenerator::mkInstMatchGeneratorAny( t[0] );
      }else{
        InstMatchGenerator* ret = InstMatchGenerator::mkInstMatchGenerator( true );
        ret->d_children.push_back( InstMatchGenerator::mkInstMatchGeneratorModEq( t[0], t[1], pol ) );  //prefer the polarity it has been given
        ret->d_children.push_back( InstMatchGenerator::mkInstMatchGeneratorModEq( t[0], t[1], !pol ) );
        return ret;
      }
    }
  }
}

void Trigger::resetInstantiationRound( uf::InstantiatorTheoryUf* itu ){
  d_mg->resetInstantiationRound( itu );
  if( d_next ){
    d_next->resetInstantiationRound( itu );
  }
}

bool Trigger::addInstantiation( uf::InstantiatorTheoryUf* itu, InstMatch& baseMatch, bool addSplits, int triggerThresh ){
  if( d_valid ){
    //std::cout << "Trigger is ";
    //for( int i=0; i<(int)d_nodes.size(); i++ ){
    //  std::cout << d_nodes[i] << " ";
    //}
    //std::cout << std::endl;
    Debug("trigger") << "trigger: try to add new instantiation..." << std::endl;
    //std::cout << "trigger: try to add new instantiation..." << std::endl;
    int counter = 0;
    while( d_mg->getNextMatch( itu ) ){
      Debug("trigger") << "trigger: made match." << std::endl;
      InstMatch temp( d_mg->getCurrent() );
      temp.add( baseMatch );
      Debug("trigger") << "trigger: add instantiation..." << std::endl;
#if 1
      if( d_instEngine->addInstantiation( d_f, &temp, addSplits ) ){
        return true;
      }
#elif 0
      if( d_instEngine->addInstantiation( d_f, &temp, addSplits ) ){
        if( d_mg->d_operation==2 && d_mg->d_index<d_mg->d_children.size() ){
          //move to next index
          d_mg->d_index++;
          counter++;
        }else{
          return true;
        }
      }
#else
      if( d_instEngine->addInstantiation( d_f, &temp, addSplits ) ){
        counter++;
        if( counter>3 ){
          return true;
        }
      }
#endif
    }
    if( counter>0 ){
      return true;
    }
    Debug("trigger") << "trigger: failed." << std::endl;
    //std::cout << "trigger: failed." << std::endl;
    if( triggerThresh>0 ){
      Debug("trigger") << "trigger: get next trigger..." << std::endl;
      //std::cout << "trigger: get next trigger..." << std::endl;
      Trigger* t = getNextTrigger();
      if( t && t->addInstantiation( itu, baseMatch, addSplits, triggerThresh-1 ) ){
        return true;
      }
    }else{
      Debug("trigger") << "trigger: return false" << std::endl;
      //std::cout << "trigger: return false" << std::endl;
    }
  }
  return false;
}

//
//void QuantMatchGenerator::reset(){
//  //for( int i=0; i<(int)d_auto_gen.size(); i++ ){
//  //  d_auto_gen[i]->reset();
//  //}
//  //for( int i=0; i<(int)d_auto_gen.size(); i++ ){
//  //  d_auto_gen[i]->reset();
//  //}
//  //for( int i=0; i<(int)d_lit_match.size(); i++ ){
//  //  d_lit_match[i]->reset();
//  //}
//}
//
//void QuantMatchGenerator::collectPatTerms( Node n, std::vector< Node >& patTerms ){
//  if( n.getKind()==APPLY_UF && n.getAttribute(InstConstantAttribute())==d_f  ){
//    if( std::find( patTerms.begin(), patTerms.end(), n )==patTerms.end() ){
//      patTerms.push_back( n );
//    }
//  }else if( n.getKind()!=FORALL ){
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      collectPatTerms( n[i], patTerms );
//    }
//  }
//}
////
////void QuantMatchGenerator::collectLiterals( Node n, std::vector< Node >& litPatTerms, bool reqPol, bool polarity ){
////  //check if this is a literal
////  if( d_instEngine->getTheoryEngine()->getPropEngine()->isSatLiteral( n ) && n.getKind()!=NOT ){
////    if( std::find( litPatTerms.begin(), litPatTerms.end(), n )==litPatTerms.end() ){
////      litPatTerms.push_back( n );
////    }
////    if( reqPol ){
////      d_phaseReq[ n ] = polarity;
////    }
////  }else{
////    bool newReqPol = false;
////    bool newPolarity = true;
////    if( reqPol ){
////      if( n.getKind()==NOT ){
////        newReqPol = true;
////        newPolarity = !polarity;
////      }else if( n.getKind()==OR || n.getKind()==IMPLIES ){
////        if( !polarity ){
////          newReqPol = true;
////          newPolarity = false;
////        }
////      }else if( n.getKind()==AND ){
////        if( polarity ){
////          newReqPol = true;
////          newPolarity = true;
////        }
////      }
////    }
////    if( newReqPol ){
////      for( int i=0; i<(int)n.getNumChildren(); i++ ){
////        if( n.getKind()==IMPLIES && i==0 ){
////          collectLiterals( n[i], litPatTerms, newReqPol, !newPolarity );
////        }else{
////          collectLiterals( n[i], litPatTerms, newReqPol, newPolarity );
////        }
////      }
////    }
////  }
////}
//
///** add pattern */
//void QuantMatchGenerator::addUserPattern( Node pat ) {
//  //add to generators
//  std::vector< Node > nodes;
//  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
//    nodes.push_back( pat[i] );
//  }
//  d_user_gen.push_back( new Trigger( d_instEngine, d_f, nodes, true ) );
//}
//
//Trigger* QuantMatchGenerator::getAutoGenTrigger(){
//  if( !d_auto_gen_trigger ){
//    collectPatTerms( d_instEngine->getCounterexampleBody( d_f ), d_patTerms );
//    d_auto_gen_trigger = new Trigger( d_instEngine, d_f, d_patTerms, true );
//    //std::cout << "produced auto trigger" << std::endl;
//  }
//  return d_auto_gen_trigger;
//}

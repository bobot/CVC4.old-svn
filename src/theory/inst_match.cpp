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

InstMatch::InstMatch( Node f, InstantiationEngine* ie ){
  d_computeVec = true;
  for( int i=0; i<(int)ie->d_inst_constants[f].size(); i++ ){
    d_vars.push_back( ie->d_inst_constants[f][i] );
  }
}
InstMatch::InstMatch( InstMatch* m ){
  d_computeVec = true;
  d_vars.insert( d_vars.begin(), m->d_vars.begin(), m->d_vars.end() );
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m->d_map[ d_vars[i] ] );
    }
  }
  d_splits = m->d_splits;
}

bool InstMatch::add( InstMatch& m ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m.d_map[ d_vars[i] ] );
    }
  }
  return true;
}

bool InstMatch::merge( InstMatch& m, bool allowSplit ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m.d_map[ d_vars[i] ] );
    }else if( m.d_map[ d_vars[i] ]!=Node::null() ){
      if( d_map[ d_vars[i] ]!=m.d_map[ d_vars[i] ] ){
        //split?
        if( allowSplit ){
          addSplit( d_map[ d_vars[i] ], m.d_map[ d_vars[i] ] );
        }else{
          d_map.clear();
          return false;
        }
      }
    }
  }
  if( allowSplit ){
    //also add splits
    for( std::map< Node, Node >::iterator it = m.d_splits.begin(); it != m.d_splits.end(); ++it ){
      addSplit( it->first, it->second );
    }
  }
  return true;
}

// -1 : keep this, 1 : keep m, 0 : keep both
int InstMatch::checkSubsume( InstMatch& m ){
  bool nsubset1 = true;
  bool nsubset2 = true;
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( m.d_map[ d_vars[i] ]!=d_map[ d_vars[i] ] ){
      if( d_map[ d_vars[i] ]!=Node::null() ){
        nsubset1 = false;
        if( !nsubset2 ) break;
      }
      if( m.d_map[ d_vars[i] ]!=Node::null() ){
        nsubset2 = false;
        if( !nsubset1 ) break;
      }
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
bool InstMatch::isEqual( InstMatch& m ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( m.d_map[ d_vars[i] ]!=d_map[ d_vars[i] ] ){
      return false;
    }
  }
  return true;
}
void InstMatch::debugPrint( const char* c ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    Debug( c ) << "   " << d_vars[i] << " -> " << d_map[ d_vars[i] ] << std::endl;
  }
  if( !d_splits.empty() ){
    Debug( c ) << "   Conditions: ";
    for( std::map< Node, Node >::iterator it = d_splits.begin(); it !=d_splits.end(); ++it ){
      Debug( c ) << it->first << " = " << it->second << " ";
    }
    Debug( c ) << std::endl;
  }
}
bool InstMatch::isComplete( InstMatch* mbase ){
  Assert( !mbase || getQuantifier()==mbase->getQuantifier() );
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() &&
        ( !mbase || mbase->d_map[ d_vars[i] ]==Node::null() ) ){
      return false;
    }
  }
  return true;
}

void InstMatch::computeTermVec(){
  if( d_computeVec ){
    d_match.clear();
    for( int i=0; i<(int)d_vars.size(); i++ ){
      if( d_map[ d_vars[i] ]!=Node::null() ){
        d_match.push_back( d_map[ d_vars[i] ] );
      }else{
        //if integer or real, make zero
        TypeNode tn = d_vars[i].getType();
        if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
          Rational z(0);
          d_match.push_back( NodeManager::currentNM()->mkConst( z ) );
        }else{
          d_match.push_back( NodeManager::currentNM()->mkVar( tn ) );
        }
      }
    }
    d_computeVec = false;
  }
}

void InstMatch::addSplit( Node n1, Node n2 ){
  if( n2<n1 ){
    Node ntemp = n1;
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

Node InstMatch::getQuantifier() { 
  return d_vars[0].getAttribute(InstConstantAttribute()); 
}

bool InstMatchGroup::merge( InstMatchGroup& mg )
{
  std::vector< InstMatch > newMatches;
  for( int l=0; l<(int)d_matches.size(); l++ ){
    for( int k=0; k<(int)mg.d_matches.size(); k++ ){
      InstMatch temp( &d_matches[l] );
      if( temp.merge( mg.d_matches[k] ) ){
        newMatches.push_back( temp );
      }
    }
  }
  d_matches.clear();
  d_matches.insert( d_matches.begin(), newMatches.begin(), newMatches.end() );
  removeRedundant();
  return (d_matches.size()>0);
}

void InstMatchGroup::add( InstMatchGroup& mg ){
  if( !mg.d_matches.empty() ){
    d_matches.insert( d_matches.end(), mg.d_matches.begin(), mg.d_matches.end() );
  }
}

void InstMatchGroup::combine( InstMatchGroup& mg ){
  InstMatchGroup temp( this );
  merge( mg );
  add( temp );
  add( mg );
  removeDuplicate();
}

void InstMatchGroup::addComplete( InstMatchGroup& mg, InstMatch* mbase ){
  for( int i=0; i<(int)mg.d_matches.size(); i++ ){
    if( mg.d_matches[i].isComplete( mbase ) ){
      if( mbase ){
        mg.d_matches[i].add( *mbase );
      }
      d_matches.push_back( mg.d_matches[i] );
      mg.d_matches.erase( mg.d_matches.begin() + i, mg.d_matches.begin() + i + 1 );
      i--;
    }
  }
}

void InstMatchGroup::removeRedundant(){
  std::vector< bool > active;
  active.resize( d_matches.size(), true );
  for( int k=0; k<(int)d_matches.size(); k++ ){
    for( int l=(k+1); l<(int)d_matches.size(); l++ ){
      if( k!=l && active[k] && active[l] ){
        int result = d_matches[k].checkSubsume( d_matches[l] );
        if( result==1 ){
          active[k] = false;
        }else if( result==-1 ){
          active[l] = false;
        }
      }
    }
  }
  std::vector< InstMatch > temp;
  temp.insert( temp.begin(), d_matches.begin(), d_matches.end() );
  d_matches.clear();
  for( int i=0; i<(int)temp.size(); i++ ){
    if( active[i] ){
      d_matches.push_back( temp[i] );
    }
  }
}
bool InstMatchGroup::contains( InstMatch& m ){
  for( int k=0; k<(int)d_matches.size(); k++ ){
    if( d_matches[k].isEqual( m ) ){
      return true;
    }
  }
  return false;
}
void InstMatchGroup::removeDuplicate(){
  std::vector< bool > active;
  active.resize( d_matches.size(), true );
  for( int k=0; k<(int)d_matches.size(); k++ ){
    for( int l=(k+1); l<(int)d_matches.size(); l++ ){
      if( k!=l && active[k] && active[l] ){
        if( d_matches[k].isEqual( d_matches[l] ) ){
          active[l] = false;
        }
      }
    }
  }
  std::vector< InstMatch > temp;
  temp.insert( temp.begin(), d_matches.begin(), d_matches.end() );
  d_matches.clear();
  for( int i=0; i<(int)temp.size(); i++ ){
    if( active[i] ){
      d_matches.push_back( temp[i] );
    }
  }
}

void InstMatchGroup::debugPrint( const char* c ){
  for( int j=0; j<(int)d_matches.size(); j++ ){
    Debug( c ) << "Match " << j << " : " << std::endl;
    d_matches[j].debugPrint( c );
  }
}




uf::InstantiatorTheoryUf* InstMatchGenerator::d_itu = NULL;
std::map< Node, std::map< Node, std::vector< InstMatchGenerator* > > > InstMatchGenerator::d_iter[4];
std::map< Node, std::map< Node, int > > InstMatchGenerator::d_assigned[4];
int InstMatchGenerator::d_splitThreshold;
bool InstMatchGenerator::d_useSplitThreshold = false;
uint64_t InstMatchGenerator::d_instLevelThreshold;
bool InstMatchGenerator::d_useInstLevelThreshold = false;

void InstMatchGenerator::resetAssigned(){
  for( int i=0; i<4; i++ ){
    d_assigned[i].clear();
  }
}

void InstMatchGenerator::clearMatches(){
  d_mg_i = -1;
  if( getMaster()==this ){
    if( !d_children.empty() || d_mg.empty() ){
      d_mg_set = false;
      d_partial.clear();
      d_mg.clear();
      d_index = 0;
      for( int i=0; i<(int)d_children.size(); i++ ){
        d_children[i]->clearMatches();
      }
    }
  }else{
    getMaster()->clearMatches();
  }
}

void InstMatchGenerator::clear(){
  d_children_set = false;
  d_children.clear();
  d_depth = 0;
  d_mg_i = -1;
  d_mg_set = false;
  d_partial.clear();
  d_mg.clear();
  d_index = 0;
}

InstMatchGenerator::InstMatchGenerator( Node t, Node s, int op ) :
d_children_set( false ), d_mg_set( false ), d_t( t ), d_s( s ), d_operation( op ), d_index( 0 ), d_depth( 0 ), d_mg_i( -1 ){

}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( Node t, Node s, int op ){
  int index = d_assigned[op][t][s];
  Debug( "quant-uf-uiter" ) << "mkInstMatchGenerator " << t << " " << s << " " << op;
  Debug( "quant-uf-uiter" )<< " (" << index << "/" << d_iter[op][t][s].size() << ")" << std::endl;
  if( index<(int)d_iter[op][t][s].size() ){
    d_iter[op][t][s][ index ]->clear();
    d_assigned[op][t][s]++;
    return d_iter[op][t][s][ index ];
  }else{
    InstMatchGenerator* mi = new InstMatchGenerator( t, s, op );
    d_iter[op][t][s].push_back( mi );
    d_assigned[op][t][s]++;
    return mi;
  }
}

InstMatchGenerator* InstMatchGenerator::mkInstMatchGenerator( bool isComb ){
  Node nl;
  int op = isComb ? 0 : 2;
  return mkInstMatchGenerator( nl, nl, op );
}

InstMatchGenerator* InstMatchGenerator::mkCombineInstMatchGenerator( Node t, Node s, bool isEq ){
  int op = isEq ? 0 : 1;
  return mkInstMatchGenerator( t, s, op );
}

InstMatchGenerator* InstMatchGenerator::mkMergeInstMatchGenerator( Node t, Node s ){
  return mkInstMatchGenerator( t, s, 2 );
}

InstMatchGenerator* InstMatchGenerator::mkAnyMatchInstMatchGenerator( Node t ){
  Assert( t.getKind()==APPLY_UF );
  Node nl;
  return mkInstMatchGenerator( t, nl, 3 );
}

bool InstMatchGenerator::areEqual( Node a, Node b ) { return d_itu->areEqual( a, b ); }
bool InstMatchGenerator::areDisequal( Node a, Node b ) { return d_itu->areDisequal( a, b ); }
Node InstMatchGenerator::getRepresentative( Node a ) { return d_itu->getRepresentative( a ); }

bool InstMatchGenerator::getNextMatch(){
  Debug( "quant-uf-uiter" ) << "get next match " << this << std::endl;
  d_mg_i++;
  InstMatchGenerator* master = getMaster();
  if( d_mg_i<(int)master->d_mg.d_matches.size() ){
    Debug( "quant-uf-uiter" ) << this << " returned (existing) match " << d_mg_i << std::endl;
    getCurrent()->debugPrint( "quant-uf-uiter" );
    return true;
  }else if( d_mg_i==(int)master->d_mg.d_matches.size() ){
    if( master->d_mg_set ){
      Debug( "quant-uf-uiter" )  << this << " already set" << std::endl;
      return false;
    }else{
      if( !master->d_children_set ){
        Debug( "quant-uf-uiter" ) << this << " calculate children" << std::endl;
        master->calcChildren();
        Debug( "quant-uf-uiter" ) << "This is my iterator: " << std::endl;
        debugPrint( "quant-uf-uiter", 0 );
        Debug( "quant-uf-uiter" ) << std::endl;
      }
      if( master->d_mg_set ){
        return ( d_mg_i<(int)master->d_mg.d_matches.size() );
      }else if( master->calcNextMatch() ){
        Assert( d_mg_i<(int)master->d_mg.d_matches.size() );
        Debug( "quant-uf-uiter" ) << this << " returned match " << d_mg_i << std::endl;
        getCurrent()->debugPrint( "quant-uf-uiter" );
        return true;
      }else{
        Debug( "quant-uf-uiter" ) << this << " did not calc new match" << std::endl;
        master->d_mg_set = true;
        return false;
      }
    }
  }else{
    Debug( "quant-uf-uiter" ) << this << " no more matches." << std::endl;
    return false;
  }
}

bool InstMatchGenerator::addInstMatch( InstMatch& m ){
#if 1
  for( int i=0; i<(int)d_mg.d_matches.size(); i++ ){
    if( d_mg.d_matches[i].checkSubsume( m )==-1 ){
      return false;
    }
  }
  d_mg.d_matches.push_back( m );
  return true;
#else
  if( d_mg.contains( m ) ){
    return false;
  }else{
    d_mg.d_matches.push_back( m );
    return true;
  }
#endif
}

void InstMatchGenerator::indent( const char* c, int ind ){
  for( int i=0; i<(int)ind; i++ ){
    Debug( c ) << " ";
  }
}

struct sortInstantiationLevel {
  bool operator() (InstMatchGenerator* i,InstMatchGenerator* j) { return (i->getInstantiationLevel()<j->getInstantiationLevel());}
} sortInstantiationLevelObj;


void InstMatchGenerator::debugPrint( const char* c, int ind, bool printChildren ){
  indent( c, ind );
  if( getMaster()==this ){
    Debug( c ) << ( ( getMaster()->d_mg_set || getMaster()->d_children_set ) ? "+" : "-" );
  }else{
    Debug( c ) << "<";
  }
  Debug( c ) << " " << this << " " << d_depth << " " << ( isCombine() ? "Combine" : "Merge" );
  if( d_t!=Node::null() ){
    Debug( c ) << " " << d_t << ( d_operation==1 ? " != " : " = " ) << d_s;
  }
  Debug( c ) << " (" << ( getMaster()->d_mg_set ? "***" : "" ) << "matches=" << getMaster()->d_mg.d_matches.size() << ")";
  //Debug( c ) << ", children = " << d_children.size() << std::endl;
  Debug( c ) << std::endl;
  if( getMaster()==this && printChildren ){
    for( int i=0; i<(int)d_children.size(); i++ ){
      d_children[i]->debugPrint( c, ind+1 );
    }
  }
}

void InstMatchGenerator::calcChildren(){
  if( d_t!=Node::null() ){
    Node f = d_t.getAttribute(InstConstantAttribute());
    if( d_operation==0 ){
      if( d_t.getKind()==INST_CONSTANT && d_s.getAttribute(InstConstantAttribute())!=f ){
        InstMatch m( f, d_itu->d_instEngine );
        Node c = getRepresentative( d_s );
        if( !areEqual( d_t, c ) ){
          m.setMatch( d_t, c );
        }
        d_mg.d_matches.push_back( m );
        d_mg_set = true;
      }else{
        ////find any term to match d_t to d_s
        ////if they share the same operator, try a merge, if legal to do so
        //if( d_t.getKind()==APPLY_UF && d_s.getKind()==APPLY_UF && d_t.getOperator()==d_s.getOperator() ){
        //  InstMatchGenerator* ui = mkMergeInstMatchGenerator( d_t, d_s, f );
        //  if( ui ){
        //    d_children.push_back( ui );
        //  }
        //}
        d_itu->calculateEIndLitCandidates( d_t, d_s, f, true );
        //Assert( d_t.getKind()!=APPLY_UF || d_s.getKind()!=APPLY_UF || d_t.getOperator()!=d_s.getOperator() );
        for( int i=0; i<(int)d_itu->d_litMatchCandidates[0][d_t][d_s].size(); i++ ){
          Node m = d_itu->d_litMatchCandidates[0][d_t][d_s][i];
          if( d_s.getAttribute(InstConstantAttribute())==f ){
            //equality between two triggers
            InstMatchGenerator* mi = mkInstMatchGenerator( false );
            mi->d_children.push_back( mkCombineInstMatchGenerator( d_t, m, true ) );
            mi->d_children.push_back( mkCombineInstMatchGenerator( d_s, m, true ) );
            d_children.push_back( mi );
          }else{
            //equality between trigger and ground term
            d_children.push_back( mkMergeInstMatchGenerator( d_t, m ) );
          }
        }
      }
    }else if( d_operation==1 ){
      //find any term to match d_t to d_s
      d_itu->calculateEIndLitCandidates( d_t, d_s, f, false );
      Debug( "quant-uf-uiter" ) << "Find candidates for " << d_t << ( d_operation==0 ? " = " : " != " ) << d_s << std::endl;
      Debug( "quant-uf-uiter" ) << "# of match candidates = " << d_itu->d_litMatchCandidates[d_operation][d_t][d_s].size() << std::endl;
      //if( d_itu->d_litMatchCandidates[d_operation][d_t][d_s].size()==1 && !d_s.hasAttribute(InstConstantAttribute()) ){
      //  //if one child, compress the child to this
      //  // must consider if the following InstMatchGenerator already exists
      //  int nOp = d_operation==1 ? 0 : 2;
      //  Node s = d_itu->d_litMatchCandidates[d_operation][d_t][d_s][0];
      //  if( d_assigned[nOp][d_t][s]==0 ){
      //    if( d_operation==1 ){
      //      mkCombineInstMatchGenerator( d_t, s, true, f );
      //    }else{
      //      mkMergeInstMatchGenerator( d_t, s, f );
      //    }
      //  }
      //  d_miter[d_operation][d_t][d_s] = d_miter[nOp][d_t][s];
      //  d_mg_i = -1;
      //  getMaster()->calcChildren();
      //  return;
      //}
      if( d_s.getAttribute(InstConstantAttribute())==f ){
        //disequality between two triggers
        for( int i=0; i<(int)d_itu->d_litMatchCandidates[1][d_t][d_s].size(); i++ ){
          Node mt = d_itu->d_litMatchCandidates[1][d_t][d_s][i][0];
          Node ms = d_itu->d_litMatchCandidates[1][d_t][d_s][i][1];
          InstMatchGenerator* mi = mkInstMatchGenerator( false );
          mi->d_children.push_back( mkCombineInstMatchGenerator( d_t, mt, true ) );
          mi->d_children.push_back( mkCombineInstMatchGenerator( d_s, ms, true ) );
          d_children.push_back( mi );
        }
      }else{
        //disequality between trigger and ground term
        for( int i=0; i<(int)d_itu->d_litMatchCandidates[1][d_t][d_s].size(); i++ ){
          Node m = d_itu->d_litMatchCandidates[1][d_t][d_s][i];
          d_children.push_back( mkCombineInstMatchGenerator( d_t, m, true ) );
        }
      }
    }else if( d_operation==2 ){
      if( d_t.getKind()==INST_CONSTANT ){
        InstMatch m( f, d_itu->d_instEngine );
        Node c = getRepresentative( d_s );
        if( !areEqual( d_t, c ) ){
          m.setMatch( d_t, c );
        }
        d_mg.d_matches.push_back( m );
        d_mg_set = true;
      }else{
        //merge the arguments of d_t and d_s 
        Assert( d_t.getKind()==APPLY_UF );
        Assert( d_s.getKind()==APPLY_UF );
        Assert( d_t.getOperator()==d_s.getOperator() );
        Assert( d_t.getNumChildren()==d_s.getNumChildren() );
        Node f = d_t.getAttribute(InstConstantAttribute());
        for( int j=0; j<(int)d_s.getNumChildren(); j++ ){
          if( !areEqual( d_t[j], d_s[j] ) ){
            if( d_t[j].hasAttribute(InstConstantAttribute()) ){
              d_children.push_back( mkCombineInstMatchGenerator( d_t[j], getRepresentative( d_s[j] ), true ) );
            }else{
              Assert( d_s[j].getAttribute(InstConstantAttribute())!=f );
              addSplit( d_t[j], d_s[j] );
            }
          }else if( areDisequal( d_t[j], d_s[j] ) ){
            d_children.clear();
            break;
          }
        }
      }
    }else if( d_operation==3 ){
      d_itu->calculateMatches( f, d_t );
      for( int i=0; i<(int)d_itu->d_matches[d_t].size(); i++ ){
        d_children.push_back( mkMergeInstMatchGenerator( d_t, d_itu->d_matches[d_t][i] ) );
      }
    }
  }
  if( isCombine() ){
    //sort children based on instantiation level
    std::sort( d_children.begin(), d_children.end(), sortInstantiationLevelObj );
  }
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i]->d_depth = d_depth + 1;
  }
  d_children_set = true;
}

void InstMatchGenerator::addSplit( Node n1, Node n2 ){
  if( n2<n1 ){
    Node ntemp = n1;
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

bool InstMatchGenerator::acceptMatch( InstMatch* m ){
  if( d_useInstLevelThreshold ){
    for( std::map< Node, Node >::iterator it = m->d_map.begin(); 
        it != m->d_map.end(); ++it ){
      if( it->second!=Node::null() && it->second.hasAttribute(InstLevelAttribute()) &&
          it->second.getAttribute(InstLevelAttribute())>d_instLevelThreshold ){
        return false;
      }
    }
  }
  if( d_useSplitThreshold ){
    if( (int)m->d_splits.size()<=d_splitThreshold ){
      for( std::map< Node, Node >::iterator it = m->d_splits.begin();
            it != m->d_splits.end(); ++it ){
        if( areDisequal( it->first, it->second ) ){
          return false;
        }
      }
    }else{
      return false;
    }
  }
  return true;
}

int InstMatchGenerator::getInstantiationLevel(){
  if( getMaster()==this ){
    if( d_s!=Node::null() ){
      return d_s.getAttribute(InstLevelAttribute());
    }else{
      int maxLevel = 0;
      for( int i=0; i<(int)d_children.size(); i++ ){
        int level = d_children[i]->getInstantiationLevel();
        if( level>maxLevel ){
          maxLevel = level;
        }
      }
      return maxLevel;
    }
  }else{
    return getMaster()->getInstantiationLevel();
  }
}

bool InstMatchGenerator::calcNextMatch(){
  Assert( getMaster()==this );
  Assert( !d_mg_set );
  if( d_children.empty() ){
    Debug( "quant-uf-uiter" ) << "calcNextMatch:: Children empty " << d_children.size() << std::endl;
    if( !isCombine() && d_t!=Node::null() ){
      //by definition, this should produce the empty match
      Node f = d_t.getAttribute(InstConstantAttribute());
      d_mg.d_matches.push_back( InstMatch( f, d_itu->d_instEngine ) );
      d_mg_set = true;
      return true;
    }else{
      return false;
    }
  }else{
    Debug( "quant-uf-uiter" ) << "calc next match " << this << std::endl;
    if( isCombine() ){
      //get the next match
      bool success;
      do{
        success = d_children[d_index]->getNextMatch();
        if( !success ){
          d_index++;
          if( d_index==(int)d_children.size() ){
            return false;
          }
        }
      }while( !success );
      Assert( d_children[d_index]->getCurrent()!=NULL );
      if( addInstMatch( *d_children[d_index]->getCurrent() ) ){  //if we have not seen this match before
        return true;
      }else{
        return calcNextMatch();
      }
    }else{
      //if this is the first time
      if( d_mg.empty() ){
        if( d_useSplitThreshold && (int)d_splits.size()>d_splitThreshold ){
          d_mg_set = true;
          return false;
        }else{
          for( int i=0; i<(int)d_children.size(); i++ ){
            //do quick check to see if any are empty
            if( !d_children[i]->getNextMatch() ){
              d_mg_set = true;
              return false;
            }else{
              d_children[i]->reset();
            }
          }
        }
      }

      if( !d_partial.empty() ){
        d_partial.pop_back();
      }
      // i is the index of the child we are trying to fit into our merged match
      int i = (int)d_partial.size();
      //until we have created a merge for all children
      while( i!=(int)d_children.size() ){
        InstMatch combined;
        bool success = false;
        //get the next match
        while( !success && d_children[i]->getNextMatch() ){
          combined = InstMatch( *d_children[i]->getCurrent() );
          //ensure that splits are consistent 
          //see if it merges into the current built merge (stored in d_partial)
          if( i==0 ){
            for( std::map< Node, Node >::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
              combined.addSplit( it->first, it->second );
            }
          }else{
            combined.merge( d_partial[i-1], true );
          }
          success = acceptMatch( &combined );
        }
        Assert( !d_children[i]->empty() );
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
      if( addInstMatch( d_partial[ d_children.size() - 1 ] ) ){ //if we have not seen this match before
        return true;
      }else{
        return calcNextMatch();
      }
    }
  }
}

double InstMatchGenerator::collectUnmerged( std::map< InstMatchGenerator*, InstMatchGenerator* >& index, std::vector< InstMatchGenerator* >& unmerged,
                                   std::vector< InstMatchGenerator* >& cover ){
  Assert( getMaster()->d_children_set );
  Assert( getMaster()->d_mg.d_matches.empty() && getMaster()->d_mg_set );
  if( getMaster()->d_children.empty() ){
    unmerged.push_back( this );
    return 0.0;
  }else{
    if( getMaster()->isCombine() ){
      double maxScore = -1.0;
      int maxIndex = -1;
      //take maximum index child
      std::vector< InstMatchGenerator* > unmg;
      std::vector< InstMatchGenerator* > cvr;
      for( int i=0; i<(int)getMaster()->d_children.size(); i++ ){
        std::vector< InstMatchGenerator* > unmg_temp;
        std::vector< InstMatchGenerator* > cvr_temp;
        double cScore = getMaster()->d_children[ i ]->collectUnmerged( index, unmg_temp, cvr_temp );
        if( cScore>maxScore ){
          maxScore = cScore;
          maxIndex = i;
          unmg.clear();
          unmg.insert( unmg.end(), unmg_temp.begin(), unmg_temp.end() );
          cvr.clear();
          cvr.insert( cvr.end(), cvr_temp.begin(), cvr_temp.end() );
        }
      }
      index[ this ] = getMaster()->d_children[ maxIndex ];
      unmerged.insert( unmerged.end(), unmg.begin(), unmg.end() );
      cover.insert( cover.end(), cvr.begin(), cvr.end() );
      return maxScore;
    }else{
      bool emptyChild = false;
      double score = 0.0;
      for( int i=0; i<(int)getMaster()->d_children.size(); i++ ){
        if( !getMaster()->d_children[i]->getMaster()->d_mg_set && 
            getMaster()->d_children[i]->getMaster()->d_mg.d_matches.empty() ){
          getMaster()->d_children[i]->getNextMatch();
        }
        if( getMaster()->d_children[i]->empty() ){
          score += .5*getMaster()->d_children[i]->collectUnmerged( index, unmerged, cover );
          emptyChild = true;
        }else{
          Assert( !getMaster()->d_children[i]->getMaster()->d_mg.d_matches.empty() );
          cover.push_back( getMaster()->d_children[i] );
          score += 1.0;
        }
      }
      if( !emptyChild ){
        unmerged.push_back( this );
      }
      score = score/(double)(getMaster()->d_children.size());
      return score;
    }
  }
}

void InstMatchGenerator::collectUnmerged( std::vector< InstMatchGenerator* >& unmerged, std::vector< InstMatchGenerator* >& cover ){
  if( !getMaster()->d_mg.d_matches.empty() ){
    return;
  }
  Assert( getMaster()->d_children_set );
  Assert( getMaster()->d_mg_set );
  if( getMaster()->d_children.empty() ){
    unmerged.push_back( this );
  }else{
    if( getMaster()->isCombine() ){
      //take maximum index child
      for( int i=0; i<(int)getMaster()->d_children.size(); i++ ){
        getMaster()->d_children[ i ]->collectUnmerged( unmerged, cover );
      }
    }else{
      bool emptyChild = false;
      for( int i=0; i<(int)getMaster()->d_children.size(); i++ ){
        if( !getMaster()->d_children[i]->getMaster()->d_mg_set && 
            getMaster()->d_children[i]->getMaster()->d_mg.d_matches.empty() ){
          getMaster()->d_children[i]->getNextMatch();
        }
        if( getMaster()->d_children[i]->empty() ){
          getMaster()->d_children[i]->collectUnmerged( unmerged, cover );
        }else{
          Assert( !getMaster()->d_children[i]->getMaster()->d_mg.d_matches.empty() );
          cover.push_back( getMaster()->d_children[i] );
        }
      }
      if( !emptyChild ){
        unmerged.push_back( this );
      }
    }
  }
}

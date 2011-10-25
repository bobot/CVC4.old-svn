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

InstantiatorTheoryUf* UIterator::d_itu = NULL;
std::map< Node, std::map< Node, std::vector< UIterator* > > > UIterator::d_iter[3];
std::map< Node, std::map< Node, int > > UIterator::d_assigned[3];
int UIterator::d_splitThreshold;

void UIterator::resetAssigned(){
  for( int i=0; i<3; i++ ){
    d_assigned[i].clear();
  }
}

void UIterator::clearMatches(){
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

void UIterator::clear(){
  d_children_set = false;
  d_children.clear();
  d_depth = 0;
  d_mg_i = -1;
  d_mg_set = false;
  d_partial.clear();
  d_mg.clear();
  d_index = 0;
}

UIterator::UIterator( int op ) : 
d_children_set( false ), d_mg_set( false ), d_operation( op ), d_index( 0 ), d_depth( 0 ), d_mg_i( -1 ){

}

UIterator::UIterator( Node t, Node s, int op, Node f ) :
d_children_set( false ), d_mg_set( false ), d_t( t ), d_s( s ), d_operation( op ), d_index( 0 ), d_depth( 0 ), d_mg_i( -1 ){
  Assert( t.getType()==s.getType() );
  Assert( t.getAttribute(InstConstantAttribute())==f );
}

UIterator* UIterator::mkUIterator( bool isComb ){
  Node nl;
  int ind = isComb ? 0 : 2;
  int index = d_assigned[ind][nl][nl];
  Debug( "quant-uf-uiter" ) << "mkUIterator " << isComb;
  Debug( "quant-uf-uiter" )<< " (" << index << "/" << d_iter[ind][nl][nl].size() << ")" << std::endl;
  if( index<(int)d_iter[ind][nl][nl].size() ){
    d_iter[ind][nl][nl][ index ]->clear();
    d_assigned[ind][nl][nl]++;
    return d_iter[ind][nl][nl][ index ];
  }else{
    UIterator* i = new UIterator( ind );
    d_iter[ind][nl][nl].push_back( i );
    d_assigned[ind][nl][nl]++;
    return i;
  }
}

UIterator* UIterator::mkCombineUIterator( Node t, Node s, bool isEq, Node f ){
  //if( isEq && !s.hasAttribute(InstConstantAttribute()) ){
  //  d_itu->calculateEIndLitCandidates( t, s, f, isEq );
  //  if( d_itu->d_litMatchCandidates[0][t][s].size()==1 ){
  //    return mkMergeUIterator( t, d_itu->d_litMatchCandidates[0][t][s][0], f );
  //  }
  //}
  int ind = isEq ? 0 : 1;
  int index = d_assigned[ind][t][s];
  Debug( "quant-uf-uiter" ) << "mkCombineIterator " << t << " " << s << " " << isEq;
  Debug( "quant-uf-uiter" )<< " (" << index << "/" << d_iter[ind][t][s].size() << ")" << std::endl;
  if( index<(int)d_iter[ind][t][s].size() ){
    d_iter[ind][t][s][ index ]->clear();
    d_assigned[ind][t][s]++;
    return d_iter[ind][t][s][ index ];
  }else{
    UIterator* ci = new UIterator( t, s, ind, f );
    d_iter[ind][t][s].push_back( ci );
    d_assigned[ind][t][s]++;
    return ci;
  }
}

UIterator* UIterator::mkMergeUIterator( Node t, Node s, Node f ){
  int index = d_assigned[2][t][s];
  Debug( "quant-uf-uiter" ) << "mkMergeIterator " << t << " " << s;
  Debug( "quant-uf-uiter" )<< " (" << index << "/" << d_iter[2][t][s].size() << ")" << std::endl;
  if( index<(int)d_iter[2][t][s].size() ){
    d_iter[2][t][s][ index ]->clear();
    d_assigned[2][t][s]++;
    return d_iter[2][t][s][ index ];
  }else{
    UIterator* mi = new UIterator( t, s, 2, f );
    d_iter[2][t][s].push_back( mi );
    d_assigned[2][t][s]++;
    return mi;
  }
}

bool UIterator::areEqual( Node a, Node b ) { return d_itu->areEqual( a, b ); }
bool UIterator::areDisequal( Node a, Node b ) { return d_itu->areDisequal( a, b ); }
Node UIterator::getRepresentative( Node a ) { return d_itu->getRepresentative( a ); }

bool UIterator::getNextMatch(){
  Debug( "quant-uf-uiter" ) << "get next match " << this << std::endl;
  d_mg_i++;
  UIterator* master = getMaster();
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

bool UIterator::addInstMatch( InstMatch& m ){
  if( d_mg.contains( m ) ){
    return false;
  }else{
    d_mg.d_matches.push_back( m );
    return true;
  }
}

void UIterator::indent( const char* c, int ind ){
  for( int i=0; i<(int)ind; i++ ){
    Debug( c ) << " ";
  }
}

void UIterator::debugPrint( const char* c, int ind, bool printChildren ){
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

void UIterator::calcChildren(){
  if( d_t!=Node::null() ){
    Node f = d_t.getAttribute(InstConstantAttribute());
    if( isCombine() ){
      if( d_t.getKind()==INST_CONSTANT && !d_s.hasAttribute(InstConstantAttribute()) ){
        InstMatch m( f, d_itu->d_instEngine );
        Node c = getRepresentative( d_s );
        if( !areEqual( d_t, c ) ){
          m.setMatch( d_t, c );
        }
        d_mg.d_matches.push_back( m );
        d_mg_set = true;
      }else{
        //find any term to match d_t to d_s
        d_itu->calculateEIndLitCandidates( d_t, d_s, f, d_operation==0 );
        Debug( "quant-uf-uiter" ) << "Find candidates for " << d_t << ( d_operation==0 ? " = " : " != " ) << d_s << std::endl;
        Debug( "quant-uf-uiter" ) << "# of match candidates = " << d_itu->d_litMatchCandidates[d_operation][d_t][d_s].size() << std::endl;
        //if( d_itu->d_litMatchCandidates[d_operation][d_t][d_s].size()==1 && !d_s.hasAttribute(InstConstantAttribute()) ){
        //  //if one child, compress the child to this
        //  // must consider if the following UIterator already exists
        //  int nOp = d_operation==1 ? 0 : 2;
        //  Node s = d_itu->d_litMatchCandidates[d_operation][d_t][d_s][0];
        //  if( d_assigned[nOp][d_t][s]==0 ){
        //    if( d_operation==1 ){
        //      mkCombineUIterator( d_t, s, true, f );
        //    }else{
        //      mkMergeUIterator( d_t, s, f );
        //    }
        //  }
        //  d_miter[d_operation][d_t][d_s] = d_miter[nOp][d_t][s];
        //  d_mg_i = -1;
        //  getMaster()->calcChildren();
        //  return;
        //}
        if( d_operation==1 ){
          if( d_s.getAttribute(InstConstantAttribute())==f ){
            //disequality between two triggers
            for( int i=0; i<(int)d_itu->d_litMatchCandidates[1][d_t][d_s].size(); i++ ){
              Node mt = d_itu->d_litMatchCandidates[1][d_t][d_s][i][0];
              Node ms = d_itu->d_litMatchCandidates[1][d_t][d_s][i][1];
              UIterator* mi = mkUIterator( false );
              mi->d_children.push_back( mkCombineUIterator( d_t, mt, true, f ) );
              mi->d_children.push_back( mkCombineUIterator( d_s, ms, true, f ) );
              d_children.push_back( mi );
            }
          }else{
            //disequality between trigger and ground term
            for( int i=0; i<(int)d_itu->d_litMatchCandidates[1][d_t][d_s].size(); i++ ){
              Node m = d_itu->d_litMatchCandidates[1][d_t][d_s][i];
              d_children.push_back( mkCombineUIterator( d_t, m, true, f ) );
            }
          }
        }else{
          //Assert( d_t.getKind()!=APPLY_UF || d_s.getKind()!=APPLY_UF || d_t.getOperator()!=d_s.getOperator() );
          for( int i=0; i<(int)d_itu->d_litMatchCandidates[0][d_t][d_s].size(); i++ ){
            Node m = d_itu->d_litMatchCandidates[0][d_t][d_s][i];
            if( d_s.getAttribute(InstConstantAttribute())==f ){
              //equality between two triggers
              UIterator* mi = mkUIterator( false );
              mi->d_children.push_back( mkCombineUIterator( d_t, m, true, f ) );
              mi->d_children.push_back( mkCombineUIterator( d_s, m, true, f ) );
              d_children.push_back( mi );
            }else{
              //equality between trigger and ground term
              d_children.push_back( mkMergeUIterator( d_t, m, f ) );
            }
          }
        }
      }
    }else{
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
          Assert( !areDisequal( d_t[j], d_s[j] ) );
          if( !areEqual( d_t[j], d_s[j] ) ){
            if( d_t[j].hasAttribute(InstConstantAttribute()) ){
              d_children.push_back( mkCombineUIterator( d_t[j], getRepresentative( d_s[j] ), true, f ) );
            }else{
              addSplit( d_t[j], d_s[j] );
            }
          }
        }
      }
    }
  }
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i]->d_depth = d_depth + 1;
  }
  d_children_set = true;
}

void UIterator::addSplit( Node n1, Node n2 ){
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

bool UIterator::calcNextMatch(){
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
        if( (int)d_splits.size()>d_splitThreshold ){
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
          if( (int)combined.d_splits.size()<=d_splitThreshold ){
            bool consistentSplit = true;
            for( std::map< Node, Node >::iterator it = combined.d_splits.begin();
                  it != combined.d_splits.end(); ++it ){
              if( areDisequal( it->first, it->second ) ){
                consistentSplit = false;
                break;
              }
            }
            success = consistentSplit;
          }
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

double UIterator::collectUnmerged( std::map< UIterator*, UIterator* >& index, std::vector< UIterator* >& unmerged,
                                   std::vector< UIterator* >& cover ){
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
      std::vector< UIterator* > unmg;
      std::vector< UIterator* > cvr;
      for( int i=0; i<(int)getMaster()->d_children.size(); i++ ){
        std::vector< UIterator* > unmg_temp;
        std::vector< UIterator* > cvr_temp;
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

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie, th ),
//d_subterms( c ),
//d_subterm_size( c ),
d_obligations( c ),
d_ob_pol( c ),
d_terms_full( c ),
d_terms( c ),
d_disequality( c )
{
  registerTerm( ((TheoryUF*)d_th)->d_true );
  registerTerm( ((TheoryUF*)d_th)->d_false );
  Node eq = NodeManager::currentNM()->mkNode( IFF, ((TheoryUF*)d_th)->d_true, ((TheoryUF*)d_th)->d_false );
  d_disequality.push_back( eq );
}

void InstantiatorTheoryUf::check( Node assertion )
{
  Debug("quant-uf-assert") << "InstantiatorTheoryUf::check: " << assertion << std::endl;
  switch (assertion.getKind()) {
  case kind::EQUAL:
    assertEqual( assertion[0], assertion[1] );
    break;
  case kind::APPLY_UF:
    assertEqual( assertion, ((TheoryUF*)d_th)->d_true );
    break;
  case kind::NOT:
    assertEqual( assertion[0], ((TheoryUF*)d_th)->d_false );
    break;
  default:
    Unreachable();
  }
}

void InstantiatorTheoryUf::assertEqual( Node a, Node b )
{
  if( a.hasAttribute(InstConstantAttribute()) || 
      b.hasAttribute(InstConstantAttribute()) ){
    //add to obligation list
    Node formula;
    Node f;
    bool isEq = true;
    if( a.hasAttribute(InstConstantAttribute()) ){
      f = a.getAttribute(InstConstantAttribute());
      Kind knd = a.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
      formula = NodeManager::currentNM()->mkNode( knd, a, b );
    }else if( b.hasAttribute(InstConstantAttribute()) ){
      f = b.getAttribute(InstConstantAttribute());
      //swap sides
      Kind knd = a.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
      formula = NodeManager::currentNM()->mkNode( knd, b, a );
    }
    //swap sides for a disequality
    if( a.getKind()==EQUAL || a.getKind()==IFF ){
      if( !a[0].hasAttribute(InstConstantAttribute()) ){
        Assert( a[1].hasAttribute(InstConstantAttribute()) );
        a = NodeManager::currentNM()->mkNode( a.getKind(), a[1], a[0] );
        InstConstantAttribute icai;
        a.setAttribute(icai,f);
      }
      isEq = false;
      formula = a;
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
    d_ob_pol[ formula ] = isEq;
    //this theory has constraints from f
    setHasConstraintsFrom( f );
  }
  if( a.getKind()==EQUAL || a.getKind()==IFF ){
    Assert( b==((TheoryUF*)d_th)->d_false );
    d_disequality.push_back( a );
    registerTerm( a[0] );
    registerTerm( a[1] );
  }else{
    Assert( b.getKind()!=EQUAL && b.getKind()!=IFF );
    registerTerm( a );
    registerTerm( b );
  }
}

void InstantiatorTheoryUf::registerTerm( Node n, bool isTop )
{
  bool recurse = false;
  if( isTop ){
    if( d_terms.find( n )==d_terms.end() ){
      d_terms[n] = true;
      d_terms_full[n] = true;
      recurse = true;
    }
  }else{
    if( d_terms_full.find( n )==d_terms_full.end() ){
      d_terms_full[n] = true;
      recurse = true;
    }
  }
  if( recurse ){
    if( n.getKind()==INST_CONSTANT ){
      d_instEngine->d_ic_active[n] = true;
    }
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerTerm( n[i], false );
    }
  }
}

//void InstantiatorTheoryUf::buildSubTerms( Node n )
//{
//  SubTermMap::iterator it = d_subterms.find( n );
//  if( it==d_subterms.end() ){
//    SubTermNode* g = getSubTerm( n );
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      if( n[i].hasAttribute(InstConstantAttribute()) ){
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
//  Assert( n.hasAttribute(InstConstantAttribute()) );
//  if( n.getKind()==INST_CONSTANT ){
//    d_active_ic[ n ] = true;
//  }else{
//    if( d_inst_terms.find( n )==d_inst_terms.end() ){
//      for( int i=0; i<(int)n.getNumChildren(); i++ ){
//        if( n[i].hasAttribute(InstConstantAttribute()) ){
//          setActiveInstConstants( n[i] );
//        }
//      }
//    }
//  }
//}

void InstantiatorTheoryUf::resetInstantiation()
{
  UIterator::d_itu = this;
  UIterator::resetAssigned();
  d_status = STATUS_UNFINISHED; 
  d_baseMatch.clear();
  d_matches.clear();
  d_anyMatches.clear();
  d_eq_dep.clear();
  d_litMatchCandidates[0].clear();
  d_litMatchCandidates[1].clear();
  //build equivalence classes
  d_emap.clear();
  for( BoolMap::iterator it = d_terms.begin(); it!=d_terms.end(); ++it ){
    Node n = (*it).first;
    if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) ){
      Node r = ((TheoryUF*)d_th)->d_equalityEngine.getRepresentative( n );
      Assert( std::find( d_emap[r].begin(), d_emap[r].end(), n )==d_emap[r].end() );
      d_emap[r].push_back( n );
    }
  }
  //set representatives
  std::map< Node, Node > repReplace;
  for( std::map< Node, std::vector< Node > >::iterator it = d_emap.begin(); it!=d_emap.end(); ++it ){
    Node r = it->first;
    if( r.hasAttribute(InstConstantAttribute()) ){
      //see if there is concrete ground term, make that representative
      for( int i=0; i<(int)it->second.size(); i++ ){
        if( !it->second[i].hasAttribute(InstConstantAttribute()) ){
          repReplace[ r ] = it->second[i];
        }
      }
    }
  }
  for( std::map< Node, Node >::iterator it = repReplace.begin(); it!=repReplace.end(); ++it ){
    Assert( d_emap[ it->second ].empty() );
    d_emap[ it->second ].clear();
    d_emap[ it->second ].insert( d_emap[ it->second ].begin(), d_emap[ it->first ].begin(), d_emap[ it->first ].end() );
    d_emap.erase( it->first );
  }
  d_reps.clear();
  for( std::map< Node, std::vector< Node > >::iterator it = d_emap.begin(); it!=d_emap.end(); ++it ){
    for( int i=0; i<(int)it->second.size(); i++ ){
      d_reps[ it->second[i] ] = it->first;
    }
  }
  //build disequality lists
  d_dmap.clear();
  for( NodeList::const_iterator it = d_disequality.begin(); it!=d_disequality.end(); ++it ){
    Node n = (*it);
    Node r1 = getRepresentative( n[0] );
    //must be added to emap
    if( d_emap.find( r1 )==d_emap.end() ){
      Assert( r1==n[0] );
      d_emap[ r1 ].push_back( r1 );
    }
    Node r2 = getRepresentative( n[1] );
    //must be added to emap
    if( d_emap.find( r2 )==d_emap.end() ){
      Assert( r2==n[1] );
      d_emap[ r2 ].push_back( r2 );
    }
    if( std::find( d_dmap[r1].begin(), d_dmap[r1].end(), r2 )==d_dmap[r1].end() ){
      d_dmap[r1].push_back( r2 );
    }
    if( std::find( d_dmap[r2].begin(), d_dmap[r2].end(), r1 )==d_dmap[r2].end() ){
      d_dmap[r2].push_back( r1 );
    }
  }
  //debug print
  debugPrint("quant-uf-debug");
}

void InstantiatorTheoryUf::debugPrint( const char* c )
{
  //Debug( c ) << "Terms:" << std::endl;
  //for( BoolMap::const_iterator it = d_terms.begin(); it!=d_terms.end(); ++it ){
  //  Debug( c ) << "   " << (*it).first;
  //  //Debug( c ) << "  ->  " << getRepresentative( (*it).first );
  //  Debug( c ) << std::endl;
  //}
  Debug( c ) << "Equivalence classes:" << std::endl;
  int counter = 1;
  for( std::map< Node, std::vector< Node > >::iterator it = d_emap.begin(); it!=d_emap.end(); ++it ){
    Debug( c ) << "E" << counter << ": { ";
    for( int i = 0; i<(int)it->second.size(); i++ ){
      if( i!=0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << it->second[i];
    }
    Debug( c ) << " }";
    Debug( c ) << ", disequal : ";
    std::map< Node, std::vector< Node > >::iterator itd = d_dmap.find( it->first );
    if( itd!=d_dmap.end() ){
      for( int i = 0; i<(int)itd->second.size(); i++ ){
        if( i!=0 ){
          Debug( c ) << ", ";
        }
        int counter2 = 1;
        std::map< Node, std::vector< Node > >::iterator it4 = d_emap.begin();
        while( it4!=d_emap.end() && !areEqual( it4->first, itd->second[i] ) ){
          ++it4;
          ++counter2;
        }
        if( it4==d_emap.end() ){
          Debug( c ) << getRepresentative( itd->second[i] );
        }else{
          Debug( c ) << "E" << counter2;
        }
      }
    }
    ++counter;
    //Debug( c ) << ", rep = " << it->first;
    Debug( c ) << std::endl;
  }
  Debug( c ) << std::endl;

  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    Node f = it->first;
    Debug( c ) << f << std::endl;
    Debug( c ) << "   Inst constants:" << std::endl;
    Debug( c ) << "      ";
    for( int i=0; i<(int)it->second.size(); i++ ){
      if( i>0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << it->second[i];
      if(d_terms_full.find( it->second[i] )==d_terms_full.end()){
        Debug( c ) << " (inactive)";
      }
    }
    Debug( c ) << std::endl;
    Debug( c ) << "   Obligations:" << std::endl;
    NodeLists::iterator ob_i = d_obligations.find( f );
    if( ob_i!=d_obligations.end() ){
      NodeList* ob = (*ob_i).second;
      for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
        Debug( c ) << "      " << ( !d_ob_pol[*it] ? "NOT " : "" );
        Debug( c ) << *it << std::endl;
      }
    }
  }

  Debug( c ) << std::endl;
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
  if( d_reps.find( a )!=d_reps.end() ){
    return d_reps[a];
  }else{
    return a;
  }
}

void InstantiatorTheoryUf::process( Node f, int effort ){
  Debug("quant-uf") << "UF: Try to solve (" << effort << ") for " << f << "... " << std::endl;
  if( effort>4 ){
    if( d_status==STATUS_SAT ){
      Debug("quant-uf-stuck") << "Stuck at this state:" << std::endl;
      debugPrint("quant-uf-stuck");
    }
    d_quantStatus = STATUS_UNKNOWN;
  }else if( effort==0 ){
    //calculate base matches
    d_baseMatch[f] = InstMatch( f, d_instEngine );
    //check if any instantiation constants are solved for
    for( int j = 0; j<(int)d_instEngine->d_inst_constants[f].size(); j++ ){
      Node i = d_instEngine->d_inst_constants[f][j];
      if( d_instEngine->getTheoryEngine()->theoryOf( i )==getTheory() ){
        if( d_terms_full.find( i )!=d_terms_full.end() ){
          Node rep = getRepresentative( i );
          if( !rep.hasAttribute(InstConstantAttribute()) ){
            d_baseMatch[f].setMatch( i, rep );
          }
        }//else{
          //d_baseMatch[f].setMatch( i, NodeManager::currentNM()->mkVar( i.getType() ) );
        //}
      }
    }
    //check if f is counterexample-solved
    if( d_baseMatch[f].isComplete() ){
      d_instEngine->addInstantiation( &d_baseMatch[f] );
    }
  }else{
    NodeLists::iterator ob_i = d_obligations.find( f );
    if( ob_i!=d_obligations.end() ){
      NodeList* ob = (*ob_i).second;
      if( effort==1 ){
        UIterator::d_splitThreshold = 0;
        // for each literal asserted about the negation of the body of f
        d_mergeIter[ f ] = UIterator::mkUIterator( false );
        for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
          Node lit = (*it);
          d_mergeIter[ f ]->d_children.push_back( UIterator::mkCombineUIterator( lit[0], lit[1], d_ob_pol[lit], f ) );
        }
        while( d_mergeIter[ f ]->getNextMatch() ){
          // f is E-induced
          InstMatch temp( d_mergeIter[ f ]->getCurrent() );
          temp.add( d_baseMatch[f] );
          if( d_instEngine->addInstantiation( &temp ) ){
            break;
          }
        }
      }else if( effort<4 ){
        d_mergeIter[ f ]->clearMatches();
        Debug("quant-uf-alg") << "Here is the merge iterator: " << std::endl;
        d_mergeIter[ f ]->debugPrint( "quant-uf-alg", 0 );
        UIterator::d_splitThreshold = effort==2 ? 1 : 2;
        while( d_mergeIter[ f ]->getNextMatch() ){
          // f is (conditionally) E-induced
          InstMatch temp( d_mergeIter[ f ]->getCurrent() );
          temp.add( d_baseMatch[f] );
          if( d_instEngine->addInstantiation( &temp ) ){
            Debug("quant-uf") << "Added this inst match: " << std::endl;
            temp.debugPrint( "quant-uf" );
            //add corresponding splits
            for( std::map< Node, Node >::iterator it = temp.d_splits.begin(); it != temp.d_splits.end(); ++it ){
              addSplitEquality( it->first, it->second, true, true );
            }
            break;
          }
        }
      }else if( effort==4 ){
        Debug("quant-uf-alg") << "Here is the merge iterator: " << std::endl;
        d_mergeIter[ f ]->debugPrint( "quant-uf-alg", 0 );
        std::map< UIterator*, UIterator* > index;
        std::vector< UIterator* > unmerged;
        std::vector< UIterator* > cover;
        double score;
        if( d_mergeIter[ f ]->empty() ){
          score = d_mergeIter[ f ]->collectUnmerged( index, unmerged, cover );
        }else{
          score = 1.0;
        }
        Debug("quant-uf-alg") << "Score = " << score << std::endl;
        Debug("quant-uf-alg") << "Here are the unmerged points: " << std::endl;
        for( int i=0; i<(int)unmerged.size(); i++ ){
          unmerged[i]->debugPrint( "quant-uf-alg", 1, false );
        }
        Debug("quant-uf-alg") << "Here are the covering points: " << std::endl;
        for( int i=0; i<(int)cover.size(); i++ ){
          cover[i]->debugPrint( "quant-uf-alg", 1, false );
          cover[i]->d_mg.debugPrint( "quant-uf-alg" );
        }
        bool success = false;
        for( int i=0; i<(int)cover.size(); i++ ){
          //see if we can construct any complete instantiations 
          cover[i]->reset();
          while( !success && cover[i]->getNextMatch() ){
            if( cover[i]->getCurrent()->isComplete( &d_baseMatch[f] ) ){
              InstMatch temp( cover[i]->getCurrent() );
              temp.add( d_baseMatch[f] );
              if( d_instEngine->addInstantiation( &temp ) ){
                success = true;
                for( std::map< Node, Node >::iterator it = temp.d_splits.begin(); it != temp.d_splits.end(); ++it ){
                  addSplitEquality( it->first, it->second, true, true );
                }
              }
            }
          }
        }
        if( !success ){
          std::vector< std::pair< Node, Node > > splits;
          std::vector< std::pair< Node, Node > > matchFails;
          for( int i=0; i<(int)unmerged.size(); i++ ){
            //process each unmerged point
            if( unmerged[i]->isCombine() ){
              //determine why it has no children
              //matchFails.push_back( std::pair< Node, Node >( unmerged[i]->d_t, unmerged[i]->d_s ) );
              //unmerged[i]->resolveMatch();
            }else{
              //add splits?
            }
          }
        }

        ////resolve matches on the literal level
        //d_matchable[f] = true;
        //d_unmatched[f] = false;
        //std::vector< std::pair< Node, Node > > splits;
        //for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
        //  Node lit = (*it);
        //  Node t = lit[0];
        //  Node s = lit[1];
        //  int ind = d_ob_pol[lit] ? 0 : 1;
        //  Debug("quant-uf-alg") << "Process obligation " << ( !d_ob_pol[*it] ? "NOT " : "" );
        //  Debug("quant-uf-alg") << (*it) << std::endl;
        //  calculateEIndLitCandidates( t, s, f, d_ob_pol[lit] );
        //  if( !d_litMatchCandidates[ind][t][s].empty() ){
        //    Debug("quant-uf-alg") << "-> Literal is matched." << std::endl;
        //  }else{
        //    bool litMatchable = true;
        //    bool litUnmatched = false;
        //    for( int i=0; i<2; i++ ){
        //      if( lit[i].hasAttribute(InstConstantAttribute()) ){
        //        calculateMatches( f, lit[i] );
        //        if( d_matches[ lit[i] ].empty() ){
        //          litMatchable = false;
        //          if( d_anyMatches[ lit[i] ].empty() ){
        //            litUnmatched = true;
        //            break;
        //          }
        //        }
        //      }
        //    }
        //    if( litMatchable ){
        //      int prevSplitSize = (int)splits.size();
        //      for( int i=0; i<(int)d_matches[t].size(); i++ ){
        //        Node mt = d_matches[t][i];
        //        if( s.getAttribute(InstConstantAttribute())==f ){
        //          for( int j=0; j<(int)d_matches[s].size(); j++ ){
        //            Node ms = d_matches[s][j];
        //            if( !areEqual( mt, ms ) && !areDisequal( mt, ms ) ){
        //              splits.push_back( std::pair< Node, Node >( mt, ms ) );
        //            }
        //          }
        //        }else{
        //          if( !areEqual( mt, s ) && !areDisequal( mt, s ) ){
        //            splits.push_back( std::pair< Node, Node >( mt, s ) );
        //          }
        //        }
        //      }
        //      if( prevSplitSize!=(int)splits.size() ){
        //        Debug("quant-uf-alg") << "-> Literal has possible matches." << std::endl;
        //      }else{
        //        litMatchable = false;
        //      }
        //    }
        //    if( !litMatchable ){
        //      d_matchable[f] = false;
        //      if( litUnmatched ){
        //        Debug("quant-uf-alg") << "-> Literal is unmatched." << std::endl;
        //        d_unmatched[f] = true;
        //      }else{
        //        Debug("quant-uf-alg") << "-> Literal is not matchable." << std::endl;
        //      }
        //    }
        //  }
        //}
        //if( d_matchable[f] ){
        //  for( int i=0; i<(int)splits.size(); i++ ){
        //    addSplitEquality( splits[i].first, splits[i].second );
        //  }
        //}
      }else if( effort==3 ){
        //if( d_matchable[f] ){
        //  //resolve ground argument mismatches
        //  for( int i=0; i<(int)UIterator::d_splits[f].size(); i++ ){
        //    addSplitEquality( UIterator::d_splits[f][i].first, UIterator::d_splits[f][i].second );
        //  }
        //}
      }else{


      }
    }
  }



      //  calculateEIndLitCandidates( lit[0], lit[1], f, d_ob_pol[lit] );
      //  int ind = d_ob_pol[lit] ? 0 : 1;
      //  if( !d_litMatchCandidates[ind][lit[0]][lit[1]].empty() ){
      //    Debug("quant-uf-alg") << "-> Literal is literal-matched." << std::endl;
      //  }else{
      //    if( effort<4 ){
      //      Debug("quant-uf-alg") << "-> Literal is not literal-matched." << std::endl;
      //      process = false;
      //      break;
      //    }else{
      //      bool matchable = true;
      //      bool unmatched = false;
      //      for( int i=0; i<2; i++ ){
      //        if( lit[i].hasAttribute(InstConstantAttribute()) ){
      //          calculateMatches( f, lit[i] );
      //          if( d_matches[ lit[i] ].empty() ){
      //            matchable = false;
      //            if( d_anyMatches[ lit[i] ].empty() ){
      //              unmatched = true;
      //              break;
      //            }
      //          }
      //        }
      //      }
      //      if( matchable ){
      //        litMatchFails.push_back( lit );
      //        Debug("quant-uf-alg") << "-> Literal is matchable." << std::endl;
      //      }else if( unmatched ){
      //        process = false;
      //        Debug("quant-uf-alg") << "-> Literal is unmatched." << std::endl;
      //      }else{
      //        Debug("quant-uf-alg") << "-> Literal is not matchable." << std::endl;
      //      }
      //    }
      //  }
      //}
      //if( process ){
      //  bool addedLemma = false;
      //  if( litMatchFails.empty() ){
      //    ////create iterators over the candidate matches
      //    //std::vector< int > litMatchCandidateIter;
      //    //litMatchCandidateIter.resize( ob->size(), 1 );
      //    MergeUIterator mi;
      //    for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
      //      Node lit = (*it);
      //      mi.d_children.push_back( CombineUIterator( lit[0], lit[1], d_ob_pol[lit], f ) );
      //    }

  Debug("quant-uf-alg") << std::endl;
}


void InstantiatorTheoryUf::calculateMatches( Node f, Node t ){
  Assert( t.getAttribute(InstConstantAttribute())==f );
  if( d_matches.find( t )==d_matches.end() ){
    d_matches[t].clear();
    d_anyMatches[t].clear();
    for( BoolMap::const_iterator it = d_terms_full.begin(); it!=d_terms_full.end(); ++it ){
      Node c = (*it).first;
      if( t!=c && t.getType()==c.getType() ){
        calculateEqDep( t, c, f );
        if( d_eq_dep[t][c] ){
          if( !c.hasAttribute(InstConstantAttribute()) ){
            d_matches[t].push_back( c );
          }else{
            d_anyMatches[t].push_back( c );
          }
        }
      }
    }
  }
}

void InstantiatorTheoryUf::calculateEIndLitCandidates( Node t, Node s, Node f, bool isEq ){
  int ind = isEq ? 0 : 1;
  if( d_litMatchCandidates[ind].find( t )==d_litMatchCandidates[ind].end() ||
      d_litMatchCandidates[ind][t].find( s )==d_litMatchCandidates[ind][t].end() ){
    Debug("quant-uf-ematch") << "Calc Eind lit candidates " << t << (isEq ? " = " : " != " ) << s << std::endl;
    if( !isEq ){
      Assert( t.getAttribute(InstConstantAttribute())==f );
      if( s.getAttribute(InstConstantAttribute())==f  ){
        //a disequality between two triggers
        //for each equivalence class E
        for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
          Node ct = (*it1).first;
          Assert( ct==getRepresentative( ct ) );
          if( ct.getType()==t.getType() && !ct.hasAttribute(InstConstantAttribute()) ){
            calculateEIndLitCandidates( t, ct, f, true );
            if( !d_litMatchCandidates[0][t][ct].empty() ){
              //for each equivalence class disequal from E
              for( int j=0; j<(int)d_dmap[ct].size(); j++ ){
                Node cs = d_dmap[ct][j];
                Assert( cs==getRepresentative( cs ) );
                if( !cs.hasAttribute(InstConstantAttribute()) ){
                  calculateEIndLitCandidates( s, cs, f, true );
                  if( !d_litMatchCandidates[0][s][cs].empty() ){
                    // could be the case that t matches ct and s matches cs
                    Kind knd = ct.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
                    Node ceq = NodeManager::currentNM()->mkNode( knd, ct, cs );
                    d_litMatchCandidates[1][t][s].push_back( ceq );
                  }
                }
              }
            }
          }
        }
      }else{
        Assert( !s.hasAttribute(InstConstantAttribute()) );
        //a disequality between a trigger and ground term
        Node c = getRepresentative( s );
        //match against all equivalence classes disequal from c
        for( int j=0; j<(int)d_dmap[c].size(); j++ ){
          Node ct = d_dmap[c][j];
          Assert( ct==getRepresentative( ct ) );
          if( !ct.hasAttribute(InstConstantAttribute()) ){
            calculateEIndLitCandidates( t, ct, f, true );  
            if( !d_litMatchCandidates[0][t][ct].empty() ){
              //it could be the case that t matches with ct
              d_litMatchCandidates[1][t][s].push_back( ct );
            }
          }
        }
      }
    }else{
      if( s.getAttribute(InstConstantAttribute())==f ){
        //equality between two triggers
        //for each equivalence class
        for( std::map< Node, std::vector< Node > > ::iterator it1 = d_emap.begin(); it1!=d_emap.end(); ++it1 ){
          Node c = (*it1).first;
          if( c.getType()==t.getType() && !c.hasAttribute(InstConstantAttribute()) ){
            calculateEIndLitCandidates( t, c, f, true );
            if( !d_litMatchCandidates[0][t][c].empty() ){
              calculateEIndLitCandidates( s, c, f, true );
              if( !d_litMatchCandidates[0][s][c].empty() ){
                // both have a chance to match in the equivalence class, thus i1 = i2 may be forced by c
                d_litMatchCandidates[0][t][s].push_back( c );
              }
            }
          }
        }
      }else{
        Assert( !s.hasAttribute(InstConstantAttribute()) );
        Node c = getRepresentative( s );
        Assert( !c.hasAttribute(InstConstantAttribute()) );
        if( d_litMatchCandidates[0].find( t )==d_litMatchCandidates[0].end() ||
            d_litMatchCandidates[0][t].find( c )==d_litMatchCandidates[0][t].end() ){
          Debug("quant-uf-ematch") << "EIndMod " << t << " = " << c << std::endl;
          //equality between trigger and concrete ground term
          //build E-matches with terms in the same equivalence class
          if( t.getKind()==INST_CONSTANT || d_emap.find( c )==d_emap.end() ){
            //there is no need in scanning the equivalence class of c 
            //(either singleton or instantiation constant case)
            calculateEqDep( t, c, f );
            if( d_eq_dep[t][c] ){
              d_litMatchCandidates[0][t][c].push_back( c );
            }
          }else{
            for( int j=0; j<(int)d_emap[c].size(); j++ ){
              Node ca = d_emap[c][j];
              if( !ca.hasAttribute(InstConstantAttribute()) ){
                calculateEqDep( t, ca, f );
                if( d_eq_dep[t][ca] ){
                  d_litMatchCandidates[0][t][c].push_back( ca );
                }
              }
            }
          }
        }
        if( s!=c ){
          d_litMatchCandidates[0][t][s].insert( d_litMatchCandidates[0][t][s].begin(),
                                                d_litMatchCandidates[0][t][c].begin(),
                                                d_litMatchCandidates[0][t][c].end() );
        }
      }
    }
  }
}

void InstantiatorTheoryUf::calculateEqDep( Node i, Node c, Node f ){
  if( d_eq_dep.find( i )==d_eq_dep.end() ||
      d_eq_dep[i].find( c )==d_eq_dep[i].end() ){
    if( i.getKind()==INST_CONSTANT ){
      d_eq_dep[i][c] = true;
    }else if( c.getKind()!=APPLY_UF || i.getOperator()!=c.getOperator() ){
      d_eq_dep[i][c] = false;
    }else{
      Assert( i.getKind()==APPLY_UF && c.getKind()==APPLY_UF );
      Assert( i.getNumChildren()==c.getNumChildren() );
      d_eq_dep[i][c] = true;
      for( int j=0; j<(int)c.getNumChildren(); j++ ){
        if( areDisequal( i[j], c[j] ) ){
          d_eq_dep[i][c] = false;
          break;
        }
      }
    }
  }
}

bool InstantiatorTheoryUf::addSplitEquality( Node n1, Node n2, bool reqPhase, bool reqPhasePol ){
  Assert( !n1.hasAttribute(InstConstantAttribute()) );
  Assert( !n2.hasAttribute(InstConstantAttribute()) );
  Assert( !areEqual( n1, n2 ) );
  Assert( !areDisequal( n1, n2 ) );
  Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  Node fm = NodeManager::currentNM()->mkNode( knd, n1, n2 );
  fm = Rewriter::rewrite( fm );
  if( d_instEngine->addSplit( fm ) ){
    Debug("quant-uf-split") << "*** Add split " << n1 << " = " << n2 << std::endl;
    //require phase?
    if( reqPhase ){
      d_instEngine->d_curr_out->requirePhase( fm, reqPhasePol );
    }
    return true;
  }else{
    return false;
  }
}

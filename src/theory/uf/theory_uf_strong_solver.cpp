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

#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine_impl.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

void StrongSolverTheoryUf::ConflictFind::Region::setDisequal( Node n1, Node n2, int type, bool valid ){
  Assert( isDisequal( n1, n2, type )!=valid );

  d_disequalities[type][ n1 ][ n2 ] = valid;
  if( valid ){
    d_disequalities_size[type][ n1 ]++;
    d_total_disequalities_size[type]++;
  }else{
    d_disequalities_size[type][ n1 ]--;
    d_total_disequalities_size[type]--;
  }
}

bool StrongSolverTheoryUf::ConflictFind::Region::isDisequal( Node n1, Node n2, int type ){
  return d_disequalities[type][n1].find( n2 )!=d_disequalities[type][n1].end() && d_disequalities[type][n1][n2];
}

void StrongSolverTheoryUf::ConflictFind::Region::takeNode( StrongSolverTheoryUf::ConflictFind::Region& r, Node n ){
  //make external equalities internal, and vice versa
  for( int t=0; t<2; t++ ){
    Region* tr = t==0 ? this : &r;
    for( std::map< Node, std::map< Node, bool > >::iterator it = tr->d_disequalities[t].begin();
        it != tr->d_disequalities[t].end(); ++it ){
      Node n1 = it->first;
      if( tr->d_reps[ n1 ] && it->second.find( n )!=it->second.end() && it->second[ n ] ){
        //flip internal/external
        tr->setDisequal( n1, n, t, false );
        tr->setDisequal( n1, n, t==0 ? 1 : 0, true );
      }
    }
  }
  d_reps[n] = true;
  d_reps_size++;
  //remove representative
  r.d_reps[n] = false;
  r.d_reps_size--;
}

void StrongSolverTheoryUf::ConflictFind::Region::merge( StrongSolverTheoryUf::ConflictFind::Region& r ){
  //add new representatives
  for( std::map< Node, bool >::iterator it = r.d_reps.begin(); it != r.d_reps.end(); ++it ){
    if( it->second ){
      Node n1 = it->first;
      d_reps[ n1 ] = true;
      d_reps_size++;
      //take disequalities from n1
      for( int t=0; t<2; t++ ){
        for( std::map< Node, bool >::iterator it = r.d_disequalities[t][n1].begin(); it != r.d_disequalities[t][n1].end(); ++it ){
          if( it->second ){
            Node n2 = it->first;
            if( t==0 && hasRep( n2 ) ){
              //external is now internal
              setDisequal( n2, n1, 0, false );
              setDisequal( n2, n1, 1, true );
              //add disequality
              setDisequal( n1, n2, 1, true );
            }else{
              setDisequal( n1, n2, t, true );
            }
          }
        }
      }
    }
  }
}

/** setEqual */
void StrongSolverTheoryUf::ConflictFind::Region::setEqual( Node a, Node b ){
  Assert( hasRep( a ) && hasRep( b ) );
  //move disequalities of b over to a
  for( int t=0; t<2; t++ ){
    for( std::map< Node, bool >::iterator it = d_disequalities[t][b].begin(); it != d_disequalities[t][b].end(); ++it ){
      if( it->second ){
        Node n = it->first;
        if( !isDisequal( a, n, t ) ){
          setDisequal( a, n, t, true );
        }
        setDisequal( b, n, t, false );
      }
    }
  }
  //remove b from representatives
  d_reps[b] = false;
  d_reps_size--;
}

void StrongSolverTheoryUf::ConflictFind::mergeRegions( int ai, int bi ){
  Assert( d_valid[ai] && d_valid[bi] );
  for( std::map< Node, bool >::iterator it = d_regions[bi].d_reps.begin(); it != d_regions[bi].d_reps.end(); ++it ){
    if( it->second ){
      d_regions_map[ it->first ] = ai;
    }
  }
  d_regions[ai].merge( d_regions[bi] );
  d_valid[bi] = false;
}

/** new node */
void StrongSolverTheoryUf::ConflictFind::newEqClass( Node n ){
  if( d_regions_map.find( n )==d_regions_map.end() ){
    d_regions_map[n] = (int)d_regions.size();
    d_regions.push_back( Region( n ) );
    d_valid.push_back( true );
  }
}

/** merge */
void StrongSolverTheoryUf::ConflictFind::merge( Node a, Node b ){
  Assert( d_regions_map.find( a )!=d_regions_map.end() );
  Assert( d_regions_map.find( b )!=d_regions_map.end() );
  int ai = d_regions_map[a];
  int bi = d_regions_map[b];
  //change all external disequalities to now be disequal from b
  for( std::map< Node, bool >::iterator it = d_regions[bi].d_disequalities[0][b].begin(); 
       it != d_regions[bi].d_disequalities[0][b].end(); ++it ){
    if( it->second ){
      int ci = d_regions_map[ it->first ];
      d_regions[ci].setDisequal( it->first, b, 0, false );
      if( !d_regions[ci].isDisequal( it->first, a, 0 ) ){
        d_regions[ci].setDisequal( it->first, a, ai==ci ? 1 : 0, true );
      }
    }
  }
  int ri;
  if( ai!=bi ){
    // either add a to d_regions[bi], or b to d_regions[ai]
    int ext[2];
    for( int i=0; i<2; i++ ){
      int ci = i==0 ? ai : bi;
      int di = i==0 ? bi : ai;
      Node c = i==0 ? a : b;
      ext[i] = d_regions[ci].d_disequalities_size[1][c];
      for( std::map< Node, bool >::iterator it = d_regions[ci].d_disequalities[0][c].begin(); 
           it != d_regions[ci].d_disequalities[0][c].end(); ++it ){
        if( it->second && d_regions[di].hasRep( it->first ) ){
          ext[i]--;
        }
      }
    }
    //based on which would produce the fewest number of external disequalities
    if( ext[0]<ext[1] ){
      ri = bi;
      d_regions[bi].takeNode( d_regions[ai], a ); 
    }else{
      ri = ai;
      d_regions[ai].takeNode( d_regions[bi], b ); 
    }
  }else{
    ri = ai;
  }
  //now, do merge within d_regions[ri]
  d_regions[ri].setEqual( a, b );
}

/** unmerge */
void StrongSolverTheoryUf::ConflictFind::undoMerge( Node a, Node b ){

}

/** assert terms are disequal */
void StrongSolverTheoryUf::ConflictFind::assertDisequal( Node a, Node b ){
  //if they are not already disequal
  if( !d_th->d_equalityEngine.areDisequal( a, b ) ){
    Assert( d_regions_map.find( a )!=d_regions_map.end() );
    Assert( d_regions_map.find( b )!=d_regions_map.end() );
    int ai = d_regions_map[a];
    int bi = d_regions_map[b];
    if( ai==bi ){
      //internal disequality
      d_regions[ai].setDisequal( a, b, 1, true );
      d_regions[ai].setDisequal( b, a, 1, true );
    }else{
      //external disequality
      d_regions[ai].setDisequal( a, b, 0, true );
      d_regions[bi].setDisequal( b, a, 0, true );
    }
  }
}

/** check */
void StrongSolverTheoryUf::ConflictFind::check( Theory::Effort level ){
  if( level==Theory::FULL_EFFORT ){
    //validate regions: maintain the invariant that no cliques can exist between regions
    for( int i=0; i<(int)d_regions.size(); i++ ){
      if( d_valid[i] ){
        
      }
    }
    //do a quick check for cliques within each region
    for( int i=0; i<(int)d_regions.size(); i++ ){
      if( d_valid[i] && d_regions[i].d_reps_size>d_cardinality ){
        //see if they form a clique
        std::vector< Node > testClique;
        for( std::map< Node, bool >::iterator it = d_regions[i].d_reps.begin(); it != d_regions[i].d_reps.end(); ++ it ){
          if( it->second ){
            testClique.push_back( it->first );
            if( testClique.size()>d_cardinality ){
              break;
            }
          }
        }
        Assert( testClique.size()==(d_cardinality+1) );
        Node split;
        for( int j=0; j<(int)testClique.size(); j++ ){
          for( int k=(j+1); k<(int)testClique.size(); k++ ){
            if( !d_regions[i].isDisequal( testClique[j], testClique[k], 1 ) ){
              split = NodeManager::currentNM()->mkNode( EQUAL, testClique[j], testClique[k] );
              break;
            }
          }
          if( split!=Node::null() ){
            break;
          }
        }
        if( split==Node::null() ){
          //clique discovered, explain clique
        }else{
          //do split
        }
      }
    }
  }
}

StrongSolverTheoryUf::StrongSolverTheoryUf(context::Context* c, TheoryUF* th) :
d_th( th )
{

}

/** new node */
void StrongSolverTheoryUf::newEqClass( Node n ){
  Debug("ss-uf") << "StrongSolverTheoryUf: New eq class " << n << std::endl;
  TypeNode tn = n.getType();
  if( d_conf_find.find( tn )!=d_conf_find.end() ){
    d_conf_find[tn].newEqClass( n );
  }
}

/** merge */
void StrongSolverTheoryUf::merge( Node a, Node b ){
  Debug("ss-uf") << "StrongSolverTheoryUf: Merge " << a << " " << b << std::endl;
  TypeNode tn = a.getType();
  if( d_conf_find.find( tn )!=d_conf_find.end() ){
    d_conf_find[tn].merge( a, b );
  }
}

/** unmerge */
void StrongSolverTheoryUf::undoMerge( Node a, Node b ){
  Debug("ss-uf") << "StrongSolverTheoryUf: Undo merge " << a << " " << b << std::endl;
  TypeNode tn = a.getType();
  if( d_conf_find.find( tn )!=d_conf_find.end() ){
    d_conf_find[tn].undoMerge( a, b );
  }
}

/** assert terms are disequal */
void StrongSolverTheoryUf::assertDisequal( Node a, Node b ){
  Debug("ss-uf") << "StrongSolverTheoryUf: Assert disequal " << a << " " << b << std::endl;
  TypeNode tn = a.getType();
  if( d_conf_find.find( tn )!=d_conf_find.end() ){
    d_conf_find[tn].assertDisequal( a, b );
  }
}

/** check */
void StrongSolverTheoryUf::check( Theory::Effort level ){
  Debug("ss-uf") << "StrongSolverTheoryUf: check " << level << std::endl;
  if( level==Theory::FULL_EFFORT ){
    debugPrint( "ss-uf-debug" );
  }
  for( std::map< TypeNode, ConflictFind >::iterator it = d_conf_find.begin(); it != d_conf_find.end(); ++it ){
    it->second.check( level );
  }
}

void StrongSolverTheoryUf::debugPrint( const char* c ){
  EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
  while( !eqc_iter.isFinished() ){
    Debug( c ) << "Eq class [[" << (*eqc_iter) << "]]" << std::endl;
    EqClassIterator< TheoryUF::NotifyClass > eqc_iter2( *eqc_iter, &((TheoryUF*)d_th)->d_equalityEngine );
    Debug( c ) << "   ";
    while( !eqc_iter2.isFinished() ){
      Debug( c ) << "[" << (*eqc_iter2) << "] ";
      eqc_iter2++;
    }
    Debug( c ) << std::endl;
    eqc_iter++;
  }
}

/** set cardinality for sort */
void StrongSolverTheoryUf::setCardinality( TypeNode t, int c ) 
{ 
  if( d_conf_find.find( t )!=d_conf_find.end() ){
    d_conf_find[t] = ConflictFind( d_th );
  }
  d_conf_find[t].d_cardinality = c; 
}
/** get cardinality for sort */
int StrongSolverTheoryUf::getCardinality( TypeNode t ) 
{ 
  return d_conf_find.find( t )!=d_conf_find.end() ? d_conf_find[t].d_cardinality : -1; 
}

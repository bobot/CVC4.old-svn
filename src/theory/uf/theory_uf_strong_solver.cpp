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

void StrongSolverTheoryUf::ConflictFind::Region::takeNode( StrongSolverTheoryUf::ConflictFind::Region* r, Node n ){
  Assert( !hasRep( n ) );
  Assert( r->hasRep( n ) );
  //take disequalities from r
  RegionNodeInfo* rni = r->d_nodes[n];
  for( int t=0; t<2; t++ ){
    RegionNodeInfo::DiseqList* del = rni->d_disequalities[t];
    for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
      if( (*it).second ){
        r->setDisequal( n, (*it).first, t, false );
        if( t==0 ){
          if( hasRep( (*it).first ) ){
            setDisequal( (*it).first, n, 0, false );
            setDisequal( (*it).first, n, 1, true );
            setDisequal( n, (*it).first, 1, true );
          }else{
            setDisequal( n, (*it).first, 0, true );
          }
        }else{
          r->setDisequal( (*it).first, n, 1, false );
          r->setDisequal( (*it).first, n, 0, true );
          setDisequal( n, (*it).first, 0, true );
        }
      }
    }
  }
  //add representative
  setRep( n, true );
  //remove representative
  r->setRep( n, false );
}

void StrongSolverTheoryUf::ConflictFind::Region::combine( StrongSolverTheoryUf::ConflictFind::Region* r ){
  //take all nodes from r
  for( std::map< Node, RegionNodeInfo* >::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      setRep( it->first, true );
    }
  }
  for( std::map< Node, RegionNodeInfo* >::iterator it = r->d_nodes.begin(); it != r->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      //take disequalities from r
      Node n = it->first;
      RegionNodeInfo* rni = it->second;
      for( int t=0; t<2; t++ ){
        RegionNodeInfo::DiseqList* del = rni->d_disequalities[t];
        for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
          if( (*it2).second ){
            if( t==0 && hasRep( (*it2).first ) ){
              setDisequal( (*it2).first, n, 0, false );
              setDisequal( (*it2).first, n, 1, true );
              setDisequal( n, (*it2).first, 1, true );
            }else{
              setDisequal( n, (*it2).first, t, true );
            }
          }
        }
      }
    }
  }
  r->d_valid = false;
}

void StrongSolverTheoryUf::ConflictFind::Region::setRep( Node n, bool valid ){
  Assert( hasRep( n )!=valid );
  if( d_nodes.find( n )==d_nodes.end() && valid ){
    d_nodes[n] = new RegionNodeInfo( d_cf->d_th->getContext() );
  }
  d_nodes[n]->d_valid = valid;
  d_reps_size = d_reps_size + ( valid ? 1 : -1 );
  if( d_testClique.find( n )!=d_testClique.end() && d_testClique[n] ){
    Assert( !valid );
    d_testClique[n] = false;
    d_testCliqueSize = d_testCliqueSize - 1;
    //remove all splits involving n
    for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
      if( (*it).second ){
        if( (*it).first[0]==n || (*it).first[1]==n ){
          d_splits[ (*it).first ] = false;
          d_splitsSize = d_splitsSize - 1;
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
    RegionNodeInfo::DiseqList* del = d_nodes[b]->d_disequalities[t];
    for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
      if( (*it).second ){
        Node n = (*it).first;
        Region* nr = d_cf->d_regions[ d_cf->d_regions_map[ n ] ];
        if( !isDisequal( a, n, t ) ){
          setDisequal( a, n, t, true );
          nr->setDisequal( n, a, t, true );
        }
        setDisequal( b, n, t, false );
        nr->setDisequal( n, b, t, false );
      }
    }
  }
  //remove b from representatives
  setRep( b, false );
}

void StrongSolverTheoryUf::ConflictFind::Region::setDisequal( Node n1, Node n2, int type, bool valid ){
  Assert( isDisequal( n1, n2, type )!=valid );
  d_nodes[ n1 ]->d_disequalities[type]->setDisequal( n2, valid );
  if( type==0 ){
    d_total_diseq_external = d_total_diseq_external + ( valid ? 1 : -1 );
  }else{
    d_total_diseq_internal = d_total_diseq_internal + ( valid ? 1 : -1 );
    if( valid ){
      //if they are both a part of testClique, then remove split
      if( d_testClique.find( n1 )!=d_testClique.end() && d_testClique[n1] &&
          d_testClique.find( n2 )!=d_testClique.end() && d_testClique[n2] ){
        Node eq = NodeManager::currentNM()->mkNode( EQUAL, n1, n2 );
        if( d_splits.find( eq )!=d_splits.end() && d_splits[ eq ] ){
          Debug("uf-ss-debug") << "removing split for " << n1 << " " << n2 << std::endl;
          d_splits[ eq ] = false;
          d_splitsSize = d_splitsSize - 1;
        }
      }
    }
  }
}

bool StrongSolverTheoryUf::ConflictFind::Region::isDisequal( Node n1, Node n2, int type ){
  RegionNodeInfo::DiseqList* del = d_nodes[ n1 ]->d_disequalities[type];
  return del->d_disequalities.find( n2 )!=del->d_disequalities.end() && del->d_disequalities[n2];
}

bool StrongSolverTheoryUf::ConflictFind::Region::getMustCombine( int cardinality ){
  if( d_total_diseq_external>=cardinality ){
    //The number of external disequalities is greater than or equal to cardinality.
    //Thus, a clique of size cardinality+1 may exist between nodes in d_regions[i] and other regions
    //Check if this is actually the case:  must have n nodes with outgoing degree (cardinality+1-n) for some n>0
    std::vector< int > degrees;
    for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
      RegionNodeInfo* rni = it->second;
      if( rni->d_valid ){
        int outDeg = rni->d_disequalities[0]->d_size;
        if( outDeg>=cardinality ){
          return true;
        }else if( outDeg>0 ){
          degrees.push_back( outDeg );
          if( (int)degrees.size()>=cardinality ){
            return true;
          }
        }
      }
    }
    std::sort( degrees.begin(), degrees.end() );
    for( int i=0; i<(int)degrees.size(); i++ ){
      if( degrees[i]>=cardinality+1-((int)degrees.size()-i) ){
        return true;
      }
    }
  }
  return false;
}

struct sortInternalDegree {
  StrongSolverTheoryUf::ConflictFind::Region* r;
  bool operator() (Node i,Node j) { return (r->d_nodes[i]->getNumInternalDisequalities()>r->d_nodes[j]->getNumInternalDisequalities());}
};


bool StrongSolverTheoryUf::ConflictFind::Region::check( Theory::Effort level, unsigned cardinality, std::vector< Node >& clique ){
  if( d_reps_size>cardinality ){
    if( d_reps_size>cardinality && d_total_diseq_internal==d_reps_size*( d_reps_size - 1 ) ){
      //quick clique check, all reps form a clique
      for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
        if( it->second->d_valid ){
          clique.push_back( it->first );
        }
      }
      return true;
    }else{
      //build test clique, up to size cardinality+1
      if( d_testCliqueSize<=cardinality ){
        std::vector< Node > newClique;
        if( d_testCliqueSize<cardinality ){
          for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->d_valid && ( d_testClique.find( it->first )==d_testClique.end() || !d_testClique[ it->first ] ) ){
              newClique.push_back( it->first );
            }
          }
          //choose remaining nodes with the highest degrees
          sortInternalDegree sidObj;
          sidObj.r = this;
          std::sort( newClique.begin(), newClique.end(), sidObj );
          newClique.erase( newClique.begin() + ( cardinality - d_testCliqueSize ) + 1, newClique.end() );
        }else{
          //scan for the highest degree
          int maxDeg = -1;
          Node maxNode;
          for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->d_valid && ( d_testClique.find( it->first )==d_testClique.end() || !d_testClique[ it->first ] ) ){
              if( it->second->getNumInternalDisequalities()>maxDeg ){
                maxDeg = it->second->getNumInternalDisequalities();
                maxNode = it->first;
              }
            }
          }
          Assert( maxNode!=Node::null() );
          newClique.push_back( maxNode );
        }
        //check splits internal to new members
        for( int j=0; j<(int)newClique.size(); j++ ){
          Debug("uf-ss-debug") << "Choose to add clique member " << newClique[j] << std::endl;
          for( int k=(j+1); k<(int)newClique.size(); k++ ){
            if( !isDisequal( newClique[j], newClique[k], 1 ) ){
              d_splits[ NodeManager::currentNM()->mkNode( EQUAL, newClique[j], newClique[k] ) ] = true;
              d_splitsSize = d_splitsSize + 1;
            }
          }
          //check disequalities with old members
          for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++it ){
            if( (*it).second ){
              if( !isDisequal( (*it).first, newClique[j], 1 ) ){
                d_splits[ NodeManager::currentNM()->mkNode( EQUAL, (*it).first, newClique[j] ) ] = true;
                d_splitsSize = d_splitsSize + 1;
              }
            }
          }
        }
        //add new clique members to test clique
        for( int j=0; j<(int)newClique.size(); j++ ){
          d_testClique[ newClique[j] ] = true;
          d_testCliqueSize = d_testCliqueSize + 1;
        }
      }
      Assert( d_testCliqueSize==cardinality+1 );
      if( d_splitsSize==0 ){
        //test clique is a clique
        for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++it ){
          if( (*it).second ){
            clique.push_back( (*it).first );
          }
        }
        return true;
      }
    }
  }
  return false;
}

Node StrongSolverTheoryUf::ConflictFind::Region::getBestSplit(){
  //IMPROVE_THIS
  //take the first split you find
  for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
    if( (*it).second ){
      return (*it).first;
    }
  }
  return Node::null();
}

void StrongSolverTheoryUf::ConflictFind::Region::debugPrint( const char* c, bool incClique ){
  Debug( c ) << "Num reps: " << d_reps_size << std::endl;
  for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      Node n = it->first;
      Debug( c ) << "   " << n << std::endl;
      for( int i=0; i<2; i++ ){
        Debug( c ) << "      " << ( i==0 ? "Ext" : "Int" ) << " disequal:";
        RegionNodeInfo::DiseqList* del = rni->d_disequalities[i];
        for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
          if( (*it2).second ){
            Debug( c ) << " " << (*it2).first;
          }
        }
        Debug( c ) << ", total = " << del->d_size << std::endl;
      }
    }
  }
  Debug( c ) << "Total disequal: " << d_total_diseq_external << " external," << std::endl;
  Debug( c ) << "                " << d_total_diseq_internal<< " internal." << std::endl;

  if( incClique ){
    Debug( c ) << "Candidate clique members: " << std::endl;
    Debug( c ) << "   ";
    for( NodeBoolMap::iterator it = d_testClique.begin(); it != d_testClique.end(); ++ it ){
      if( (*it).second ){
        Debug( c ) << (*it).first << " ";
      }
    }
    Debug( c ) << ", size = " << d_testCliqueSize << std::endl;
    Debug( c ) << "Required splits: " << std::endl;
    Debug( c ) << "   ";
    for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++ it ){
      if( (*it).second ){
        Debug( c ) << (*it).first << " ";
      }
    }
    Debug( c ) << ", size = " << d_splitsSize << std::endl;
  }
}

void StrongSolverTheoryUf::ConflictFind::combineRegions( int ai, int bi ){
  Debug("uf-ss-region") << "uf-ss: Combine Region #" << bi << " with Region #" << ai << std::endl; 
  Assert( isValid( ai ) && isValid( bi ) );
  for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[bi]->d_nodes.begin(); it != d_regions[bi]->d_nodes.end(); ++it ){
    Region::RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      d_regions_map[ it->first ] = ai;
    }
  }
  //update regions disequal DO_THIS
  
  d_regions[ai]->combine( d_regions[bi] );
  //Debug("uf-ss-debug") << "Now in this state:" << std::endl;
  //debugPrint( "uf-ss" );
}

void StrongSolverTheoryUf::ConflictFind::moveNode( Node n, int ri ){
  Debug("uf-ss-region") << "uf-ss: Move node " << n << " to Region #" << ri << std::endl; 
  //update regions disequal DO_THIS
  Region::RegionNodeInfo::DiseqList* del = d_regions[ d_regions_map[n] ]->d_nodes[n]->d_disequalities[0];
  for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
    if( (*it).second ){
      
    }
  }
  //move node to region ri
  d_regions_map[n] = ri;
  d_regions[ri]->takeNode( d_regions[ d_regions_map[n] ], n );
}

int StrongSolverTheoryUf::ConflictFind::getNumDisequalitiesToRegion( Node n, int ri ){
  int ni = d_regions_map[n];
  int counter = 0;
  Region::RegionNodeInfo::DiseqList* del = d_regions[ni]->d_nodes[n]->d_disequalities[0];
  for( NodeBoolMap::iterator it = del->d_disequalities.begin(); it != del->d_disequalities.end(); ++it ){
    if( (*it).second ){
      if( d_regions_map[ (*it).first ]==ri ){
        counter++;
      }
    }
  }
  return counter;
}

void StrongSolverTheoryUf::ConflictFind::getDisequalitiesToRegions( int ri, std::map< int, int >& regions_diseq ){
  for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[ri]->d_nodes.begin(); 
       it != d_regions[ri]->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      Region::RegionNodeInfo::DiseqList* del = it->second->d_disequalities[0];
      for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
        if( (*it2).second ){
          Assert( isValid( d_regions_map[ (*it2).first ] ) );
          regions_diseq[ d_regions_map[ (*it2).first ] ]++;
        }
      }
    }
  }
}

void StrongSolverTheoryUf::ConflictFind::explainClique( std::vector< Node >& clique, OutputChannel* out ){
  Debug("uf-ss") << "Finding clique disequalities..." << std::endl;
  std::vector< Node > conflict;
  //collect disequalities, and nodes that must be equal within representatives
  std::map< Node, std::map< Node, bool > > explained;
  std::map< Node, std::map< Node, bool > > nodesWithinRep;
  for( int i=0; i<(int)d_disequalities_index; i++ ){
    //if both sides of disequality exist in clique
    Node r1 = d_th->d_equalityEngine.getRepresentative( d_disequalities[i][0][0] );
    Node r2 = d_th->d_equalityEngine.getRepresentative( d_disequalities[i][0][1] );
    if( ( explained.find( r1 )==explained.end() || explained[r1].find( r2 )==explained[r1].end() ) &&
        std::find( clique.begin(), clique.end(), r1 )!=clique.end() &&
        std::find( clique.begin(), clique.end(), r2 )!=clique.end() ){
      explained[r1][r2] = true;
      explained[r2][r1] = true;
      conflict.push_back( d_disequalities[i] );
      nodesWithinRep[r1][ d_disequalities[i][0][0] ] = true;
      nodesWithinRep[r2][ d_disequalities[i][0][1] ] = true;
    }
  }
  Assert( conflict.size()==d_cardinality*( d_cardinality+1 )/2 );
  Debug("uf-ss") << "Finding clique equalities internal to eq classes..." << std::endl;
  //now, we must explain equalities within each equivalence class
  for( std::map< Node, std::map< Node, bool > >::iterator it = nodesWithinRep.begin(); it != nodesWithinRep.end(); ++it ){
    if( it->second.size()>1 ){
      Node prev;
      //add explanation of t1 = t2 = ... = tn
      for( std::map< Node, bool >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        if( prev!=Node::null() ){
          //explain it2->first and prev
          std::vector< TNode > expl;
          d_th->d_equalityEngine.getExplanation( it2->first, prev, expl );
          for( int i=0; i<(int)expl.size(); i++ ){
            if( std::find( conflict.begin(), conflict.end(), expl[i] )==conflict.end() ){
              conflict.push_back( expl[i] );
            }
          }
        }
        prev = it2->first;
      }
    }
  }
  Debug("uf-ss") << "Explanation of clique = " << std::endl;
  for( int i=0; i<(int)conflict.size(); i++ ){
    Debug("uf-ss") << conflict[i] << " ";
  }
  Debug("uf-ss") << std::endl;
  //now, make the conflict
  Node conflictNode = conflict.size()==1 ? conflict[0] : NodeManager::currentNM()->mkNode( AND, conflict );
#if 0
  //add cardinality constraint
  Node cardNode = NodeManager::currentNM()->mkNode( CARDINALITY_CONSTRAINT, 
  conflictNode = NodeManager::currentNM()->mkNode( IMPLIES, cliqueNode, cardNode.notNode() );
  out->lemma( conflictNode );
#else
  Debug("uf-ss-lemma") << "*** Add conflict " << conflictNode.notNode() << std::endl;
  out->lemma( conflictNode.notNode() );
#endif
}

/** new node */
void StrongSolverTheoryUf::ConflictFind::newEqClass( Node n ){
  if( d_regions_map.find( n )==d_regions_map.end() ){
    d_regions_map[n] = d_regions_index;
    Debug("uf-ss") << "StrongSolverTheoryUf: New Eq Class " << n << std::endl;
    if( d_regions_index<d_regions.size() ){
      Assert( d_regions[ d_regions_index ]->d_valid );
      Assert( d_regions[ d_regions_index ]->getNumReps()==0 );
    }else{
      d_regions.push_back( new Region( this, d_th->getContext() ) );
    }
    d_regions[ d_regions_index ]->setRep( n, true );
    d_regions_index = d_regions_index + 1;
    d_reps = d_reps + 1;
  }
}

/** merge */
void StrongSolverTheoryUf::ConflictFind::merge( Node a, Node b ){
  Debug("uf-ss") << "StrongSolverTheoryUf: Merging " << a << " = " << b << "..." << std::endl;
  Assert( d_regions_map.find( a )!=d_regions_map.end() );
  Assert( d_regions_map.find( b )!=d_regions_map.end() );
  int ai = d_regions_map[a];
  int bi = d_regions_map[b];
  if( ai!=bi ){
    if( d_regions[ai]->getNumReps()==1 ){
      combineRegions( bi, ai );
      d_regions[bi]->setEqual( a, b );
      checkCombine( bi );
    }else if( d_regions[bi]->getNumReps()==1 ){
      combineRegions( ai, bi );
      d_regions[ai]->setEqual( a, b );
      checkCombine( ai );
    }else{
      // either move a to d_regions[bi], or b to d_regions[ai]
      int aex = d_regions[ai]->d_nodes[a]->getNumInternalDisequalities() - getNumDisequalitiesToRegion( a, bi );
      int bex = d_regions[bi]->d_nodes[b]->getNumInternalDisequalities() - getNumDisequalitiesToRegion( b, ai );
      //based on which would produce the fewest number of external disequalities
      if( aex<bex ){
        moveNode( a, bi );
        d_regions[bi]->setEqual( a, b );
      }else{
        moveNode( b, ai );
        d_regions[ai]->setEqual( a, b );
      }
      checkCombine( ai );
      checkCombine( bi );
    }
  }else{
    d_regions[ai]->setEqual( a, b );
    checkCombine( ai );
  }
  d_reps = d_reps - 1;
}

/** unmerge */
void StrongSolverTheoryUf::ConflictFind::undoMerge( Node a, Node b ){

}

/** assert terms are disequal */
void StrongSolverTheoryUf::ConflictFind::assertDisequal( Node a, Node b, Node reason ){
  //if they are not already disequal
  if( !d_th->d_equalityEngine.areDisequal( a, b ) ){
    Debug("uf-ss") << "Assert disequal " << a << " != " << b << "..." << std::endl;
    //add to list of disequalities
    if( d_disequalities_index<d_disequalities.size() ){
      d_disequalities[d_disequalities_index] = reason;
    }else{
      d_disequalities.push_back( reason );
    }
    d_disequalities_index = d_disequalities_index + 1;
    //now, add disequalities to regions
    Node ar = d_th->d_equalityEngine.getRepresentative( a );
    Node br = d_th->d_equalityEngine.getRepresentative( b );
    Debug("uf-ss") << "   representatives: " << ar << ", " << br << std::endl;
    Assert( d_regions_map.find( ar )!=d_regions_map.end() );
    Assert( d_regions_map.find( br )!=d_regions_map.end() );
    int ai = d_regions_map[ar];
    int bi = d_regions_map[br];
    if( ai==bi ){
      //internal disequality
      d_regions[ai]->setDisequal( ar, br, 1, true );
      d_regions[ai]->setDisequal( br, ar, 1, true );
    }else{
      //external disequality
      d_regions[ai]->setDisequal( ar, br, 0, true );
      d_regions[bi]->setDisequal( br, ar, 0, true );
      checkCombine( ai );
      checkCombine( bi );
    }
  }
}

bool StrongSolverTheoryUf::ConflictFind::checkCombine( int ri, bool rec ){
  if( isValid(ri) ){
    //check if this region must merge with another
    if( d_regions[ri]->getMustCombine( d_cardinality ) ){
      Debug("uf-ss") << "We must combine Region #" << ri << ". " << std::endl;
      //debugPrint("uf-ss");
      ////alternatively, check if we can reduce the number of external disequalities by moving single nodes
      //for( std::map< Node, bool >::iterator it = d_regions[i]->d_reps.begin(); it != d_regions[i]->d_reps.end(); ++it ){
      //  if( it->second ){
      //    int inDeg = d_regions[i]->d_disequalities_size[1][ it-> first ];
      //    int outDeg = d_regions[i]->d_disequalities_size[1][ it-> first ];
      //    if( inDeg<outDeg ){
      //    }
      //  }
      //}
      //take region with maximum disequality density
      double maxScore = 0;
      int maxRegion = -1;
      std::map< int, int > regions_diseq;
      getDisequalitiesToRegions( ri, regions_diseq );
      for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
        Assert( it->first!=ri );
        Assert( isValid( it->first ) );
        Assert( d_regions[ it->first ]->getNumReps()>0 );
        double tempScore = double(it->second)/double(d_regions[it->first]->getNumReps() );
        if( tempScore>maxScore ){
          maxRegion = it->first;
          maxScore = tempScore;
        }
      }
      Assert( maxRegion!=-1 );
      combineRegions( ri, maxRegion );
      if( rec ){
        checkCombine( ri, rec );
      }
      return true;
    }
  }
  return false;
}

/** check */
void StrongSolverTheoryUf::ConflictFind::check( Theory::Effort level, OutputChannel* out ){
  Debug("uf-ss") << "StrongSolverTheoryUf: Check " << level << std::endl;
  if( level>=Theory::STANDARD ){
    bool finished = false;
    while( !finished ){
      finished = true;
      if( d_reps<=d_cardinality ){
        Debug("uf-ss") << "We have " << d_reps << " representatives, <= " << d_cardinality << std::endl;
        return;
      }else{
        //do a check within each region
        for( int i=0; i<(int)d_regions_index; i++ ){
          if( d_regions[i]->d_valid ){
            std::vector< Node > clique;
            if( d_regions[i]->check( level, d_cardinality, clique ) ){
              //found a clique
              debugPrint("uf-ss-debug");
              Debug("uf-ss") << "Found a clique in Region #" << i << ":" << std::endl;
              Debug("uf-ss") << "   ";
              for( int i=0; i<(int)clique.size(); i++ ){
                Debug("uf-ss") << clique[i] << " ";
              }
              Debug("uf-ss") << std::endl;
              //explain clique
              explainClique( clique, out );
              return;
            }else{
              Debug("uf-ss") << "No clique in Region #" << i << std::endl;
            }
          }
        }
        if( level==Theory::FULL_EFFORT ){
          //see if we have any recommended splits
          bool addedLemma = false;
          for( int i=0; i<(int)d_regions_index; i++ ){
            if( d_regions[i]->d_valid ){
              if( d_regions[i]->hasSplits() ){
                Node s = d_regions[i]->getBestSplit();
                d_regions[i]->debugPrint("uf-ss-temp", true );
                //add lemma to output channel
                Assert( s!=Node::null() && s.getKind()==EQUAL );
                s = Rewriter::rewrite( s );
                Debug("uf-ss-lemma") << "*** Split on " << s << std::endl;
                //split on the equality s
                out->split( s );
                //tell the sat solver to explore the equals branch first
                out->requirePhase( s, true );
                addedLemma = true;
              }
            }
          }
          if( !addedLemma ){
            //otherwise, we must consider merging regions
            //finished = false;
          }
        }
      }
    }
  }
}

void StrongSolverTheoryUf::ConflictFind::debugPrint( const char* c ){
  Debug( c ) << "--  Conflict Find:" << std::endl;
  Debug( c ) << "Number of reps = " << d_reps << std::endl;
  Debug( c ) << "Cardinality req = " << d_cardinality << std::endl;
  int debugReps = 0;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->d_valid ){
      Debug( c ) << "Region #" << i << ": " << std::endl;
      Debug( c ) << std::endl;
      d_regions[i]->debugPrint( c, true );
      Debug( c ) << std::endl;
      for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[i]->d_nodes.begin(); it != d_regions[i]->d_nodes.end(); ++it ){
        if( it->second->d_valid ){
          if( d_regions_map[ it->first ]!=i ){
            Debug( c ) << "***Bad regions map : " << it->first << " " << d_regions_map[ it->first ].get() << std::endl;
          }
        }
      }
      debugReps += d_regions[i]->getNumReps();
    }
  }
  if( debugReps!=d_reps ){
    Debug( c ) << "***Bad reps: " << d_reps << ", actual = " << debugReps << std::endl;
  }
}

StrongSolverTheoryUf::StrongSolverTheoryUf(context::Context* c, TheoryUF* th) :
d_th( th )
{

}

/** new node */
void StrongSolverTheoryUf::newEqClass( Node n ){
  TypeNode tn = n.getType();
  //TEMPORARY 
  if( tn!=NodeManager::currentNM()->booleanType() ){
    setCardinality( tn, 2 );
  }
  //END_TEMPORARY
  Debug("uf-ss-solver") << "StrongSolverTheoryUf: New eq class " << n << " " << tn << std::endl;
  if( d_conf_find.find( tn )!=d_conf_find.end() ){
    d_conf_find[tn]->newEqClass( n );
  }
}

/** merge */
void StrongSolverTheoryUf::merge( Node a, Node b ){
  TypeNode tn = a.getType();
  Debug("uf-ss-solver") << "StrongSolverTheoryUf: Merge " << a << " " << b << " " << tn << std::endl;
  if( d_conf_find.find( tn )!=d_conf_find.end() ){
    d_conf_find[tn]->merge( a, b );
  }
}

/** unmerge */
void StrongSolverTheoryUf::undoMerge( Node a, Node b ){
  TypeNode tn = a.getType();
  Debug("uf-ss-solver") << "StrongSolverTheoryUf: Undo merge " << a << " " << b << " " << tn << std::endl;
  if( d_conf_find.find( tn )!=d_conf_find.end() ){
    d_conf_find[tn]->undoMerge( a, b );
  }
}

/** assert terms are disequal */
void StrongSolverTheoryUf::assertDisequal( Node a, Node b, Node reason ){
  TypeNode tn = a.getType();
  Debug("uf-ss-solver") << "StrongSolverTheoryUf: Assert disequal " << a << " " << b << " " << tn << std::endl;
  if( d_conf_find.find( tn )!=d_conf_find.end() ){
    d_conf_find[tn]->assertDisequal( a, b, reason );
  }
}

/** check */
void StrongSolverTheoryUf::check( Theory::Effort level, OutputChannel* out ){
  Debug("uf-ss-solver") << "StrongSolverTheoryUf: check " << level << std::endl;
  if( level==Theory::FULL_EFFORT ){
    debugPrint( "uf-ss-debug" );
  }
  for( std::map< TypeNode, ConflictFind* >::iterator it = d_conf_find.begin(); it != d_conf_find.end(); ++it ){
    it->second->check( level, out );
  }
}

/** set cardinality for sort */
void StrongSolverTheoryUf::setCardinality( TypeNode t, int c ) { 
  Debug("uf-ss-solver") << "StrongSolverTheoryUf: Set cardinality " << t << " = " << c << std::endl;
  if( d_conf_find.find( t )==d_conf_find.end() ){
    d_conf_find[t] = new ConflictFind( d_th->getContext(), d_th );
  }
  d_conf_find[t]->d_cardinality = c; 
}

/** get cardinality for sort */
int StrongSolverTheoryUf::getCardinality( TypeNode t ) { 
  return d_conf_find.find( t )!=d_conf_find.end() ? d_conf_find[t]->d_cardinality : -1; 
}

//print debug
void StrongSolverTheoryUf::debugPrint( const char* c ){
  //EqClassesIterator< TheoryUF::NotifyClass > eqc_iter( &((TheoryUF*)d_th)->d_equalityEngine );
  //while( !eqc_iter.isFinished() ){
  //  Debug( c ) << "Eq class [[" << (*eqc_iter) << "]]" << std::endl;
  //  EqClassIterator< TheoryUF::NotifyClass > eqc_iter2( *eqc_iter, &((TheoryUF*)d_th)->d_equalityEngine );
  //  Debug( c ) << "   ";
  //  while( !eqc_iter2.isFinished() ){
  //    Debug( c ) << "[" << (*eqc_iter2) << "] ";
  //    eqc_iter2++;
  //  }
  //  Debug( c ) << std::endl;
  //  eqc_iter++;
  //}

  for( std::map< TypeNode, ConflictFind* >::iterator it = d_conf_find.begin(); it != d_conf_find.end(); ++it ){
    Debug( c ) << "Conflict find structure for " << it->first << ": " << std::endl;
    it->second->debugPrint( c );
    Debug( c ) << std::endl;
  }
}
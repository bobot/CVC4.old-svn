/*********************                                                        */
/*! \file theory_uf_strong_solver.cpp
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
 ** \brief Implementation of theory uf strong solver class
 **/

#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/term_database.h"

//#define USE_SMART_SPLITS
//#define ONE_SPLIT_REGION
//#define DISABLE_QUICK_CLIQUE_CHECKS
//#define COMBINE_REGIONS_SMALL_INTO_LARGE

//#define UF_SS_TOTALITY

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

void StrongSolverTheoryUf::SortRepModel::Region::addRep( Node n ) {
  setRep( n, true );
}

void StrongSolverTheoryUf::SortRepModel::Region::takeNode( StrongSolverTheoryUf::SortRepModel::Region* r, Node n ){
  //Debug("uf-ss") << "takeNode " << r << " " << n << std::endl;
  //Debug("uf-ss") << "r : " << std::endl;
  //r->debugPrint("uf-ss");
  //Debug("uf-ss") << "this : " << std::endl;
  //debugPrint("uf-ss");
  Assert( !hasRep( n ) );
  Assert( r->hasRep( n ) );
  //add representative
  setRep( n, true );
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
  //remove representative
  r->setRep( n, false );
}

void StrongSolverTheoryUf::SortRepModel::Region::combine( StrongSolverTheoryUf::SortRepModel::Region* r ){
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

/** setEqual */
void StrongSolverTheoryUf::SortRepModel::Region::setEqual( Node a, Node b ){
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

void StrongSolverTheoryUf::SortRepModel::Region::setDisequal( Node n1, Node n2, int type, bool valid ){
  //Debug("uf-ss-region-debug") << "set disequal " << n1 << " " << n2 << " " << type << " " << valid << std::endl;
  //debugPrint("uf-ss-region-debug");
  //Assert( isDisequal( n1, n2, type )!=valid );
  if( isDisequal( n1, n2, type )!=valid ){    //DO_THIS: make assertion
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
}

void StrongSolverTheoryUf::SortRepModel::Region::setRep( Node n, bool valid ){
  Assert( hasRep( n )!=valid );
  if( valid && d_nodes.find( n )==d_nodes.end() ){
    d_nodes[n] = new RegionNodeInfo( d_cf->d_th->getSatContext() );
  }
  d_nodes[n]->d_valid = valid;
  d_reps_size = d_reps_size + ( valid ? 1 : -1 );
  //removing a member of the test clique from this region
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

bool StrongSolverTheoryUf::SortRepModel::Region::isDisequal( Node n1, Node n2, int type ){
  RegionNodeInfo::DiseqList* del = d_nodes[ n1 ]->d_disequalities[type];
  return del->d_disequalities.find( n2 )!=del->d_disequalities.end() && del->d_disequalities[n2];
}

struct sortInternalDegree {
  StrongSolverTheoryUf::SortRepModel::Region* r;
  bool operator() (Node i,Node j) { return (r->d_nodes[i]->getNumInternalDisequalities()>r->d_nodes[j]->getNumInternalDisequalities());}
};

struct sortExternalDegree {
  StrongSolverTheoryUf::SortRepModel::Region* r;
  bool operator() (Node i,Node j) { return (r->d_nodes[i]->getNumExternalDisequalities()>r->d_nodes[j]->getNumExternalDisequalities());}
};

bool StrongSolverTheoryUf::SortRepModel::Region::getMustCombine( int cardinality ){
  if( options::ufssRegions() && d_total_diseq_external>=long(cardinality) ){
    //The number of external disequalities is greater than or equal to cardinality.
    //Thus, a clique of size cardinality+1 may exist between nodes in d_regions[i] and other regions
    //Check if this is actually the case:  must have n nodes with outgoing degree (cardinality+1-n) for some n>0
    std::vector< int > degrees;
    for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
      RegionNodeInfo* rni = it->second;
      if( rni->d_valid ){
        if( rni->getNumDisequalities()>=cardinality ){
          int outDeg = rni->getNumExternalDisequalities();
          if( outDeg>=cardinality ){
            //we have 1 node of degree greater than (cardinality)
            return true;
          }else if( outDeg>=1 ){
            degrees.push_back( outDeg );
            if( (int)degrees.size()>=cardinality ){
              //we have (cardinality) nodes of degree 1
              return true;
            }
          }
        }
      }
    }
    //static int gmcCount = 0;
    //gmcCount++;
    //if( gmcCount%100==0 ){
    //  std::cout << gmcCount << " " << cardinality << std::endl;
    //}
    //this should happen relatively infrequently....
    std::sort( degrees.begin(), degrees.end() );
    for( int i=0; i<(int)degrees.size(); i++ ){
      if( degrees[i]>=cardinality+1-((int)degrees.size()-i) ){
        return true;
      }
    }
  }
  return false;
}

bool StrongSolverTheoryUf::SortRepModel::Region::check( Theory::Effort level, int cardinality, std::vector< Node >& clique ){
  if( d_reps_size>long(cardinality) ){
    if( d_total_diseq_internal==d_reps_size*( d_reps_size - 1 ) ){
      //quick clique check, all reps form a clique
      for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
        if( it->second->d_valid ){
          clique.push_back( it->first );
        }
      }
      return true;
    }else if( options::ufssRegions() || options::ufssEagerSplits() || level==Theory::EFFORT_FULL ){
      //build test clique, up to size cardinality+1
      if( d_testCliqueSize<=long(cardinality) ){
        std::vector< Node > newClique;
        if( d_testCliqueSize<long(cardinality) ){
          for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
            //if not in the test clique, add it to the set of new members
            if( it->second->d_valid && ( d_testClique.find( it->first )==d_testClique.end() || !d_testClique[ it->first ] ) ){
              //if( it->second->getNumInternalDisequalities()>cardinality || level==Theory::EFFORT_FULL ){
              newClique.push_back( it->first );
              //}
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
      //check if test clique has larger size than cardinality, and forms a clique
      if( d_testCliqueSize>=long(cardinality+1) && d_splitsSize==0 ){
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

void StrongSolverTheoryUf::SortRepModel::Region::getRepresentatives( std::vector< Node >& reps ){
  for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      reps.push_back( it->first );
    }
  }
}

void StrongSolverTheoryUf::SortRepModel::Region::getNumExternalDisequalities( std::map< Node, int >& num_ext_disequalities ){
  for( std::map< Node, RegionNodeInfo* >::iterator it = d_nodes.begin(); it != d_nodes.end(); ++it ){
    RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      RegionNodeInfo::DiseqList* del = rni->d_disequalities[0];
      for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
        if( (*it2).second ){
          num_ext_disequalities[ (*it2).first ]++;
        }
      }
    }
  }
}

Node StrongSolverTheoryUf::SortRepModel::Region::getBestSplit(){
#ifndef USE_SMART_SPLITS
  //take the first split you find
  for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
    if( (*it).second ){
      return (*it).first;
    }
  }
  return Node::null();
#else
  std::vector< Node > splits;
  for( NodeBoolMap::iterator it = d_splits.begin(); it != d_splits.end(); ++it ){
    if( (*it).second ){
      splits.push_back( (*it).first );
    }
  }
  if( splits.size()>1 ){
    std::map< Node, std::map< Node, bool > > ops;
    Debug("uf-ss-split") << "Choice for splits: " << std::endl;
    double maxScore = -1;
    int maxIndex;
    for( int i=0; i<(int)splits.size(); i++ ){
      Debug("uf-ss-split") << "   " << splits[i] << std::endl;
      for( int j=0; j<2; j++ ){
        if( ops.find( splits[i][j] )==ops.end() ){
          EqClassIterator eqc( splits[i][j], ((uf::TheoryUF*)d_cf->d_th)->getEqualityEngine() );
          while( !eqc.isFinished() ){
            Node n = (*eqc);
            if( n.getKind()==APPLY_UF ){
              ops[ splits[i][j] ][ n.getOperator() ] = true;
            }
            ++eqc;
          }
        }
      }
      //now, compute score
      int common[2] = { 0, 0 };
      for( int j=0; j<2; j++ ){
        int j2 = j==0 ? 1 : 0;
        for( std::map< Node, bool >::iterator it = ops[ splits[i][j] ].begin(); it != ops[ splits[i][j] ].end(); ++it ){
          if( ops[ splits[i][j2] ].find( it->first )!=ops[ splits[i][j2] ].end() ){
            common[0]++;
          }else{
            common[1]++;
          }
        }
      }
      double score = ( 1.0 + (double)common[0] )/( 1.0 + (double)common[1] );
      if( score>maxScore ){
        maxScore = score;
        maxIndex = i;
      }
    }
    //if( maxIndex!=0 ){
    //  std::cout << "Chose maxIndex = " << maxIndex << std::endl;
    //}
    return splits[maxIndex];
  }else if( !splits.empty() ){
    return splits[0];
  }else{
    return Node::null();
  }
#endif
}

void StrongSolverTheoryUf::SortRepModel::Region::debugPrint( const char* c, bool incClique ){
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








StrongSolverTheoryUf::SortRepModel::SortRepModel( Node n, context::Context* c, TheoryUF* th ) : RepModel( n.getType() ),
          d_th( th ), d_regions_index( c, 0 ), d_regions_map( c ), d_disequalities_index( c, 0 ),
          d_reps( c, 0 ), d_cardinality( c, 1 ), d_aloc_cardinality( 0 ),
          d_cardinality_assertions( c ), d_hasCard( c, false ){
#ifndef UF_SS_TOTALITY
  d_cardinality_term.push_back( n );
#endif
}

/** initialize */
void StrongSolverTheoryUf::SortRepModel::initialize( OutputChannel* out ){
  allocateCardinality( out );
}

/** new node */
void StrongSolverTheoryUf::SortRepModel::newEqClass( Node n ){
  if( d_regions_map.find( n )==d_regions_map.end() ){
    if( !options::ufssRegions() ){
      //if not using regions, always add new equivalence classes to region index = 0
      d_regions_index = 0;
    }
    d_regions_map[n] = d_regions_index;
#ifdef UF_SS_TOTALITY
    //must generate totality axioms for every cardinality we have allocated thus far
    for( std::map< int, Node >::iterator it = d_cardinality_literal.begin(); it != d_cardinality_literal.end(); ++it ){
      addTotalityAxiom( n, it->first, &d_th->getOutputChannel() );
    }
#else
    Debug("uf-ss") << "StrongSolverTheoryUf: New Eq Class " << n << std::endl;
    Debug("uf-ss-debug") << d_regions_index << " " << (int)d_regions.size() << std::endl;
    if( d_regions_index<d_regions.size() ){
      d_regions[ d_regions_index ]->debugPrint("uf-ss-debug",true);
      d_regions[ d_regions_index ]->d_valid = true;
      Assert( !options::ufssRegions() || d_regions[ d_regions_index ]->getNumReps()==0 );
    }else{
      d_regions.push_back( new Region( this, d_th->getSatContext() ) );
    }
    d_regions[ d_regions_index ]->addRep( n );
    d_regions_index = d_regions_index + 1;
    d_reps = d_reps + 1;
#endif
  }
}

/** merge */
void StrongSolverTheoryUf::SortRepModel::merge( Node a, Node b ){
#ifndef UF_SS_TOTALITY
  //Assert( a==d_th->d_equalityEngine.getRepresentative( a ) );
  //Assert( b==d_th->d_equalityEngine.getRepresentative( b ) );
  Debug("uf-ss") << "StrongSolverTheoryUf: Merging " << a << " = " << b << "..." << std::endl;
  if( a!=b ){
    Assert( d_regions_map.find( a )!=d_regions_map.end() );
    Assert( d_regions_map.find( b )!=d_regions_map.end() );
    int ai = d_regions_map[a];
    int bi = d_regions_map[b];
    Debug("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
    if( ai!=bi ){
      if( d_regions[ai]->getNumReps()==1  ){
        int ri = combineRegions( bi, ai );
        d_regions[ri]->setEqual( a, b );
        checkRegion( ri );
      }else if( d_regions[bi]->getNumReps()==1 ){
        int ri = combineRegions( ai, bi );
        d_regions[ri]->setEqual( a, b );
        checkRegion( ri );
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
        checkRegion( ai );
        checkRegion( bi );
      }
    }else{
      d_regions[ai]->setEqual( a, b );
      checkRegion( ai );
    }
    d_reps = d_reps - 1;
    d_regions_map[b] = -1;
  }
  Debug("uf-ss") << "Done merge." << std::endl;
#endif
}

/** assert terms are disequal */
void StrongSolverTheoryUf::SortRepModel::assertDisequal( Node a, Node b, Node reason ){
#ifndef UF_SS_TOTALITY
  //if they are not already disequal
  a = d_th->d_equalityEngine.getRepresentative( a );
  b = d_th->d_equalityEngine.getRepresentative( b );
  if( !d_th->d_equalityEngine.areDisequal( a, b, true ) ){
    Debug("uf-ss") << "Assert disequal " << a << " != " << b << "..." << std::endl;
    //if( reason.getKind()!=NOT || ( reason[0].getKind()!=EQUAL && reason[0].getKind()!=IFF ) ||
    //    a!=reason[0][0] || b!=reason[0][1] ){
    //  Notice() << "Assert disequal " << a << " != " << b << ", reason = " << reason << "..." << std::endl;
    //}
    Debug("uf-ss-disequal") << "Assert disequal " << a << " != " << b << "..." << std::endl;
    //add to list of disequalities
    if( d_disequalities_index<d_disequalities.size() ){
      d_disequalities[d_disequalities_index] = reason;
    }else{
      d_disequalities.push_back( reason );
    }
    d_disequalities_index = d_disequalities_index + 1;
    //now, add disequalities to regions
    Assert( d_regions_map.find( a )!=d_regions_map.end() );
    Assert( d_regions_map.find( b )!=d_regions_map.end() );
    int ai = d_regions_map[a];
    int bi = d_regions_map[b];
    Debug("uf-ss") << "   regions: " << ai << " " << bi << std::endl;
    if( ai==bi ){
      //internal disequality
      d_regions[ai]->setDisequal( a, b, 1, true );
      d_regions[ai]->setDisequal( b, a, 1, true );
    }else{
      //external disequality
      d_regions[ai]->setDisequal( a, b, 0, true );
      d_regions[bi]->setDisequal( b, a, 0, true );
      checkRegion( ai );
      checkRegion( bi );
    }
    //Notice() << "done" << std::endl;
  }
#endif
}


/** check */
void StrongSolverTheoryUf::SortRepModel::check( Theory::Effort level, OutputChannel* out ){
#ifndef UF_SS_TOTALITY
  if( level>=Theory::EFFORT_STANDARD && d_hasCard ){
    Assert( d_cardinality>0 );
    Debug("uf-ss") << "StrongSolverTheoryUf: Check " << level << " " << d_type << std::endl;
    //Notice() << "StrongSolverTheoryUf: Check " << level << std::endl;
    if( d_reps<=(unsigned)d_cardinality ){
      Debug("uf-ss-debug") << "We have " << d_reps << " representatives for type " << d_type << ", <= " << d_cardinality << std::endl;
      if( level==Theory::EFFORT_FULL ){
        Debug("uf-ss-sat") << "We have " << d_reps << " representatives for type " << d_type << ", <= " << d_cardinality << std::endl;
        //Notice() << "We have " << d_reps << " representatives for type " << d_type << ", <= " << cardinality << std::endl;
        //Notice() << "Model size for " << d_type << " is " << cardinality << std::endl;
        //Notice() << cardinality << " ";
      }
      return;
    }else{
      //do a check within each region
      for( int i=0; i<(int)d_regions_index; i++ ){
        if( d_regions[i]->d_valid ){
          std::vector< Node > clique;
          if( d_regions[i]->check( level, d_cardinality, clique ) ){
            //explain clique
            explainClique( clique, out );
            return;
          }else{
            Debug("uf-ss-debug") << "No clique in Region #" << i << std::endl;
          }
        }
      }
      bool addedLemma = false;
      //do splitting on demand
      if( level==Theory::EFFORT_FULL || options::ufssEagerSplits() ){
        Debug("uf-ss-debug") << "Add splits?" << std::endl;
        //see if we have any recommended splits from large regions
        for( int i=0; i<(int)d_regions_index; i++ ){
          if( d_regions[i]->d_valid && d_regions[i]->getNumReps()>d_cardinality ){
            if( addSplit( d_regions[i], out ) ){
              addedLemma = true;
#ifdef ONE_SPLIT_REGION
              break;
#endif
            }
          }
        }
      }
      //if no added lemmas, force continuation via combination of regions
      if( level==Theory::EFFORT_FULL ){
        if( !addedLemma ){
          Debug("uf-ss") << "No splits added." << std::endl;
          if( !options::ufssColoringSat() ){
            bool recheck = false;
            //naive strategy, force region combination involving the first valid region
            for( int i=0; i<(int)d_regions_index; i++ ){
              if( d_regions[i]->d_valid ){
                forceCombineRegion( i, false );
                recheck = true;
                break;
              }
            }
            if( recheck ){
              check( level, out );
            }
          }
        }
      }
    }
  }
#endif
}

void StrongSolverTheoryUf::SortRepModel::propagate( Theory::Effort level, OutputChannel* out ){
  //propagate the current cardinality as a decision literal, if not already asserted
  //for( int i=1; i<=d_aloc_cardinality; i++ ){
  //  if( !d_hasCard || i<d_cardinality ){
  //    Node cn = d_cardinality_literal[ i ];
  //    Assert( !cn.isNull() );
  //    if( d_cardinality_assertions.find( cn )==d_cardinality_assertions.end() ){
  //      out->propagateAsDecision( cn );
  //      Trace("uf-ss-prop-as-dec") << "Propagate as decision " << cn << " " << d_type << std::endl;
  //      break;
  //    }
  //  }
  //}
}

TNode StrongSolverTheoryUf::SortRepModel::getNextDecisionRequest(){
  //request the current cardinality as a decision literal, if not already asserted
  for( int i=1; i<=d_aloc_cardinality; i++ ){
    if( !d_hasCard || i<d_cardinality ){
      Node cn = d_cardinality_literal[ i ];
      Assert( !cn.isNull() );
      if( d_cardinality_assertions.find( cn )==d_cardinality_assertions.end() ){
        Trace("uf-ss-prop-as-dec") << "Propagate as decision " << d_type << " " << i << std::endl;
        return cn;
      }
    }
  }
  return TNode::null();
}

bool StrongSolverTheoryUf::SortRepModel::minimize( OutputChannel* out, TheoryModel* m ){
#ifndef UF_SS_TOTALITY
  if( m ){
#if 0
    // ensure that the constructed model is minimal
    // if the model has terms that the strong solver does not know about
    if( (int)m->d_rep_set.d_type_reps[ d_type ].size()>d_cardinality ){
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &m->d_equalityEngine );
      while( !eqcs_i.isFinished() ){
        Node eqc = (*eqcs_i);
        if( eqc.getType()==d_type ){
          //we must ensure that this equivalence class has been accounted for
          if( d_regions_map.find( eqc )==d_regions_map.end() ){
            //split on unaccounted for term and cardinality lemma term (as default)
            Node splitEq = eqc.eqNode( d_cardinality_term[0] );
            splitEq = Rewriter::rewrite( splitEq );
            Trace("uf-ss-minimize") << "Last chance minimize : " << splitEq << std::endl;
            out->split( splitEq );
            //tell the sat solver to explore the equals branch first
            out->requirePhase( splitEq, true );
            ++( d_th->getStrongSolver()->d_statistics.d_split_lemmas );
            return false;
          }
        }
        ++eqcs_i;
      }
      Assert( false );
    }
#endif
  }else{
    //internal minimize, ensure that model forms a clique:
    // if two equivalence classes are neither equal nor disequal, add a split
    int validRegionIndex = -1;
    for( int i=0; i<(int)d_regions_index; i++ ){
      if( d_regions[i]->d_valid ){
        if( validRegionIndex!=-1 ){
          combineRegions( validRegionIndex, i );
          if( addSplit( d_regions[validRegionIndex], out ) ){
            return false;
          }
        }else{
          validRegionIndex = i;
        }
      }
    }
    if( addSplit( d_regions[validRegionIndex], out ) ){
      return false;
    }
  }
#endif
  return true;
}


int StrongSolverTheoryUf::SortRepModel::getNumDisequalitiesToRegion( Node n, int ri ){
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

void StrongSolverTheoryUf::SortRepModel::getDisequalitiesToRegions( int ri, std::map< int, int >& regions_diseq ){
  for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[ri]->d_nodes.begin();
       it != d_regions[ri]->d_nodes.end(); ++it ){
    if( it->second->d_valid ){
      Region::RegionNodeInfo::DiseqList* del = it->second->d_disequalities[0];
      for( NodeBoolMap::iterator it2 = del->d_disequalities.begin(); it2 != del->d_disequalities.end(); ++it2 ){
        if( (*it2).second ){
          Assert( isValid( d_regions_map[ (*it2).first ] ) );
          //Notice() << "Found disequality with " << (*it2).first << ", region = " << d_regions_map[ (*it2).first ] << std::endl;
          regions_diseq[ d_regions_map[ (*it2).first ] ]++;
        }
      }
    }
  }
}

void StrongSolverTheoryUf::SortRepModel::explainClique( std::vector< Node >& clique, OutputChannel* out ){
  Assert( d_hasCard );
  Assert( d_cardinality>0 );
  while( clique.size()>size_t(d_cardinality+1) ){
    clique.pop_back();
  }
  //found a clique
  Trace("uf-ss") << "Found a clique (cardinality=" << d_cardinality << ") :" << std::endl;
  Trace("uf-ss") << "   ";
  for( int i=0; i<(int)clique.size(); i++ ){
    Trace("uf-ss") << clique[i] << " ";
  }
  Trace("uf-ss") << std::endl;
  Debug("uf-ss") << "Finding clique disequalities..." << std::endl;
  std::vector< Node > conflict;
  //collect disequalities, and nodes that must be equal within representatives
  std::map< Node, std::map< Node, bool > > explained;
  std::map< Node, std::map< Node, bool > > nodesWithinRep;
  for( int i=0; i<(int)d_disequalities_index; i++ ){
    //if both sides of disequality exist in clique
    Node r1 = d_th->d_equalityEngine.getRepresentative( d_disequalities[i][0][0] );
    Node r2 = d_th->d_equalityEngine.getRepresentative( d_disequalities[i][0][1] );
    if( r1!=r2 && ( explained.find( r1 )==explained.end() || explained[r1].find( r2 )==explained[r1].end() ) &&
        std::find( clique.begin(), clique.end(), r1 )!=clique.end() &&
        std::find( clique.begin(), clique.end(), r2 )!=clique.end() ){
      explained[r1][r2] = true;
      explained[r2][r1] = true;
      conflict.push_back( d_disequalities[i] );
      Trace("uf-ss") << "   -> disequality : " << d_disequalities[i] << std::endl;
      nodesWithinRep[r1][ d_disequalities[i][0][0] ] = true;
      nodesWithinRep[r2][ d_disequalities[i][0][1] ] = true;
      if( conflict.size()==(clique.size()*( clique.size()-1 )/2) ){
        break;
      }
    }
  }
  //Debug("uf-ss") << conflict.size() << " " << clique.size() << std::endl;
  Assert( (int)conflict.size()==((int)clique.size()*( (int)clique.size()-1 )/2) );
  //Assert( (int)conflict.size()==(int)clique.size()*( (int)clique.size()-1 )/2 );
  Debug("uf-ss") << "Finding clique equalities internal to eq classes..." << std::endl;
  //now, we must explain equalities within each equivalence class
  for( std::map< Node, std::map< Node, bool > >::iterator it = nodesWithinRep.begin(); it != nodesWithinRep.end(); ++it ){
    if( it->second.size()>1 ){
      Node prev;
      //add explanation of t1 = t2 = ... = tn
      Trace("uf-ss") << "Explain ";
      for( std::map< Node, bool >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        if( prev!=Node::null() ){
          Trace("uf-ss") << " = ";
          //explain it2->first and prev
          std::vector< TNode > expl;
          d_th->d_equalityEngine.explainEquality( it2->first, prev, true, expl );
          for( int i=0; i<(int)expl.size(); i++ ){
            if( std::find( conflict.begin(), conflict.end(), expl[i] )==conflict.end() ){
              conflict.push_back( expl[i] );
            }
          }
        }
        prev = it2->first;
        Trace("uf-ss") << prev;
      }
      Trace("uf-ss") << std::endl;
    }
  }
  Debug("uf-ss") << "Explanation of clique (size=" << conflict.size() << ") = " << std::endl;
  for( int i=0; i<(int)conflict.size(); i++ ){
    Debug("uf-ss") << conflict[i] << " ";
    //bool value;
    //bool hasValue = d_th->getValuation().hasSatValue( conflict[i], value );
    //Assert( hasValue );
    //Assert( value );
  }
  Debug("uf-ss") << std::endl;
  //now, make the conflict
  Node conflictNode = conflict.size()==1 ? conflict[0] : NodeManager::currentNM()->mkNode( AND, conflict );
  //add cardinality constraint
  Node cardNode = d_cardinality_literal[ d_cardinality ];
  //bool value;
  //bool hasValue = d_th->getValuation().hasSatValue( cardNode, value );
  //Assert( hasValue );
  //Assert( value );
  conflictNode = NodeManager::currentNM()->mkNode( IMPLIES, conflictNode, cardNode.notNode() );
  Trace("uf-ss-lemma") << "*** Add clique conflict " << conflictNode << std::endl;
  //Notice() << "*** Add clique conflict " << conflictNode << std::endl;
  out->lemma( conflictNode );
  ++( d_th->getStrongSolver()->d_statistics.d_clique_lemmas );

  //DO_THIS: ensure that the same clique is not reported???  Check standard effort after assertDisequal can produce same clique.
}

void StrongSolverTheoryUf::SortRepModel::assertCardinality( OutputChannel* out, int c, bool val ){
  Trace("uf-ss-assert") << "Assert cardinality " << d_type << " " << c << " " << val << std::endl;
  Assert( d_cardinality_literal.find( c )!=d_cardinality_literal.end() );
  d_cardinality_assertions[ d_cardinality_literal[c] ] = val;
  if( val ){
    if( !d_hasCard || c<d_cardinality ){
      d_cardinality = c;
    }
    d_hasCard = true;
  }else{
    //see if we need to request a new cardinality
    if( !d_hasCard ){
      bool needsCard = true;
      for( std::map< int, Node >::iterator it = d_cardinality_literal.begin(); it!=d_cardinality_literal.end(); ++it ){
        if( d_cardinality_assertions.find( it->second )==d_cardinality_assertions.end() ){
          needsCard = false;
          break;
        }
      }
      if( needsCard ){
        allocateCardinality( out );
      }
    }
  }
}

void StrongSolverTheoryUf::SortRepModel::checkRegion( int ri, bool rec ){
  if( isValid(ri) && d_hasCard ){
    Assert( d_cardinality>0 );
    //first check if region is in conflict
    std::vector< Node > clique;
    if( d_regions[ri]->check( Theory::EFFORT_STANDARD, d_cardinality, clique ) ){
      //explain clique
      explainClique( clique, &d_th->getOutputChannel() );
    }else if( d_regions[ri]->getMustCombine( d_cardinality ) ){
      ////alternatively, check if we can reduce the number of external disequalities by moving single nodes
      //for( std::map< Node, bool >::iterator it = d_regions[i]->d_reps.begin(); it != d_regions[i]->d_reps.end(); ++it ){
      //  if( it->second ){
      //    int inDeg = d_regions[i]->d_disequalities_size[1][ it-> first ];
      //    int outDeg = d_regions[i]->d_disequalities_size[0][ it-> first ];
      //    if( inDeg<outDeg ){
      //    }
      //  }
      //}
      int riNew = forceCombineRegion( ri, true );
      if( riNew>=0 && rec ){
        checkRegion( riNew, rec );
      }
    }
  }
}

int StrongSolverTheoryUf::SortRepModel::forceCombineRegion( int ri, bool useDensity ){
  if( !useDensity ){
    for( int i=0; i<(int)d_regions_index; i++ ){
      if( ri!=i && d_regions[i]->d_valid ){
        return combineRegions( ri, i );
      }
    }
    return -1;
  }else{
    //this region must merge with another
    Debug("uf-ss-check-region") << "We must combine Region #" << ri << ". " << std::endl;
    d_regions[ri]->debugPrint("uf-ss-check-region");
    //take region with maximum disequality density
    double maxScore = 0;
    int maxRegion = -1;
    std::map< int, int > regions_diseq;
    getDisequalitiesToRegions( ri, regions_diseq );
    for( std::map< int, int >::iterator it = regions_diseq.begin(); it != regions_diseq.end(); ++it ){
      Debug("uf-ss-check-region") << it->first << " : " << it->second << std::endl;
    }
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
    if( maxRegion!=-1 ){
      Debug("uf-ss-check-region") << "Combine with region #" << maxRegion << ":" << std::endl;
      d_regions[maxRegion]->debugPrint("uf-ss-check-region");
      return combineRegions( ri, maxRegion );
    }
    return -1;
  }
}


int StrongSolverTheoryUf::SortRepModel::combineRegions( int ai, int bi ){
#ifdef COMBINE_REGIONS_SMALL_INTO_LARGE
  if( d_regions[ai]->getNumReps()<d_regions[bi]->getNumReps() ){
    return combineRegions( bi, ai );
  }
#endif
  Debug("uf-ss-region") << "uf-ss: Combine Region #" << bi << " with Region #" << ai << std::endl;
  Assert( isValid( ai ) && isValid( bi ) );
  for( std::map< Node, Region::RegionNodeInfo* >::iterator it = d_regions[bi]->d_nodes.begin(); it != d_regions[bi]->d_nodes.end(); ++it ){
    Region::RegionNodeInfo* rni = it->second;
    if( rni->d_valid ){
      d_regions_map[ it->first ] = ai;
    }
  }
  //update regions disequal DO_THIS?
  d_regions[ai]->combine( d_regions[bi] );
  d_regions[bi]->d_valid = false;
  return ai;
}

void StrongSolverTheoryUf::SortRepModel::moveNode( Node n, int ri ){
  Debug("uf-ss-region") << "uf-ss: Move node " << n << " to Region #" << ri << std::endl;
  Assert( isValid( d_regions_map[ n ] ) );
  Assert( isValid( ri ) );
  //move node to region ri
  d_regions[ri]->takeNode( d_regions[ d_regions_map[n] ], n );
  d_regions_map[n] = ri;
}

void StrongSolverTheoryUf::SortRepModel::allocateCardinality( OutputChannel* out ){
  if( d_aloc_cardinality>0 ){
    Trace("uf-ss-fmf") << "No model of size " << d_aloc_cardinality << " exists for type " << d_type << " in this branch" << std::endl;
  }
  d_aloc_cardinality++;

#ifdef UF_SS_TOTALITY
  //must generate new cardinality lemma term
  std::stringstream ss;
  ss << "_c_" << d_aloc_cardinality;
  Node var = NodeManager::currentNM()->mkVar( ss.str(), d_type );
  Trace("mkVar") << "allocateCardinality, mkVar : " << var << " : " << d_type << std::endl;
  //must be distinct from all other cardinality terms
  for( int i=0; i<(int)d_cardinality_term.size(); i++ ){
    Node lem = NodeManager::currentNM()->mkNode( NOT, var.eqNode( d_cardinality_term[i] ) );
    d_th->getOutputChannel().lemma( lem );
  }
  d_cardinality_term.push_back( var );
#endif

  //add splitting lemma for cardinality constraint
  Assert( !d_cardinality_term.empty() );
  Node lem = NodeManager::currentNM()->mkNode( CARDINALITY_CONSTRAINT, d_cardinality_term[0],
                                               NodeManager::currentNM()->mkConst( Rational( d_aloc_cardinality ) ) );
  lem = Rewriter::rewrite(lem);
  d_cardinality_literal[ d_aloc_cardinality ] = lem;
  lem = NodeManager::currentNM()->mkNode( OR, lem, lem.notNode() );
  d_cardinality_lemma[ d_aloc_cardinality ] = lem;
  //add as lemma to output channel
  out->lemma( lem );
  //require phase
  out->requirePhase( d_cardinality_literal[ d_aloc_cardinality ], true );
  //add the appropriate lemma, propagate as decision
  //Trace("uf-ss-prop-as-dec") << "Propagate as decision " << lem[0] << " " << d_type << std::endl;
  //out->propagateAsDecision( lem[0] );
  d_th->getStrongSolver()->d_statistics.d_max_model_size.maxAssign( d_aloc_cardinality );

#ifdef UF_SS_TOTALITY
  //must send totality axioms for each existing term
  for( NodeIntMap::iterator it = d_regions_map.begin(); it != d_regions_map.end(); ++it ){
    addTotalityAxiom( (*it).first, d_aloc_cardinality, &d_th->getOutputChannel() );
  }
#endif
}

bool StrongSolverTheoryUf::SortRepModel::addSplit( Region* r, OutputChannel* out ){
  if( r->hasSplits() ){
    Node s = r->getBestSplit();
    //add lemma to output channel
    Assert( s!=Node::null() && s.getKind()==EQUAL );
    s = Rewriter::rewrite( s );
    Trace("uf-ss-lemma") << "*** Split on " << s << std::endl;
    //Trace("uf-ss-lemma") << d_th->getEqualityEngine()->areEqual( s[0], s[1] ) << " ";
    //Trace("uf-ss-lemma") << d_th->getEqualityEngine()->areDisequal( s[0], s[1] ) << std::endl;
    //Trace("uf-ss-lemma") << s[0].getType() << " " << s[1].getType() << std::endl;
    //Notice() << "*** Split on " << s << std::endl;
    //split on the equality s
    out->split( s );
    //tell the sat solver to explore the equals branch first
    out->requirePhase( s, true );
    ++( d_th->getStrongSolver()->d_statistics.d_split_lemmas );
    return true;
  }else{
    return false;
  }
}

void StrongSolverTheoryUf::SortRepModel::addTotalityAxiom( Node n, int cardinality, OutputChannel* out ){
  Node cardLit = d_cardinality_literal[ cardinality ];
  std::vector< Node > eqs;
  for( int i=0; i<cardinality; i++ ){
    eqs.push_back( n.eqNode( d_cardinality_term[i] ) );
  }
  Node ax = NodeManager::currentNM()->mkNode( OR, eqs );
  Node lem = NodeManager::currentNM()->mkNode( IMPLIES, cardLit, ax );
  Trace("uf-ss-lemma") << "*** Add totality axiom " << lem << std::endl;
  //send as lemma to the output channel
  d_th->getOutputChannel().lemma( lem );
  ++( d_th->getStrongSolver()->d_statistics.d_totality_lemmas );
}

void StrongSolverTheoryUf::SortRepModel::debugPrint( const char* c ){
  Debug( c ) << "--  Conflict Find:" << std::endl;
  Debug( c ) << "Number of reps = " << d_reps << std::endl;
  Debug( c ) << "Cardinality req = " << d_cardinality << std::endl;
  unsigned debugReps = 0;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->d_valid ){
      Debug( c ) << "Region #" << i << ": " << std::endl;
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

void StrongSolverTheoryUf::SortRepModel::debugModel( TheoryModel* m ){
  std::vector< Node > eqcs;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &m->d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    if( eqc.getType()==d_type ){
      if( std::find( eqcs.begin(), eqcs.end(), eqc )==eqcs.end() ){
        eqcs.push_back( eqc );
        //we must ensure that this equivalence class has been accounted for
        if( d_regions_map.find( eqc )==d_regions_map.end() ){
          Trace("uf-ss-warn") << "WARNING : equivalence class " << eqc << " unaccounted for." << std::endl;
          Trace("uf-ss-warn") << "  type : " << d_type << std::endl;
          Trace("uf-ss-warn") << "  kind : " << eqc.getKind() << std::endl;
        }
      }
    }
    ++eqcs_i;
  }
  if( (int)eqcs.size()!=d_cardinality ){
    Trace("uf-ss-warn") << "WARNING : Model does not have same # representatives as cardinality for " << d_type << "." << std::endl;
    Trace("uf-ss-warn") << "  cardinality : " << d_cardinality << std::endl;
    Trace("uf-ss-warn") << "  # reps : " << (int)eqcs.size() << std::endl;
  }
}

int StrongSolverTheoryUf::SortRepModel::getNumRegions(){
  int count = 0;
  for( int i=0; i<(int)d_regions_index; i++ ){
    if( d_regions[i]->d_valid ){
      count++;
    }
  }
  return count;
}

void StrongSolverTheoryUf::SortRepModel::getRepresentatives( std::vector< Node >& reps ){
  if( !options::ufssColoringSat() ){
    bool foundRegion = false;
    for( int i=0; i<(int)d_regions_index; i++ ){
      //should not have multiple regions at this point
      if( foundRegion ){
        Assert( !d_regions[i]->d_valid );
      }
      if( d_regions[i]->d_valid ){
        //this is the only valid region
        d_regions[i]->getRepresentatives( reps );
        foundRegion = true;
      }
    }
  }else{
    Unimplemented("Build representatives for fmf region sat is not implemented");
  }
}


/** initialize */
void StrongSolverTheoryUf::InfRepModel::initialize( OutputChannel* out ){

}

/** new node */
void StrongSolverTheoryUf::InfRepModel::newEqClass( Node n ){
  d_rep[n] = n;
  //d_const_rep[n] = n.getMetaKind()==metakind::CONSTANT;
}

/** merge */
void StrongSolverTheoryUf::InfRepModel::merge( Node a, Node b ){
  //d_rep[b] = false;
  //d_const_rep[a] = d_const_rep[a] || d_const_rep[b];
  Node repb = d_rep[b];
  Assert( !repb.isNull() );
  if( repb.getMetaKind()==metakind::CONSTANT || isBadRepresentative( d_rep[a] ) ){
    d_rep[a] = repb;
  }
  d_rep[b] = Node::null();
}

/** check */
void StrongSolverTheoryUf::InfRepModel::check( Theory::Effort level, OutputChannel* out ){

}

/** minimize */
bool StrongSolverTheoryUf::InfRepModel::minimize( OutputChannel* out ){
#if 0
  bool retVal = true;
#else
  bool retVal = !addSplit( out );
#endif
  if( retVal ){
    std::vector< Node > reps;
    getRepresentatives( reps );
    Trace("uf-ss-fmf") << "Num representatives of type " << d_type << " : " << reps.size() << std::endl;
    /*
    for( int i=0; i<(int)reps.size(); i++ ){
      std::cout << reps[i] << " ";
    }
    std::cout << std::endl;
    for( int i=0; i<(int)reps.size(); i++ ){
      std::cout << reps[i].getMetaKind() << " ";
    }
    std::cout << std::endl;
    for( NodeNodeMap::iterator it = d_rep.begin(); it != d_rep.end(); ++it ){
      Node rep = (*it).second;
      if( !rep.isNull() && !isBadRepresentative( rep ) ){
        for( NodeNodeMap::iterator it2 = d_rep.begin(); it2 != d_rep.end(); ++it2 ){
          Node rep2 = (*it2).second;
          if( !rep2.isNull() && !isBadRepresentative( rep2 ) ){
            if( d_th->getQuantifiersEngine()->getEqualityQuery()->areDisequal( rep, rep2 ) ){
              std::cout << "1 ";
            }else{
              std::cout << "0 ";
            }
          }
        }
        //std::cout << " : " << rep;
        std::cout << std::endl;
      }
    }
    */
  }
  return retVal;
}

/** get representatives */
void StrongSolverTheoryUf::InfRepModel::getRepresentatives( std::vector< Node >& reps ){
  for( NodeNodeMap::iterator it = d_rep.begin(); it != d_rep.end(); ++it ){
    if( !(*it).second.isNull() ){
      reps.push_back( (*it).first );
    }
  }
}

/** add split function */
bool StrongSolverTheoryUf::InfRepModel::addSplit( OutputChannel* out ){
  std::vector< Node > visited;
  for( NodeNodeMap::iterator it = d_rep.begin(); it != d_rep.end(); ++it ){
    Node rep = (*it).second;
    if( !rep.isNull() && !isBadRepresentative( rep ) ){
      bool constRep = rep.getMetaKind()==metakind::CONSTANT;
      for( size_t i=0; i<visited.size(); i++ ){
        if( !constRep || !visited[i].getMetaKind()==metakind::CONSTANT ){
          if( !d_th->getQuantifiersEngine()->getEqualityQuery()->areDisequal( rep, visited[i] ) ){
            //split on these nodes
            Node eq = rep.eqNode( visited[i] );
            Trace("uf-ss-lemma") << "*** Split on " << eq << std::endl;
            eq = Rewriter::rewrite( eq );
            Debug("uf-ss-lemma-debug") << "Rewritten " << eq << std::endl;
            out->split( eq );
            //explore the equals branch first
            out->requirePhase( eq, true );
            ++( d_th->getStrongSolver()->d_statistics.d_split_lemmas );
            return true;
          }
        }
      }
      visited.push_back( rep );
    }
  }
  return false;
}

bool StrongSolverTheoryUf::InfRepModel::isBadRepresentative( Node n ){
  return n.getKind()==kind::PLUS;
}

StrongSolverTheoryUf::StrongSolverTheoryUf(context::Context* c, context::UserContext* u, OutputChannel& out, TheoryUF* th) :
d_out( &out ),
d_th( th ),
d_rep_model(),
d_conf_types(),
d_rep_model_init( c )
{
  if( options::ufssColoringSat() ){
    d_term_amb = new TermDisambiguator( th->getQuantifiersEngine(), c );
  }else{
    d_term_amb = NULL;
  }
}

/** new node */
void StrongSolverTheoryUf::newEqClass( Node n ){
  RepModel* c = getRepModel( n );
  if( c ){
    Debug("uf-ss-solver") << "StrongSolverTheoryUf: New eq class " << n << " : " << n.getType() << std::endl;
    c->newEqClass( n );
  }
}

/** merge */
void StrongSolverTheoryUf::merge( Node a, Node b ){
  RepModel* c = getRepModel( a );
  if( c ){
    Debug("uf-ss-solver") << "StrongSolverTheoryUf: Merge " << a << " " << b << " : " << a.getType() << std::endl;
    c->merge( a, b );
  }
}

/** assert terms are disequal */
void StrongSolverTheoryUf::assertDisequal( Node a, Node b, Node reason ){
  RepModel* c = getRepModel( a );
  if( c ){
    Debug("uf-ss-solver") << "StrongSolverTheoryUf: Assert disequal " << a << " " << b << " : " << a.getType() << std::endl;
    //Assert( d_th->d_equalityEngine.getRepresentative( a )==a );
    //Assert( d_th->d_equalityEngine.getRepresentative( b )==b );
    c->assertDisequal( a, b, reason );
  }
}

/** assert a node */
void StrongSolverTheoryUf::assertNode( Node n, bool isDecision ){
  Debug("uf-ss-assert") << "Assert " << n << " " << isDecision << std::endl;
  if( n.getKind()==CARDINALITY_CONSTRAINT ){
    TypeNode tn = n[0].getType();
    Assert( tn.isSort() );
    Assert( d_rep_model[tn] );
    long nCard = n[1].getConst<Rational>().getNumerator().getLong();
    d_rep_model[tn]->assertCardinality( d_out, nCard, true );
  }else if( n.getKind()==NOT && n[0].getKind()==CARDINALITY_CONSTRAINT ){
    Node nn = n[0];
    TypeNode tn = nn[0].getType();
    Assert( tn.isSort() );
    Assert( d_rep_model[tn] );
    long nCard = nn[1].getConst<Rational>().getNumerator().getLong();
    d_rep_model[tn]->assertCardinality( d_out, nCard, false );
  }else{
    ////FIXME: this is too strict: theory propagations are showing up as isDecision=true, but
    ////       a theory propagation is not a decision.
    if( isDecision ){
      for( std::map< TypeNode, RepModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
        if( !it->second->hasCardinalityAsserted() ){
          Trace("uf-ss-warn") << "WARNING: Assert " << n << " as a decision before cardinality for " << it->first << "." << std::endl;
          //Message() << "Error: constraint asserted before cardinality for " << it->first << std::endl;
          //Unimplemented();
        }
      }
    }
  }
}


/** check */
void StrongSolverTheoryUf::check( Theory::Effort level ){
  Debug("uf-ss-solver") << "StrongSolverTheoryUf: check " << level << std::endl;
  if( level==Theory::EFFORT_FULL ){
    debugPrint( "uf-ss-debug" );
  }
  for( std::map< TypeNode, RepModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    it->second->check( level, d_out );
  }
  //disambiguate terms if necessary
  if( level==Theory::EFFORT_FULL && options::ufssColoringSat() ){
    Assert( d_term_amb!=NULL );
    d_statistics.d_disamb_term_lemmas += d_term_amb->disambiguateTerms( d_out );
  }
  Debug("uf-ss-solver") << "Done StrongSolverTheoryUf: check " << level << std::endl;
}

/** propagate */
void StrongSolverTheoryUf::propagate( Theory::Effort level ){
  //for( std::map< TypeNode, RepModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
  //  it->second->propagate( level, d_out );
  //}
}

/** get next decision request */
TNode StrongSolverTheoryUf::getNextDecisionRequest(){
  for( std::map< TypeNode, RepModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    TNode n = it->second->getNextDecisionRequest();
    if( !n.isNull() ){
      return n;
    }
  }
  return TNode::null();
}

void StrongSolverTheoryUf::preRegisterTerm( TNode n ){
  //shouldn't have to preregister this type (it may be that there are no quantifiers over tn)
  TypeNode tn = n.getType();
  if( d_rep_model.find( tn )==d_rep_model.end() ){
    RepModel* rm = NULL;
    if( tn.isSort() ){
      Debug("uf-ss-register") << "Preregister sort " << tn << "." << std::endl;
      rm  = new SortRepModel( n, d_th->getSatContext(), d_th );
    }else if( tn.isInteger() ){
      //rm = new InfRepModel( tn, d_th->getSatContext(), d_th );
      //rm  = new SortRepModel( tn, d_th->getSatContext(), d_th );
    }else{
      /*
      if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
        Debug("uf-ss-na") << "Error: Cannot perform finite model finding on arithmetic quantifier";
        Debug("uf-ss-na") << " (" << f << ")";
        Debug("uf-ss-na") << std::endl;
        Unimplemented("Cannot perform finite model finding on arithmetic quantifier");
      }else if( tn.isDatatype() ){
        Debug("uf-ss-na") << "Error: Cannot perform finite model finding on datatype quantifier";
        Debug("uf-ss-na") << " (" << f << ")";
        Debug("uf-ss-na") << std::endl;
        Unimplemented("Cannot perform finite model finding on datatype quantifier");
      }
      */
    }
    if( rm ){
      rm->initialize( d_out );
      d_rep_model[tn] = rm;
      d_rep_model_init[tn] = true;
    }
  }
}

void StrongSolverTheoryUf::registerQuantifier( Node f ){
  Debug("uf-ss-register") << "Register quantifier " << f << std::endl;
  //must ensure the quantifier does not quantify over arithmetic
  //for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
  //  TypeNode tn = f[0][i].getType();
  //  preRegisterType( tn, true );
  //}
}


StrongSolverTheoryUf::RepModel* StrongSolverTheoryUf::getRepModel( Node n ){
  TypeNode tn = n.getType();
  std::map< TypeNode, RepModel* >::iterator it = d_rep_model.find( tn );
  //pre-register the type if not done already
  if( it==d_rep_model.end() ){
    preRegisterTerm( n );
    it = d_rep_model.find( tn );
  }
  if( it!=d_rep_model.end() ){
    //initialize the type if necessary
    //if( d_rep_model_init.find( tn )==d_rep_model_init.end() ){
      ////initialize the model
      //it->second->initialize( d_out );
      //d_rep_model_init[tn] = true;
    //}
    return it->second;
  }
  return NULL;
}

void StrongSolverTheoryUf::notifyRestart(){
  Debug("uf-ss-prop-as-dec") << "Restart?" << std::endl;
}

/** get cardinality for sort */
int StrongSolverTheoryUf::getCardinality( Node n ) {
  RepModel* c = getRepModel( n );
  if( c ){
    return c->getCardinality();
  }else{
    return -1;
  }
}

void StrongSolverTheoryUf::getRepresentatives( Node n, std::vector< Node >& reps ){
  RepModel* c = getRepModel( n );
  if( c ){
    c->getRepresentatives( reps );
  }
}

bool StrongSolverTheoryUf::minimize( TheoryModel* m ){
  for( std::map< TypeNode, RepModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    if( !it->second->minimize( d_out, m ) ){
      return false;
    }
  }
  for( std::map< TypeNode, RepModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    Trace("uf-ss-minimize") << "Cardinality( " << it->first << " ) : " << it->second->getCardinality() << std::endl;
  }
  return true;
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

  for( std::map< TypeNode, RepModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
    Debug( c ) << "Conflict find structure for " << it->first << ": " << std::endl;
    it->second->debugPrint( c );
    Debug( c ) << std::endl;
  }
}

void StrongSolverTheoryUf::debugModel( TheoryModel* m ){
  if( Trace.isOn("uf-ss-warn") ){
    for( std::map< TypeNode, RepModel* >::iterator it = d_rep_model.begin(); it != d_rep_model.end(); ++it ){
      it->second->debugModel( m );
    }
  }
}

StrongSolverTheoryUf::Statistics::Statistics():
  d_clique_lemmas("StrongSolverTheoryUf::Clique_Lemmas", 0),
  d_split_lemmas("StrongSolverTheoryUf::Split_Lemmas", 0),
  d_disamb_term_lemmas("StrongSolverTheoryUf::Disambiguate_Term_Lemmas", 0),
  d_totality_lemmas("StrongSolverTheoryUf::Totality_Lemmas", 0),
  d_max_model_size("StrongSolverTheoryUf::Max_Model_Size", 1)
{
  StatisticsRegistry::registerStat(&d_clique_lemmas);
  StatisticsRegistry::registerStat(&d_split_lemmas);
  StatisticsRegistry::registerStat(&d_disamb_term_lemmas);
  StatisticsRegistry::registerStat(&d_totality_lemmas);
  StatisticsRegistry::registerStat(&d_max_model_size);
}

StrongSolverTheoryUf::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_clique_lemmas);
  StatisticsRegistry::unregisterStat(&d_split_lemmas);
  StatisticsRegistry::unregisterStat(&d_disamb_term_lemmas);
  StatisticsRegistry::unregisterStat(&d_totality_lemmas);
  StatisticsRegistry::unregisterStat(&d_max_model_size);
}


int TermDisambiguator::disambiguateTerms( OutputChannel* out ){
  Debug("uf-ss-disamb") << "Disambiguate terms." << std::endl;
  int lemmaAdded = 0;
  //otherwise, determine ambiguous pairs of ground terms for relevant sorts
  quantifiers::TermDb* db = d_qe->getTermDatabase();
  for( std::map< Node, std::vector< Node > >::iterator it = db->d_op_map.begin(); it != db->d_op_map.end(); ++it ){
    Debug("uf-ss-disamb") << "Check " << it->first << std::endl;
    if( it->second.size()>1 ){
      if(involvesRelevantType( it->second[0] ) ){
        for( int i=0; i<(int)it->second.size(); i++ ){
          for( int j=(i+1); j<(int)it->second.size(); j++ ){
            Kind knd = it->second[i].getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
            Node eq = NodeManager::currentNM()->mkNode( knd, it->second[i], it->second[j] );
            eq = Rewriter::rewrite(eq);
            //determine if they are ambiguous
            if( d_term_amb.find( eq )==d_term_amb.end() ){
              Debug("uf-ss-disamb") << "Check disambiguate " << it->second[i] << " " << it->second[j] << std::endl;
              d_term_amb[ eq ] = true;
              //if they are equal
              if( d_qe->getEqualityQuery()->areEqual( it->second[i], it->second[j] ) ){
                d_term_amb[ eq ] = false;
              }else{
                //if an argument is disequal, then they are not ambiguous
                for( int k=0; k<(int)it->second[i].getNumChildren(); k++ ){
                  if( d_qe->getEqualityQuery()->areDisequal( it->second[i][k], it->second[j][k] ) ){
                    d_term_amb[ eq ] = false;
                    break;
                  }
                }
              }
              if( d_term_amb[ eq ] ){
                Debug("uf-ss-disamb") << "Disambiguate " << it->second[i] << " " << it->second[j] << std::endl;
                //must add lemma
                std::vector< Node > children;
                children.push_back( eq );
                for( int k=0; k<(int)it->second[i].getNumChildren(); k++ ){
                  Kind knd2 = it->second[i][k].getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
                  Node eqc = NodeManager::currentNM()->mkNode( knd2, it->second[i][k], it->second[j][k] );
                  children.push_back( eqc.notNode() );
                }
                Assert( children.size()>1 );
                Node lem = NodeManager::currentNM()->mkNode( OR, children );
                Debug( "uf-ss-lemma" ) << "*** Disambiguate lemma : " << lem << std::endl;
                //Notice() << "*** Disambiguate lemma : " << lem << std::endl;
                out->lemma( lem );
                d_term_amb[ eq ] = false;
                lemmaAdded++;
              }
            }
          }
        }
      }
    }
  }
  Debug("uf-ss-disamb") << "Done disambiguate terms. " << lemmaAdded << std::endl;
  return lemmaAdded;
}

bool TermDisambiguator::involvesRelevantType( Node n ){
  if( n.getKind()==APPLY_UF ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n[i].getType().isSort() ){
        return true;
      }
    }
  }
  return false;
}

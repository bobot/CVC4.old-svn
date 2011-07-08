/*********************                                                        */
/*! \file instantiation_engine.cpp
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
 ** \brief Implementation of theory matcher and instantiation engine classes
 **/

#include "theory/instantiation_engine.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

TheoryMatcher::TheoryMatcher(context::Context* c, InstantiationEngine* ie) : 
d_ie( ie ){
}

InstantiationEngine::InstantiationEngine(context::Context* c, TheoryEngine* te):
d_te( te ){
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_matcherTable[theoryId] = NULL;
  }
}

theory::TheoryMatcher* InstantiationEngine::getTheoryMatcher( Theory* t ){
  TheoryId th = t->getId();
  if( !d_matcherTable[th] ){
    //switch( th ){
    //}
  }
  return d_matcherTable[th];
}

void InstantiationEngine::getInstantiationConstantsFor( Node f, std::vector< Node >& vars, 
                                                        std::vector< Node >& ics ){
  Assert( vars.empty() && ics.empty() );
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==EXISTS ) );
  if( d_inst_constants.find( f )==d_inst_constants.end() ){
    Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
    for( int i=0; i<(int)quant.getNumChildren()-1; i++ ){
      vars.push_back( quant[i] );
      Node ic = NodeManager::currentNM()->mkInstConstant( quant[i].getType() );
      d_inst_constants_map[ic] = f;
      ics.push_back( ic );
    }
    d_vars[ f ].insert( d_vars[ f ].begin(), vars.begin(), vars.end() );
    d_inst_constants[ f ].insert( d_inst_constants[ f ].begin(), ics.begin(), ics.end() );
  }else{
    vars.insert( vars.begin(), d_vars[ f ].begin(), d_vars[ f ].end() );
    ics.insert( ics.begin(), d_inst_constants[ f ].begin(), d_inst_constants[ f ].end() );
  }
}

bool InstantiationEngine::getInstantiationFor( Node f, std::vector< Node >& vars, 
                                               std::vector< Node >& terms ){
  Assert( vars.empty() && terms.empty() );
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==EXISTS ) );
 
  getInstantiationConstantsFor( f, vars, terms );

  //get the instantiation table
  std::map< Theory*, std::map< Node, Node > > instMap;
  if( d_inst_map.find( f )==d_inst_map.end() ){
    for( int i=0; i<(int)vars.size(); i++ ){
      Assert( d_te->theoryOf( vars[i] )!=NULL );
      instMap[ d_te->theoryOf( vars[i] ) ][ vars[i] ] = Node::null();
    }
    d_inst_map[f] = instMap;
  }else{
    instMap = d_inst_map[f];
  }

  //request instantiations from theory matchers
  for( std::map< Theory*, std::map< Node, Node > >::iterator it = instMap.begin(); it!=instMap.end(); ++it ){
    if( !getTheoryMatcher( it->first ) || !getTheoryMatcher( it->first )->getInstantiation( it->second ) ){
      return false;
    }
  }

  //construct instantiation
  for( int i=0; i<(int)vars.size(); i++ ){
    terms[i] = instMap[ d_te->theoryOf( vars[i] ) ][ vars[i] ];
  }
  return true;
}

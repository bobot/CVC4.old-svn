/*********************                                                        */
/*! \file instantiator_arith_instantiator.cpp
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
 ** \brief Implementation of instantiator_arith_instantiator class
 **/

#include "theory/arith/theory_arith_instantiator.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

InstantiatorTheoryArith::InstantiatorTheoryArith(context::Context* c, InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie, th ){

}

void InstantiatorTheoryArith::check( Node assertion ){
  Debug("quant-arith") << "Assert " << assertion << std::endl;
}

void InstantiatorTheoryArith::resetInstantiation(){
  //search for instantiation rows in simplex tableaux
  ArithVarToNodeMap avtnm = ((TheoryArith*)getTheory())->d_arithvarNodeMap.getArithVarToNodeMap();
  for( ArithVarToNodeMap::iterator it = avtnm.begin(); it != avtnm.end(); ++it ){
    ArithVar x = (*it).first;
    Node n = (*it).second;

  }

}

bool InstantiatorTheoryArith::doInstantiation( int effort ){
  Debug("quant-arith") << "Search (" << effort << ") for instantiation for Arith: " << std::endl;
  if( effort==0 ){
    printDebug();
  }
  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    if( d_instEngine->getActive( it->first ) ){
      
    }
  }

  d_status = STATUS_UNKNOWN;
  return true;
}

void InstantiatorTheoryArith::printDebug(){
  ArithVarToNodeMap avtnm = ((TheoryArith*)getTheory())->d_arithvarNodeMap.getArithVarToNodeMap();
  for( ArithVarToNodeMap::iterator it = avtnm.begin(); it != avtnm.end(); ++it ){
    ArithVar x = (*it).first;
    Node n = (*it).second;
    Debug("quant-arith") << x << " : " << n << ", bounds = ";
    if( ((TheoryArith*)getTheory())->d_partialModel.hasLowerBound( x ) ){
      Debug("quant-arith") << ((TheoryArith*)getTheory())->d_partialModel.getLowerBound( x );
    }else{
      Debug("quant-arith") << "-infty";
    }
    Debug("quant-arith") << " <= ";
    Debug("quant-arith") << ((TheoryArith*)getTheory())->d_partialModel.getAssignment( x );
    Debug("quant-arith") << " <= ";
    if( ((TheoryArith*)getTheory())->d_partialModel.hasUpperBound( x ) ){
      Debug("quant-arith") << ((TheoryArith*)getTheory())->d_partialModel.getUpperBound( x );
    }else{
      Debug("quant-arith") << "+infty";
    }
    Debug("quant-arith") << std::endl;
  }

  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    Node f = it->first;
    Debug("quant-arith") << f << std::endl;
    Debug("quant-arith") << "   Inst constants:" << std::endl;
    Debug("quant-arith") << "      ";
    for( int i=0; i<(int)it->second.size(); i++ ){
      if( i>0 ){
        Debug("quant-arith") << ", ";
      }
      Debug("quant-arith") << it->second[i];
    }
    Debug("quant-arith") << std::endl;
  }
}
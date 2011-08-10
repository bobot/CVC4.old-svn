/*********************                                                        */
/*! \file instantiator_default.cpp
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
 ** \brief Implementation of instantiator_default class
 **/

#include "theory/instantiator_default.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

InstantiatorDefault::InstantiatorDefault(context::Context* c, InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie ),
d_th( th ){

}

void InstantiatorDefault::check( Node assertion ){

}

bool InstantiatorDefault::prepareInstantiation(){
  for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); 
      it !=d_inst_constants.end(); ++it ){
    for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
      Node val = d_th->getValue( *it2 );
      Debug("quant-default") << "Default Instantiate for " << d_th->getId() << ", setting " << *it2 << " = " << val << std::endl;
      d_solved_ic[ *it2 ] = val;
    }
  }
  return true;
}
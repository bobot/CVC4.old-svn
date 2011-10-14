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
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

InstantiatorDefault::InstantiatorDefault(context::Context* c, InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie, th ){

}

void InstantiatorDefault::check( Node assertion ){

}

void InstantiatorDefault::process( Node f, int effort ){
  if( effort>4 ){
    d_quantStatus = STATUS_UNKNOWN;
  }else if( effort==4 ){
    Debug("quant-default") << "Process " << f << " : " << std::endl;
    InstMatch m( f, d_instEngine );
    for( std::vector< Node >::iterator it2 = d_instEngine->d_inst_constants[f].begin(); 
         it2!=d_instEngine->d_inst_constants[f].end(); ++it2 ){
      Debug("quant-default") << "Getting value for " << *it2 << std::endl;
      if( d_instEngine->getTheoryEngine()->theoryOf( *it2 )==getTheory() ){    //if it belongs to this theory
        Node val = d_th->getValue( *it2 );
        Debug("quant-default") << "Default Instantiate for " << d_th->getId() << ", setting " << *it2 << " = " << val << std::endl;
        m.setMatch( *it2, val );
      }
    }
    d_instEngine->addPartialInstantiation( m, this );
  }
}

/*********************                                                        */
/*! \file theory_quantifiers_instantiator.cpp
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
 ** \brief Implementation of theory_quantifiers_instantiator class
 **/

#include "theory/quantifiers/theory_quantifiers_instantiator.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

InstantiatorTheoryQuantifiers::InstantiatorTheoryQuantifiers(context::Context* c, QuantifiersEngine* ie, Theory* th) :
Instantiator( c, ie, th ){

}

void InstantiatorTheoryQuantifiers::assertNode( Node assertion ){
  Debug("quant-quant-assert") << "InstantiatorTheoryQuantifiers::check: " << assertion << std::endl;
  if( assertion.hasAttribute(InstConstantAttribute()) ){
    setHasConstraintsFrom( assertion.getAttribute(InstConstantAttribute()) );
  }
}

void InstantiatorTheoryQuantifiers::resetInstantiationRound(){

}


int InstantiatorTheoryQuantifiers::process( Node f, int effort ){
  Debug("quant-quant") << "Quant: Try to solve (" << effort << ") for " << f << "... " << std::endl;
  if( effort<5 ){
    return InstStrategy::STATUS_UNFINISHED;
  }else if( effort==5 ){
    //add random addition
    if( isOwnerOf( f ) ){
      InstMatch m;
      if( d_quantEngine->addInstantiation( f, &m ) ){
        ++(d_statistics.d_instantiations);
      }
    }
  }
  return InstStrategy::STATUS_UNKNOWN;
}

InstantiatorTheoryQuantifiers::Statistics::Statistics():
  d_instantiations("InstantiatorTheoryQuantifiers::Total Instantiations", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
}

InstantiatorTheoryQuantifiers::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
}


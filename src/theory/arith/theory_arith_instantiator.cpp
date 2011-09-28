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
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

InstantiatorTheoryArith::InstantiatorTheoryArith(context::Context* c, InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie ),
d_th( th ){

}

void InstantiatorTheoryArith::check( Node assertion ){

}

void InstantiatorTheoryArith::resetInstantiation(){

}

bool InstantiatorTheoryArith::doInstantiation( int effort ){
  d_status = STATUS_UNKNOWN;
  return true;
}

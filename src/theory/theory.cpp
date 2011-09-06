/*********************                                                        */
/*! \file theory.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base for theory interface.
 **
 ** Base for theory interface.
 **/

#include "theory/theory.h"
#include "util/Assert.h"
#include "theory/instantiation_engine.h"
#include "theory/instantiator_default.h"

#include <vector>

using namespace std;

namespace CVC4 {
namespace theory {

/** Default value for the uninterpreted sorts is the UF theory */
TheoryId Theory::d_uninterpretedSortOwner = THEORY_UF;

std::ostream& operator<<(std::ostream& os, Theory::Effort level){
  switch(level){
  case Theory::MIN_EFFORT:
    os << "MIN_EFFORT"; break;
  case Theory::QUICK_CHECK:
    os << "QUICK_CHECK"; break;
  case Theory::STANDARD:
    os << "STANDARD"; break;
  case Theory::FULL_EFFORT:
    os << "FULL_EFFORT"; break;
  default:
      Unreachable();
  }
  return os;
}/* ostream& operator<<(ostream&, Theory::Effort) */

Instantiator* Theory::makeInstantiator(){
  return new InstantiatorDefault( d_context, d_instEngine, this );
}

Instantiator* Theory::getInstantiator(){
  return d_instEngine ? d_instEngine->getInstantiator( this ) : NULL;
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

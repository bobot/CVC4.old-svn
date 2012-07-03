/*********************                                                        */
/*! \file model.cpp
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
 ** \brief Implementation of model class
 **/

#include "theory/model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

/** add equality */
void Model::addEquality( Node a, Node b ){
  d_equalityEngine.assertEquality( a, b, Node::null() );
}

/** add predicate */
void Model::addPredicate( Node a, bool polarity ){
  d_equalityEngine.assertPrediate( a, polarity, Node::null() );
}

/** add equality engine */
void Model::addEqualityEngine( eq::EqualityEngine& ee ){
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    eq::EqClassIterator eqc_i = eq::EqClassesIterator( eqc, &ee );
    while( !eqc_i.isFinished() ){
      addEquality( *eqc_i, eqc );
      ++eqc_i;
    }
    ++eqcs_i;
  }
}

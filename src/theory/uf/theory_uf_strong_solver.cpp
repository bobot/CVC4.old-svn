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

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;


StrongSolverTheoryUf::StrongSolverTheoryUf(context::Context* c, TheoryUF* th) :
d_th( th )
{
  d_th->d_equalityEngine.d_thss = this;
}

/** new node */
void StrongSolverTheoryUf::newNode( EqualityNodeId n ){

}

/** merge */
void StrongSolverTheoryUf::merge( EqualityNodeId a, EqualityNodeId b ){

}

/** unmerge */
void StrongSolverTheoryUf::undoMerge( EqualityNodeId a, EqualityNodeId b ){

}

/** assert terms are disequal */
//void StrongSolverTheoryUf::assertDisequal( EqualityNodeId a, EqualityNodeId b ){
//}

void StrongSolverTheoryUf::debugPrint( const char* c ){

}

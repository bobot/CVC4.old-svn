/*********************                                                        */
/*! \file theory_uf_instantiator.h
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
 ** \brief Theory uf instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_STRONG_SOLVER_H
#define __CVC4__THEORY_UF_STRONG_SOLVER_H

#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdlist.h"
#include "context/cdlist_context_memory.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUF;

class StrongSolverTheoryUf{
protected:
  /** map from sorts to cardinalities */
  std::map< TypeNode, int > d_cardinalities;
  /** theory uf pointer */
  TheoryUF* d_th;
public:
  StrongSolverTheoryUf(context::Context* c, TheoryUF* th);
  ~StrongSolverTheoryUf() {}
  /** new node */
  void newNode( EqualityNodeId n );
  /** merge */
  void merge( EqualityNodeId a, EqualityNodeId b );
  /** unmerge */
  void undoMerge( EqualityNodeId a, EqualityNodeId b );
  /** assert terms are disequal */
  //void assertDisequal( EqualityNodeId a, EqualityNodeId b );
public:
  /** identify */
  std::string identify() const { return std::string("StrongSolverTheoryUf"); }
  /** debug print */
  void debugPrint( const char* c );
public:
  /** set cardinality for sort */
  void setCardinality( TypeNode t, int c ) { d_cardinalities[t] = c; }
  /** get cardinality for sort */
  int getCardinality( TypeNode t ) { return d_cardinalities.find( t )!=d_cardinalities.end() ? d_cardinalities[t] : -1; }
};/* class StrongSolverTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

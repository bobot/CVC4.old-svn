/*********************                                                        */
/*! \file model.h
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
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_H
#define __CVC4__MODEL_H

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

class FunctionTermModel
{
private:
  /** the operator we are considering */
  Node d_op
public:
  FunctionTermModel( Node op ) : d_op( op ){}
  ~FunctionTermModel(){}
public:
  /** evaluate the term, where n.getOperator() is d_op */
  virtual void evaluate( Node n ) = 0;
  /** print */
  //virtual void print() = 0;
};

class Model
{
public:
  /** equality engine containing all known equalities/disequalities */
  eq::EqualityEngine d_equalityEngine;
  /** list of all terms for each operator */
  std::map< Node, std::vector< Node > > d_terms;
  /** representatives for each type */
  std::map< TypeNode, std::vector< Node > > d_reps;
  /** models for each function */
  std::map< Node, FunctionTermModel > d_func_models;
public:
  Model(){}
  ~Model(){}
  /** get value */
  Node getValue( TNode n );
public:
  /** add equality */
  void addEquality( Node a, Node b );
  /** add predicate */
  void addPredicate( Node a, bool polarity );
  /** add equality engine */
  void addEqualityEngine( eq::EqualityEngine& ee );
};

}
}

#endif
/*********************                                                        */
/*! \file rep_set_iterator.h
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
 ** \brief rep_set_iterator class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__REP_SET_ITERATOR_H
#define __CVC4__THEORY__QUANTIFIERS__REP_SET_ITERATOR_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/rep_set.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class RepSetEvaluator
{
private:
  FirstOrderModel* d_model;
  RepSetIterator* d_riter;
private: //for Theory UF:
  //map from terms to the models used to calculate their value
  std::map< Node, bool > d_eval_uf_use_default;
  std::map< Node, uf::UfModelTree > d_eval_uf_model;
  void makeEvalUfModel( Node n );
  //index ordering to use for each term
  std::map< Node, std::vector< int > > d_eval_term_index_order;
  int getMaxVariableNum( int n );
  void makeEvalUfIndexOrder( Node n );
private:
  //default evaluate term function
  Node evaluateTermDefault( Node n, int& depIndex, std::vector< int >& childDepIndex );
  //temporary storing which literals have failed
  void clearEvalFailed( int index );
  std::map< Node, bool > d_eval_failed;
  std::map< int, std::vector< Node > > d_eval_failed_lits;
public:
  RepSetEvaluator( FirstOrderModel* m, RepSetIterator* ri );
  virtual ~RepSetEvaluator(){}
  /** evaluate functions */
  int evaluate( Node n, int& depIndex );
  Node evaluateTerm( Node n, int& depIndex );
public:
  //statistics
  int d_eval_formulas;
  int d_eval_uf_terms;
  int d_eval_lits;
  int d_eval_lits_unknown;
};/* class RepSetEvaluator */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif

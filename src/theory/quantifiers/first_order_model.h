/*********************                                                        */
/*! \file first_order_model.h
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
 ** \brief Model extended classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__FIRST_ORDER_MODEL_H
#define __CVC4__FIRST_ORDER_MODEL_H

#include "theory/model.h"
#include "theory/uf/theory_uf_model.h"
#include "theory/arrays/theory_arrays_model.h"

namespace CVC4 {
namespace theory {

struct ModelBasisAttributeId {};
typedef expr::Attribute<ModelBasisAttributeId, bool> ModelBasisAttribute;
//for APPLY_UF terms, 1 : term has direct child with model basis attribute,
//                    0 : term has no direct child with model basis attribute.
struct ModelBasisArgAttributeId {};
typedef expr::Attribute<ModelBasisArgAttributeId, uint64_t> ModelBasisArgAttribute;

class QuantifiersEngine;

namespace quantifiers{

class TermDb;

class FirstOrderModel : public DefaultModel
{
private:
  //add term function
  void addTerm( Node n );
  //for initialize model
  void initializeModelForTerm( Node n );
  /** whether an axiom is asserted */
  context::CDO< bool > d_axiom_asserted;
  /** list of quantifiers asserted in the current context */
  context::CDList<Node> d_forall_asserts;
public: //for Theory UF:
  //models for each UF operator
  std::map< Node, uf::UfModelTree > d_uf_model_tree;
  //model generators
  std::map< Node, uf::UfModelTreeGenerator > d_uf_model_gen;
private:
  //map from terms to the models used to calculate their value
  std::map< Node, bool > d_eval_uf_use_default;
  std::map< Node, uf::UfModelTree > d_eval_uf_model;
  void makeEvalUfModel( Node n );
  //index ordering to use for each term
  std::map< Node, std::vector< int > > d_eval_term_index_order;
  void makeEvalUfIndexOrder( Node n );
public: //for Theory Arrays:
  //default value for each non-store array
  std::map< Node, arrays::ArrayModel > d_array_model;
public: //for Theory Quantifiers:
  /** assert quantifier */
  void assertQuantifier( Node n );
  /** get number of asserted quantifiers */
  int getNumAssertedQuantifiers() { return (int)d_forall_asserts.size(); }
  /** get asserted quantifier */
  Node getAssertedQuantifier( int i ) { return d_forall_asserts[i]; }
  /** bool axiom asserted */
  bool isAxiomAsserted() { return d_axiom_asserted; }
public:
  FirstOrderModel( context::Context* c, std::string name );
  virtual ~FirstOrderModel(){}
  // reset the model
  void reset();
  /** get interpreted value */
  Node getInterpretedValue( TNode n );
public:
  // initialize the model
  void initialize( bool considerAxioms = true );
  /** to stream function */
  void toStream( std::ostream& out );
//the following functions are for evaluating quantifier bodies
public:
  /** reset evaluation */
  void resetEvaluate();
  /** evaluate functions */
  int evaluate( Node n, int& depIndex, RepSetIterator* ri  );
  Node evaluateTerm( Node n, int& depIndex, RepSetIterator* ri  );
public:
  //statistics
  int d_eval_formulas;
  int d_eval_uf_terms;
  int d_eval_lits;
  int d_eval_lits_unknown;
private:
  //default evaluate term function
  Node evaluateTermDefault( Node n, int& depIndex, std::vector< int >& childDepIndex, RepSetIterator* ri  );
  //temporary storing which literals have failed
  void clearEvalFailed( int index );
  std::map< Node, bool > d_eval_failed;
  std::map< int, std::vector< Node > > d_eval_failed_lits;
};/* class FirstOrderModel */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__FIRST_ORDER_MODEL_H */

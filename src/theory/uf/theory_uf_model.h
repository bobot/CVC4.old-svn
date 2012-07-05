/*********************                                                        */
/*! \file theory_uf_model.h
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
 ** \brief Model for Theory UF
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_MODEL_H
#define __CVC4__THEORY_UF_MODEL_H

#include "theory/model.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers{
  class ExtendedModel;
}

namespace uf {

class UfModelTree
{
public:
  UfModelTree(){}
  /** the data */
  std::map< Node, UfModelTree > d_data;
  /** the value of this tree node (if all paths lead to same value) */
  Node d_value;
public:
  //is this model tree empty?
  bool isEmpty() { return d_data.empty() && d_value.isNull(); }
  //clear
  void clear();
  /** setValue function
    *
    * For each argument of n with ModelBasisAttribute() set to true will be considered default arguments if ground=false
    *
    */
  void setValue( QuantifiersEngine* qe, Node n, Node v, std::vector< int >& indexOrder, bool ground, int argIndex );
  /**  getValue function
    *
    *  returns $val, the value of ground term n
    *  Say n is f( t_0...t_n )
    *    depIndex is the index for which every term of the form f( t_0 ... t_depIndex, *,... * ) is equal to $val
    *    for example, if g( x_0, x_1, x_2 ) := lambda x_0 x_1 x_2. if( x_1==a ) b else c,
    *      then g( a, a, a ) would return b with depIndex = 1
    *  If ground = true, we are asking whether the term n is constant (assumes that all non-model basis arguments are ground)
    *
    */
  Node getValue( QuantifiersEngine* qe, Node n, std::vector< int >& indexOrder, int& depIndex, int argIndex );
  ///** getConstant Value function
  //  *
  //  * given term n, where n may contain model basis arguments
  //  * if n is constant for its entire domain, then this function returns the value of its domain
  //  * otherwise, it returns null
  //  * for example, if f( x_0, x_1 ) := if( x_0 = a ) b else if( x_1 = a ) a else b,
  //  *   then f( a, e ) would return b, while f( e, a ) would return null
  //  *
  //  */
  Node getConstantValue( QuantifiersEngine* qe, Node n, std::vector< int >& indexOrder, int argIndex );
  /** simplify function */
  void simplify( Node op, Node defaultVal, int argIndex );
  // is total ?
  bool isTotal( Node op, int argIndex );
public:
  void debugPrint( const char* c, QuantifiersEngine* qe, std::vector< int >& indexOrder, int ind = 0, int arg = 0 );
};

class UfModelTreeOrdered
{
private:
  Node d_op;
  std::vector< int > d_index_order;
  UfModelTree d_tree;
public:
  UfModelTreeOrdered(){}
  UfModelTreeOrdered( Node op ) : d_op( op ){
    TypeNode tn = d_op.getType();
    for( int i=0; i<(int)(tn.getNumChildren()-1); i++ ){
      d_index_order.push_back( i );
    }
  }
  UfModelTreeOrdered( Node op, std::vector< int >& indexOrder ) : d_op( op ){
    d_index_order.insert( d_index_order.end(), indexOrder.begin(), indexOrder.end() );
  }
  bool isEmpty() { return d_tree.isEmpty(); }
  void clear() { d_tree.clear(); }
  void setValue( QuantifiersEngine* qe, Node n, Node v, bool ground = true ){
    d_tree.setValue( qe, n, v, d_index_order, ground, 0 );
  }
  Node getValue( QuantifiersEngine* qe, Node n, int& depIndex ){
    return d_tree.getValue( qe, n, d_index_order, depIndex, 0 );
  }
  Node getConstantValue( QuantifiersEngine* qe, Node n ) {
    return d_tree.getConstantValue( qe, n, d_index_order, 0 );
  }
  void simplify() { d_tree.simplify( d_op, Node::null(), 0 ); }
  bool isTotal() { return d_tree.isTotal( d_op, 0 ); }
public:
  void debugPrint( const char* c, QuantifiersEngine* qe, int ind = 0 ){
    d_tree.debugPrint( c, qe, d_index_order, ind );
  }
};

class UfModel
{
private:
  Node d_op;
  quantifiers::ExtendedModel* d_model;
  QuantifiersEngine* d_qe;
  std::vector< Node > d_ground_asserts;
  std::vector< Node > d_ground_asserts_reps;
  bool d_model_constructed;
  //store for set values
  std::map< Node, Node > d_set_values[2][2];
  // preferences for default values
  std::vector< Node > d_values;
  std::map< Node, std::vector< Node > > d_value_pro_con[2];
  std::map< Node, std::vector< Node > > d_term_pro_con[2];
  /** set value */
  void setValue( Node n, Node v, bool ground = true, bool isReq = true );
  /** set model */
  void setModel();
  /** clear model */
  void clearModel();
private:
  // defaults
  std::vector< Node > d_defaults;
  Node getIntersection( Node n1, Node n2, bool& isGround );
  // compute model basis arg
  static void computeModelBasisArgAttribute( Node n );
public:
  UfModel(){}
  UfModel( Node op, quantifiers::ExtendedModel* m, QuantifiersEngine* qe );
  ~UfModel(){}
  //data structure that stores the model
  UfModelTreeOrdered d_tree;
  //quantifiers that are satisfied because of the constant definition of d_op
  bool d_reconsider_model;
  //the domain of the arguments
  std::map< int, RepDomain > d_active_domain;
  //the range of the function
  RepDomain d_active_range;
public:
  /** debug print */
  void debugPrint( const char* c );
  /** get value */
  Node getValue( Node n, int& depIndex );
  /** get constant value */
  Node getConstantValue( Node n );
  /** is empty */
  bool isEmpty() { return d_ground_asserts.empty(); }
  /** is constant */
  bool isConstant();
public:
  /** build model */
  void buildModel();
  /** make model */
  void makeModel( UfModelTreeOrdered& tree );
  /** compute relevant domain */
  void computeRelevantDomain();
public:
  /** set value preference */
  void setValuePreference( Node f, Node n, bool isPro );
};


}
}
}

#endif

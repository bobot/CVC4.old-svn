/*********************                                                        */
/*! \file instantiation_engine.h
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
 ** \brief Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_ENGINE_H
#define __CVC4__MODEL_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"

namespace CVC4 {
namespace theory {

namespace uf{
  class StrongSolverTheoryUf;
}

namespace quantifiers {

/** this class stores a representative alphabet */
class RepAlphabet {
public:
  RepAlphabet(){}
  RepAlphabet( RepAlphabet& ra, QuantifiersEngine* qe );
  ~RepAlphabet(){}
  std::map< TypeNode, std::vector< Node > > d_type_reps;
  std::map< Node, int > d_tmap;
  /** clear the alphabet */
  void clear(){
    d_type_reps.clear();
    d_tmap.clear();
  }
  /** set the representatives for type */
  void set( TypeNode t, std::vector< Node >& reps );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) { return d_tmap.find( n )!=d_tmap.end() ? d_tmap[n] : -1; }
  /** debug print */
  void debugPrint( const char* c, QuantifiersEngine* qe );
};

class ModelEngine;

/** this class iterates over a RepAlphabet */
class RepAlphabetIterator {
public:
  RepAlphabetIterator( QuantifiersEngine* qe, Node f, ModelEngine* model );
  ~RepAlphabetIterator(){}
  Node d_f;
  ModelEngine* d_model;
  std::vector< int > d_index;
  std::vector< Node > d_ic;
  std::vector< Node > d_terms;
  /** increment the iterator */
  void increment2( QuantifiersEngine* qe, int counter ); 
  void increment( QuantifiersEngine* qe );
  /** is the iterator finished? */
  bool isFinished();
  /** produce the match that this iterator represents */
  void getMatch( QuantifiersEngine* qe, InstMatch& m );
  /** get functions */
  Node getTerm( int i );
  int getNumTerms() { return d_f[0].getNumChildren(); }
  /** refresh d_term to be current with d_index */
  void calculateTerms( QuantifiersEngine* qe );
  /** debug print */
  void debugPrint( const char* c );
  void debugPrintSmall( const char* c );
  //for debugging
  int d_inst_skipped;
  int d_inst_tried;
  int d_inst_tests;
};


class UfModelTree
{
private:
  //helper function for set value
  void setValue2( QuantifiersEngine* qe, Node n, Node v, int argIndex, bool ground );
  //helper function for get value
  Node getValue2( QuantifiersEngine* qe, Node n, int& depIndex, int argIndex );
  ////helper function for get constant value
  //Node getConstantValue2( QuantifiersEngine* qe, Node n, int argIndex );
  //helper function for simplify
  void simplify2( Node op, Node defaultVal, int argIndex );
  //helper function for is total
  bool isTotal2( Node op, int argIndex );
public:
  UfModelTree(){}
  /** the data */
  std::map< Node, UfModelTree > d_data;
  /** the value of this tree node (if all paths lead to same value) */
  Node d_value;
  /** which terms have been defined as d_value */
  //std::vector< Node > d_explicit;
public:
  //is this model tree empty?
  bool isEmpty() { return d_data.empty(); }
  /** setValue function
    *
    * For each argument of n with ModelBasisAttribute() set to true will be considered default arguments if ground=false
    *
    */
  void setValue( QuantifiersEngine* qe, Node n, Node v, bool ground = true );
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
  Node getValue( QuantifiersEngine* qe, Node n, int& depIndex );
  ///** getConstant Value function
  //  *
  //  * given term n, where n may contain model basis arguments
  //  * if n is constant for its entire domain, then this function returns the value of its domain
  //  * otherwise, it returns null
  //  * for example, if f( x_0, x_1 ) := if( x_0 = a ) b else if( x_1 = a ) a else b,
  //  *   then f( a, e ) would return b, while f( e, a ) would return null
  //  *
  //  */
  //Node getConstantValue( QuantifiersEngine* qe, Node n ){ return getConstantValue2( qe, n, 0 ); }
  /** simplify function */
  void simplify( Node op ) { simplify2( op, Node::null(), 0 ); }
  // is total ?
  bool isTotal( Node op ) { return isTotal2( op, 0 ); }
public:
  void debugPrint( const char* c, QuantifiersEngine* qe, int ind = 0, int arg = 0 );
};

class UfModel
{
private:
  Node d_op;
  ModelEngine* d_me;
  std::map< Node, std::vector< Node > > d_reqs[2];
  std::map< Node, std::map< Node, std::vector< Node > > > d_eq_reqs[2];
  std::vector< Node > d_ground_asserts;
  bool d_model_constructed;
public:
  UfModel(){}
  UfModel( Node op, ModelEngine* qe );
  ~UfModel(){}
  //data structure that stores the model
  UfModelTree d_tree;
  /** set value */
  void setValue( Node n, Node v, bool ground = true );
  /** simplify */
  void simplify() { d_tree.simplify( d_op ); }
public:
  /** add requirement */
  void addRequirement( Node f, Node p, bool phase );
  /** add equality requirement */
  void addEqRequirement( Node f, Node t, Node te, bool phase );
  /** debug print */
  void debugPrint( const char* c );
  /** get constant value */
  Node getConstantValue( QuantifiersEngine* qe, Node n );
  /** is empty */
  bool isEmpty() { return d_ground_asserts.empty(); }
  /** is constant */
  bool isConstant();
public:
  /** build model */
  void buildModel();
};




class ModelEngine : public QuantifiersModule
{
  friend class UfModel;
private:
  TheoryQuantifiers* d_th;
  QuantifiersEngine* d_quantEngine;
  uf::StrongSolverTheoryUf* d_ss;
  //which quantifiers have been initialized
  std::map< Node, bool > d_quant_init;
  //map from ops to model basis terms
  std::map< Node, Node > d_model_basis_term;
  //map from instantiation terms to their model basis equivalent
  std::map< Node, Node > d_model_basis;
  //the model we are working with
  RepAlphabet d_ra;
  std::map< Node, UfModel > d_uf_model;
  //map from model basis terms to quantifiers that are pro/con their definition
  std::map< Node, std::vector< Node > > d_quant_pro_con[2];
  std::map< Node, bool > d_quant_sat;
private:
  int evaluate( RepAlphabetIterator* rai, Node n, bool phaseReq );
  bool evaluateEquality( Node n1, Node n2, Node gn1, Node gn2, bool phaseReq, std::vector< Node >& fv_deps, bool calc_fv_deps = false );
  Node evaluateTerm( Node n, Node gn, std::vector< Node >& fv_deps, bool calc_fv_deps = false );
private:
  //queries about equality
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
private:
  bool useModel();
private:
  //build representatives
  void buildRepresentatives();
  //initialize model
  void initializeModel();
  //analyze quantifiers
  void analyzeQuantifiers();
private:
  //register instantiation terms with their corresponding model basis terms
  void registerModelBasis( Node n, Node gn );
  //for building UF model
  void initializeUf( Node n );
  void initializeUfModel( Node op );
  void processPredicate( Node f, Node p, bool phase );
  void processEquality( Node f, Node eq, bool phase );
public:
  ModelEngine( TheoryQuantifiers* th );
  ~ModelEngine(){}
  //get quantifiers engine
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
  //get representatives
  RepAlphabet* getReps() { return &d_ra; }
  //get default term for op
  Node getModelBasisTerm( Node op );
public:
  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  void propagate( Theory::Effort level ){}
  void debugPrint( const char* c );
public:
  void increment( RepAlphabetIterator* rai );
};

}
}
}

#endif

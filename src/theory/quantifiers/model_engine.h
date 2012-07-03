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
  /** has type */
  bool hasType( TypeNode tn ) { return d_type_reps.find( tn )!=d_type_reps.end(); }
  /** set the representatives for type */
  void set( TypeNode t, std::vector< Node >& reps );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) { return d_tmap.find( n )!=d_tmap.end() ? d_tmap[n] : -1; }
  /** debug print */
  void debugPrint( const char* c, QuantifiersEngine* qe );
};

class ModelEngine;

//representative domain
typedef std::vector< int > RepDomain;

/** this class iterates over a RepAlphabet */
class RepAlphabetIterator {
private:
  //initialize the iterator
  void initialize( QuantifiersEngine* qe, Node f, ModelEngine* model );
public:
  RepAlphabetIterator( QuantifiersEngine* qe, Node f, ModelEngine* model );
  ~RepAlphabetIterator(){}
  //pointer to quantifier
  Node d_f;
  //pointer to model
  ModelEngine* d_model;
  //index we are considering
  std::vector< int > d_index;
  //domain we are considering
  std::vector< RepDomain > d_domain;
  //ordering for variables we are indexing over
  //  for example, given reps = { a, b } and quantifier forall( x, y, z ) P( x, y, z ) with d_index_order = { 2, 0, 1 },
  //    then we consider instantiations in this order:
  //      a/x a/y a/z
  //      a/x b/y a/z
  //      b/x a/y a/z
  //      b/x b/y a/z
  //      ...
  std::vector< int > d_index_order;
  //variables to index they are considered at
  //  for example, if d_index_order = { 2, 0, 1 }
  //    then d_var_order = { 0 -> 1, 1 -> 2, 2 -> 0 }
  std::map< int, int > d_var_order;
  //the instantiation constants of d_f
  std::vector< Node > d_ic;
  //the current terms we are considering
  std::vector< Node > d_terms;
public:
  /** set index order */
  void setIndexOrder( std::vector< int >& indexOrder );
  /** set domain */
  void setDomain( std::vector< RepDomain >& domain );
  /** increment the iterator */
  void increment2( QuantifiersEngine* qe, int counter );
  void increment( QuantifiersEngine* qe );
  /** is the iterator finished? */
  bool isFinished();
  /** produce the match that this iterator represents */
  void getMatch( QuantifiersEngine* qe, InstMatch& m );
  /** get the i_th term we are considering */
  Node getTerm( int i );
  /** get the number of terms we are considering */
  int getNumTerms() { return d_f[0].getNumChildren(); }
  /** refresh d_term to be current with d_index */
  void calculateTerms( QuantifiersEngine* qe );
  /** debug print */
  void debugPrint( const char* c );
  void debugPrintSmall( const char* c );
};


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
  void clear(){
    d_data.clear();
    d_value = Node::null();
  }
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
  ModelEngine* d_me;
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
  UfModel( Node op, ModelEngine* qe );
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
  /** get constant value */
  Node getConstantValue( QuantifiersEngine* qe, Node n );
  /** is empty */
  bool isEmpty() { return d_ground_asserts.empty(); }
  /** is constant */
  bool isConstant();
public:
  /** build model */
  void buildModel();
  /** make model */
  void makeModel( QuantifiersEngine* qe, UfModelTreeOrdered& tree );
  /** compute relevant domain */
  void computeRelevantDomain();
public:
  /** set value preference */
  void setValuePreference( Node f, Node n, bool isPro );
};




class ModelEngine : public QuantifiersModule
{
  friend class UfModel;
  friend class RepAlphabetIterator;
private:
  TheoryQuantifiers* d_th;
  QuantifiersEngine* d_quantEngine;
  uf::StrongSolverTheoryUf* d_ss;
  //true/false nodes
  Node d_true;
  Node d_false;
  //which quantifiers have been initialized
  std::map< Node, bool > d_quant_init;
  //map from ops to model basis terms
  std::map< Node, Node > d_model_basis_term;
  //map from instantiation terms to their model basis equivalent
  std::map< Node, Node > d_model_basis;
  //map from quantifiers to model basis match
  std::map< Node, InstMatch > d_quant_basis_match;
private:
  //the model we are working with
  RepAlphabet d_ra;
  std::map< Node, UfModel > d_uf_model;
  //map from quantifiers to the instantiation literals that their model is dependent upon
  std::map< Node, std::vector< Node > > d_quant_model_lits;
  //map from quantifiers to if are constant SAT
  std::map< Node, bool > d_quant_sat;
  //map from quantifiers to uf terms they contain
  std::map< Node, std::vector< Node > > d_quant_uf_terms;
  //relevant instantiation domain for each quantifier
  std::map< Node, std::vector< RepDomain > > d_quant_inst_domain;
private:
  int evaluate( RepAlphabetIterator* rai, Node n, int& depIndex );
  int evaluateEquality( RepAlphabetIterator* rai, Node n1, Node n2, Node gn1, Node gn2, int& depIndex );
  Node evaluateTerm( RepAlphabetIterator* rai, Node n, Node gn, int& depIndex );
  //temporary storing which literals have failed
  void clearEvalFailed( int index );
  std::map< Node, bool > d_eval_failed;
  std::map< int, std::vector< Node > > d_eval_failed_lits;
private:
  //map from terms to the models used to calculate their value
  std::map< Node, UfModelTreeOrdered > d_eval_term_model;
  std::map< Node, bool > d_eval_term_use_default_model;
  void makeEvalTermModel( Node n );
  //index ordering to use for each term
  std::map< Node, std::vector< int > > d_eval_term_index_order;
  int getMaxVariableNum( int n );
  void makeEvalTermIndexOrder( Node n );
private:
  //queries about equality
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
private:
  //options
  bool optUseModel();
  bool optOneInstPerQuantRound();
  bool optInstGen();
  bool optUseRelevantDomain();
  bool optOneQuantPerRoundInstGen();
  bool optOneQuantPerRound();
private:
  //initialize quantifiers, return number of lemmas produced
  int initializeQuantifier( Node f );
  //build representatives
  void buildRepresentatives();
  //initialize model
  void initializeModel();
  //analyze quantifiers
  void analyzeQuantifiers();
  //do InstGen techniques for quantifier, return number of lemmas produced
  int doInstGen( Node f );
  //exhaustively instantiate quantifier (possibly using mbqi), return number of lemmas produced
  int exhaustiveInstantiate( Node f, bool useRelInstDomain = false );
private:
  //temporary statistics
  int d_triedLemmas;
  int d_testLemmas;
  int d_totalLemmas;
private:
  //register instantiation terms with their corresponding model basis terms
  void registerModelBasis( Node n, Node gn );
  //for building UF model
  void collectUfTerms( Node n, std::vector< Node >& terms );
  void initializeUfModel( Node op );
  //for computing relevant instantiation domain, return true if changed
  bool computeRelevantInstantiationDomain( Node n, Node parent, int arg, std::vector< RepDomain >& rd );
  //for computing extended
  bool extendFunctionDomains( Node n, RepDomain& range );
public:
  ModelEngine( TheoryQuantifiers* th );
  ~ModelEngine(){}
  //get quantifiers engine
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
  //get representatives
  RepAlphabet* getReps() { return &d_ra; }
  //get arbitrary element
  Node getArbitraryElement( TypeNode tn, std::vector< Node >& exclude );
  //get model basis term
  Node getModelBasisTerm( TypeNode tn, int i = 0 );
  //get model basis term for op
  Node getModelBasisApplyUfTerm( Node op );
  //is model basis term for op
  //bool isModelBasisTerm( Node op, Node n );
public:
  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  void propagate( Theory::Effort level ){}
  void debugPrint( const char* c );
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_inst_rounds;
    IntStat d_pre_sat_quant;
    IntStat d_pre_nsat_quant;
    IntStat d_eval_formulas;
    IntStat d_eval_eqs;
    IntStat d_eval_uf_terms;
    IntStat d_num_quants_init;
    IntStat d_num_quants_init_fail;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  //
  std::map< Node, bool > d_quant_semi_sat;
};

}
}
}

#endif

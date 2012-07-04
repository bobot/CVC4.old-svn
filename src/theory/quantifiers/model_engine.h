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
#include "theory/model.h"
#include "theory/uf/theory_uf_model.h"

namespace CVC4 {
namespace theory {

struct ModelBasisAttributeId {};
typedef expr::Attribute<ModelBasisAttributeId, bool> ModelBasisAttribute;
//for APPLY_UF terms, 1 : term has direct child with model basis attribute,
//                    0 : term has no direct child with model basis attribute.
struct ModelBasisArgAttributeId {};
typedef expr::Attribute<ModelBasisArgAttributeId, uint64_t> ModelBasisArgAttribute;

namespace uf{
  class StrongSolverTheoryUf;
}

namespace quantifiers {

class ModelEngine;

/** this class iterates over a RepSet */
class RepSetIterator {
private:
  //initialize the iterator
  void initialize( QuantifiersEngine* qe, Node f, ModelEngine* model );
public:
  RepSetIterator( QuantifiersEngine* qe, Node f, ModelEngine* model );
  ~RepSetIterator(){}
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


class ExtModel : public Model
{
public:
  ExtModel( context::Context* c );
  virtual ~ExtModel(){}
  /** get value */
  Node getValue( TNode n );
};

class ModelEngine : public QuantifiersModule
{
  friend class uf::UfModel;
  friend class RepSetIterator;
private:
  //model builder object
  class ModelEngineModelBuilder : public theory::ModelBuilder{
    ModelEngine& d_me;
  public:
    ModelEngineModelBuilder( ModelEngine& me ) : d_me( me ){}
    virtual ~ModelEngineModelBuilder(){}
    void buildModel( Model& m ) { d_me.buildModel( m ); }
  };
private:
  TheoryQuantifiers* d_th;
  QuantifiersEngine* d_quantEngine;
  uf::StrongSolverTheoryUf* d_ss;
  ModelEngineModelBuilder d_builder;
  //true/false nodes
  Node d_true;
  Node d_false;
  //which quantifiers have been initialized
  std::map< Node, bool > d_quant_init;
  //map from types to model basis terms
  std::map< TypeNode, Node > d_model_basis_term;
  //map from ops to model basis terms
  std::map< Node, Node > d_model_basis_op_term;
  //map from instantiation terms to their model basis equivalent
  std::map< Node, Node > d_model_basis;
  //map from quantifiers to model basis match
  std::map< Node, InstMatch > d_quant_basis_match;
private:
  //the model we are working with
  RepSet d_ra;
  std::map< Node, uf::UfModel > d_uf_model;
  //map from quantifiers to the instantiation literals that their model is dependent upon
  std::map< Node, std::vector< Node > > d_quant_model_lits;
  //map from quantifiers to if are constant SAT
  std::map< Node, bool > d_quant_sat;
  //map from quantifiers to uf terms they contain
  std::map< Node, std::vector< Node > > d_quant_uf_terms;
  //relevant instantiation domain for each quantifier
  std::map< Node, std::vector< RepDomain > > d_quant_inst_domain;
private:
  int evaluate( RepSetIterator* rai, Node n, int& depIndex );
  int evaluateEquality( RepSetIterator* rai, Node n1, Node n2, Node gn1, Node gn2, int& depIndex );
  Node evaluateTerm( RepSetIterator* rai, Node n, Node gn, int& depIndex );
  //temporary storing which literals have failed
  void clearEvalFailed( int index );
  std::map< Node, bool > d_eval_failed;
  std::map< int, std::vector< Node > > d_eval_failed_lits;
private:
  //map from terms to the models used to calculate their value
  std::map< Node, uf::UfModelTreeOrdered > d_eval_term_model;
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
  //build model
  void buildModel( Model& m );
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
  RepSet* getReps() { return &d_ra; }
  //get arbitrary element
  Node getArbitraryElement( TypeNode tn, std::vector< Node >& exclude );
  //get model basis term
  Node getModelBasisTerm( TypeNode tn, int i = 0 );
  //get model basis term for op
  Node getModelBasisOpTerm( Node op );
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

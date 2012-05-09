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


class ModelTree
{
private:
  void setValue2( QuantifiersEngine* qe, Node n, Node v, int argIndex );
  Node getValue2( QuantifiersEngine* qe, Node n, int& depIndex, int argIndex );
public:
  ModelTree(){}
  /** the data */
  std::map< Node, ModelTree > d_data;
  Node d_value;
  std::vector< Node > d_explicit;
public:
  bool isEmpty() { return d_data.empty() && d_explicit.empty(); }
  void setValue( QuantifiersEngine* qe, Node n, Node v ) { setValue2( qe, n, v, 0 ); }
  Node getValue( QuantifiersEngine* qe, Node n, int& depIndex ) { return getValue2( qe, n, depIndex, 0 ); }
public:
  void debugPrint( const char* c, int ind = 0, int arg = 0 );
};

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
  void debugPrint( const char* c );
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
  void increment( QuantifiersEngine* qe );
  bool isFinished();
  void getMatch( QuantifiersEngine* qe, InstMatch& m );
  Node getTerm( int i );
  int getNumTerms() { return d_f[0].getNumChildren(); }
  void calculateTerms( QuantifiersEngine* qe );
};

class PredModel
{
private:
  Node d_op;
  QuantifiersEngine* d_qe;
  std::map< Node, std::vector< Node > > d_reqs[2];
  ModelTree d_tree;
public:
  PredModel(){}
  PredModel( Node op, QuantifiersEngine* qe );
  ~PredModel(){}

  void addRequirement( Node f, Node p, bool phase );
  /** debug print */
  void debugPrint( const char* c );
};

class FunctionModel
{
private:
  Node d_op;
  QuantifiersEngine* d_qe;
  std::map< Node, std::map< Node, std::vector< Node > > > d_reqs[2];
  ModelTree d_tree;
public:
  FunctionModel(){}
  FunctionModel( Node op, QuantifiersEngine* qe );
  ~FunctionModel(){}
  /** add requirement */
  void addRequirement( Node f, Node t, Node te, bool phase );
  /** debug print */
  void debugPrint( const char* c );
};




class ModelEngine : public QuantifiersModule
{
private:
  TheoryQuantifiers* d_th;
  QuantifiersEngine* d_quantEngine;
  uf::StrongSolverTheoryUf* d_ss;
  RepAlphabet d_ra;
  std::map< Node, PredModel > d_pred_model;
  std::map< Node, FunctionModel > d_func_model;
  //int evaluate( RepAlphabetIterator* rai, Node n, bool phaseReq, std::vector< Node >& modelExt );
  //int evaluateLiteral( RepAlphabetIterator* rai, Node lit, bool phaseReq, std::vector< Node >& modelExt );
private:
  void processPredicate( Node f, Node p, bool phase );
  void processEquality( Node f, Node eq, bool phase );
private:
  //build representatives
  void buildRepresentatives();
public:
  ModelEngine( TheoryQuantifiers* th );
  ~ModelEngine(){}
  RepAlphabet* getReps() { return &d_ra; }
public:
  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  void propagate( Theory::Effort level ){}
  void debugPrint( const char* c );
public:
  void validate( RepAlphabetIterator* rai );
private:
  void buildModel();
};

}
}
}

#endif

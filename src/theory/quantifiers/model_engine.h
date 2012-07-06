/*********************                                                        */
/*! \file model_engine.h
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
 ** \brief Model Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_ENGINE_H
#define __CVC4__MODEL_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/model.h"
#include "theory/uf/theory_uf_model.h"
#include "theory/quantifiers/relevant_domain.h"

namespace CVC4 {
namespace theory {

namespace uf{
  class StrongSolverTheoryUf;
}

namespace quantifiers {

class ModelEngine : public QuantifiersModule
{
  friend class uf::UfModel;
  friend class RepSetIterator;
private:    //data maintained globally:
  //which quantifiers have been initialized
  std::map< Node, bool > d_quant_init;
  //map from quantifiers to model basis match
  std::map< Node, InstMatch > d_quant_basis_match;
private:    //analysis of current model:
  //map from quantifiers to if are constant SAT
  std::map< Node, bool > d_quant_sat;
  //map from quantifiers to the instantiation literals that their model is dependent upon
  std::map< Node, std::vector< Node > > d_quant_selection_lits;
  //map from operators to model preference data
  std::map< Node, uf::UfModelPreferenceData > d_uf_prefs;
  //relevant domain
  RelevantDomain d_rel_domain;
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
  //analyze quantifiers
  void analyzeQuantifiers();
  //build model
  void buildModel();
  //theory-specific build models
  void buildModelUf( uf::UfModel& model );
  //do InstGen techniques for quantifier, return number of lemmas produced
  int doInstGen( Node f );
  //exhaustively instantiate quantifier (possibly using mbqi), return number of lemmas produced
  int exhaustiveInstantiate( Node f, bool useRelInstDomain = false );
private:
  //temporary statistics
  int d_triedLemmas;
  int d_testLemmas;
  int d_totalLemmas;
public:
  ModelEngine( QuantifiersEngine* qe );
  ~ModelEngine(){}
  //get quantifiers engine
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
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
};

}
}
}

#endif

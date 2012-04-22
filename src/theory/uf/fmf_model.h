/*********************                                                        */
/*! \file fmf_model.h
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
 ** \brief fmf model
 **/

#include "cvc4_private.h"

#ifndef __CVC4__FMF_MODEL_H
#define __CVC4__FMF_MODEL_H

#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace uf {


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

class PredModel
{
private:
  Node d_op;
  QuantifiersEngine* d_qe;
  std::map< Node, std::vector< Node > > d_reqs[2];
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
public:
  FunctionModel(){}
  FunctionModel( Node op, QuantifiersEngine* qe );
  ~FunctionModel(){}
  /** add requirement */
  void addRequirement( Node f, Node t, Node te, bool phase );
  /** debug print */
  void debugPrint( const char* c );
};

class RepAlphabetIterator;

class FmfModel{
private:
  QuantifiersEngine* d_quantEngine;
  StrongSolverTheoryUf* d_ss;
  RepAlphabet d_ra;
private:
  //build representatives
  void buildRepresentatives();
private:
  void processPredicate( Node f, Node p, bool phase );
  void processEquality( Node f, Node eq, bool phase );
public:
  FmfModel( QuantifiersEngine* qe, StrongSolverTheoryUf* ss );
  ~FmfModel(){}
  
  std::map< Node, PredModel > d_pred_model;
  std::map< Node, FunctionModel > d_func_model;

  void buildModel();
  RepAlphabet* getReps() { return &d_ra; }
public:
  int acceptCurrent( RepAlphabetIterator* rai );
  void debugPrint( const char* c );
};

}
}
}

#endif

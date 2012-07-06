/*********************                                                        */
/*! \file first_order_model.cpp
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
 ** \brief Implementation of model engine model class
 **/

#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/rep_set_iterator.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/uf/theory_uf_strong_solver.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

FirstOrderModel::FirstOrderModel( QuantifiersEngine* qe, context::Context* c, std::string name ) : Model( qe->getTheoryEngine(), name ),
d_qe( qe ), d_forall_asserts( c ){

}

void FirstOrderModel::processInitialize(){
  //rebuild models
  d_uf_model.clear();
  //for each quantifier, collect all operators we care about
  for( int i=0; i<getNumAssertedQuantifiers(); i++ ){
    Node f = getAssertedQuantifier( i );
    //initialize model for term
    initializeModelForTerm( f[1] );
  }

  if( Options::current()->printModelEngine ){
    for( std::map< TypeNode, std::vector< Node > >::iterator it = d_ra.d_type_reps.begin(); it != d_ra.d_type_reps.end(); ++it ){
      if( uf::StrongSolverTheoryUf::isRelevantType( it->first ) ){
        Message() << "Cardinality( " << it->first << " )" << " = " << it->second.size() << std::endl;
      }
    }
  }
}

void FirstOrderModel::initializeModelForTerm( Node n ){
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( d_uf_model.find( op )==d_uf_model.end() ){
      TypeNode tn = op.getType();
      tn = tn[ (int)tn.getNumChildren()-1 ];
      if( tn==NodeManager::currentNM()->booleanType() || uf::StrongSolverTheoryUf::isRelevantType( tn ) ){
        d_uf_model[ op ] = uf::UfModel( op, d_qe );
      }
    }
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    initializeModelForTerm( n[i] );
  }
}

void FirstOrderModel::buildModel(){
  for( std::map< Node, uf::UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.buildModel();
  }
  Debug("fmf-model-debug") << "Done building models." << std::endl;
  //print debug
  Debug("fmf-model-complete") << std::endl;
  debugPrint("fmf-model-complete");
}

Node FirstOrderModel::getInterpretedValue( TNode n ){
  if( n.getKind()==APPLY_UF ){
    int depIndex;
    return d_uf_model[ n.getOperator() ].getValue( n, depIndex );
  }
  return n;
}

void FirstOrderModel::debugPrint( const char* c ){
  Debug( c ) << "---Current Model---" << std::endl;
  Debug( c ) << "Representatives: " << std::endl;
  d_ra.debugPrint( c );
  Debug( c ) << "Functions: " << std::endl;
  for( std::map< Node, uf::UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.debugPrint( c );
    Debug( c ) << std::endl;
  }
}

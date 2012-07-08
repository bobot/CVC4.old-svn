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

FirstOrderModel::FirstOrderModel( QuantifiersEngine* qe, context::Context* c, std::string name ) : TheoryModel( qe->getTheoryEngine(), name ),
d_term_db( qe->getTermDatabase() ), d_forall_asserts( c ){

}

void FirstOrderModel::initialize(){
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
        d_uf_model[ op ] = uf::UfModel( op, this );
      }
    }
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    initializeModelForTerm( n[i] );
  }
}


Node FirstOrderModel::getInterpretedValue( TNode n ){
  Debug("fo-model") << "get interpreted value " << n << std::endl;
  if( n.getKind()==APPLY_UF ){
    int depIndex;
    return d_uf_model[ n.getOperator() ].getValue( n, depIndex );
  }
  return n;
}

TermDb* FirstOrderModel::getTermDatabase(){
  return d_term_db;
}

void FirstOrderModel::toStream(std::ostream& out){
  out << "---Current Model---" << std::endl;
  out << "Representatives: " << std::endl;
  d_ra.toStream( out );
  out << "Functions: " << std::endl;
  for( std::map< Node, uf::UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.toStream( out );
    out << std::endl;
  }
}
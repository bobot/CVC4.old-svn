/*********************                                                        */
/*! \file model_engine_model.cpp
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

#include "theory/quantifiers/model_engine_model.h"
#include "theory/quantifiers/rep_set_iterator.h"
#include "theory/quantifiers/model_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

ExtendedModel::ExtendedModel( QuantifiersEngine* qe, context::Context* c ) : Model( c ), d_qe( qe ){

}

void ExtendedModel::buildModel(){
  for( std::map< Node, uf::UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.buildModel();
  }
  Debug("fmf-model-debug") << "Done building models." << std::endl;
  //print debug
  Debug("fmf-model-complete") << std::endl;
  debugPrint("fmf-model-complete");
}

Node ExtendedModel::getValue( TNode n ){
  if( n.getKind()==APPLY_UF ){

  }
  return n;
}

void ExtendedModel::debugPrint( const char* c ){
  Debug( c ) << "---Current Model---" << std::endl;
  Debug( c ) << "Representatives: " << std::endl;
  d_ra.debugPrint( c, d_qe );
  Debug( c ) << "Functions: " << std::endl;
  for( std::map< Node, uf::UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.debugPrint( c );
    Debug( c ) << std::endl;
  }
}

bool ExtendedModel::areEqual( Node a, Node b ){
  return d_qe->getEqualityQuery()->areEqual( a, b );
  //return d_equalityEngine.areEqual( a, b );
}

bool ExtendedModel::areDisequal( Node a, Node b ){
  return d_qe->getEqualityQuery()->areDisequal( a, b );
  //return d_equalityEnginee.areDisequal( a, b );
}

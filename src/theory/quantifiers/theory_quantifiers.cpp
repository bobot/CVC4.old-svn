/*********************                                                        */
/*! \file theory_quantifiers.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): bobot, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of quantifiers
 **
 ** Implementation of the theory of quantifiers.
 **/


#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/valuation.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/instantiation_engine.h"
#include "theory/quantifiers/model_engine.h"
#include "expr/kind.h"
#include "util/cvc4_assert.h"
#include "theory/quantifiers/theory_quantifiers_instantiator.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quantifiers_attributes.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

TheoryQuantifiers::TheoryQuantifiers(Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe) :
  Theory(THEORY_QUANTIFIERS, c, u, out, valuation, logicInfo, qe),
  d_numRestarts(0){
  d_numInstantiations = 0;
  d_baseDecLevel = -1;
  out.handleUserAttribute( "axiom", this );
  out.handleUserAttribute( "conjecture", this );
}


TheoryQuantifiers::~TheoryQuantifiers() {
}

void TheoryQuantifiers::addSharedTerm(TNode t) {
  Debug("quantifiers-other") << "TheoryQuantifiers::addSharedTerm(): "
                     << t << endl;
}


void TheoryQuantifiers::notifyEq(TNode lhs, TNode rhs) {
  Debug("quantifiers-other") << "TheoryQuantifiers::notifyEq(): "
                     << lhs << " = " << rhs << endl;

}

void TheoryQuantifiers::preRegisterTerm(TNode n) {
  Debug("quantifiers-prereg") << "TheoryQuantifiers::preRegisterTerm() " << n << endl;
  if( n.getKind()==FORALL && !n.hasAttribute(InstConstantAttribute()) ){
    getQuantifiersEngine()->registerQuantifier( n );
  }
}


void TheoryQuantifiers::presolve() {
  Debug("quantifiers-presolve") << "TheoryQuantifiers::presolve()" << endl;
}


void TheoryQuantifiers::collectModelInfo( TheoryModel* m, bool fullModel ){

}

void TheoryQuantifiers::check(Effort e) {
  CodeTimer codeTimer(d_theoryTime);

  Debug("quantifiers-check") << "quantifiers::check(" << e << ")" << std::endl;
  while(!done()) {
    Node assertion = get();
    Debug("quantifiers-assert") << "quantifiers::assert(): " << assertion << std::endl;
    getQuantifiersEngine()->assertFact( assertion );
  }
  // call the quantifiers engine to check
  getQuantifiersEngine()->check( e );
}

void TheoryQuantifiers::propagate(Effort level){

}

Node TheoryQuantifiers::getNextDecisionRequest(){
  return getQuantifiersEngine()->getNextDecisionRequest();
}

bool TheoryQuantifiers::flipDecision(){
  //Debug("quantifiers-flip") << "No instantiation given, flip decision, level = " << d_valuation.getDecisionLevel() << std::endl;
  //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
  //  Debug("quantifiers-flip") << "   " << d_valuation.getDecision( i ) << std::endl;
  //}
  //if( d_valuation.getDecisionLevel()>0 ){
  //  double r = double(rand())/double(RAND_MAX);
  //  unsigned decisionLevel = (unsigned)(r*d_valuation.getDecisionLevel());
  //  d_out->flipDecision( decisionLevel );
  //  return true;
  //}else{
  //  return false;
  //}

  if( !d_out->flipDecision() ){
    return restart();
  }
  return true;
}

bool TheoryQuantifiers::restart(){
  static const int restartLimit = 0;
  if( d_numRestarts==restartLimit ){
    Debug("quantifiers-flip") << "No more restarts." << std::endl;
    return false;
  }else{
    d_numRestarts++;
    Debug("quantifiers-flip") << "Do restart." << std::endl;
    return true;
  }
}

void TheoryQuantifiers::setUserAttribute( std::string& attr, Node n ){
  QuantifiersAttributes::setUserAttribute( attr, n );
}

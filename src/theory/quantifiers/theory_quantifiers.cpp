/*********************                                                        */
/*! \file theory_quantifiers.cpp
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
 ** \brief Implementation of the theory of quantifiers
 **
 ** Implementation of the theory of quantifiers.
 **/


#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/valuation.h"
#include "theory/instantiation_engine.h"
#include "expr/kind.h"
#include "util/Assert.h"
#include <map>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

TheoryQuantifiers::TheoryQuantifiers(Context* c, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_QUANTIFIERS, c, out, valuation),
  d_forall_asserts(c),
  d_exists_asserts(c),
  d_counterexample_asserts(c){

}


TheoryQuantifiers::~TheoryQuantifiers() {
}

void TheoryQuantifiers::addSharedTerm(TNode t) {
  Debug("quantifiers") << "TheoryQuantifiers::addSharedTerm(): "
                     << t << endl;
}


void TheoryQuantifiers::notifyEq(TNode lhs, TNode rhs) {
  Debug("quantifiers") << "TheoryQuantifiers::notifyEq(): "
                     << lhs << " = " << rhs << endl;
  
}

void TheoryQuantifiers::preRegisterTerm(TNode n) {  
  Debug("quantifiers-prereg") << "TheoryQuantifiers::preRegisterTerm() " << n << endl;
}


void TheoryQuantifiers::presolve() {
  Debug("quantifiers") << "TheoryQuantifiers::presolve()" << endl;
}

Node TheoryQuantifiers::getValue(TNode n) {
  //NodeManager* nodeManager = NodeManager::currentNM();
  switch(n.getKind()) {
  default:
    Unhandled(n.getKind());
  }
}

void TheoryQuantifiers::check(Effort e) {
  Debug("quantifiers") << "quantifiers::check(" << e << ")" << std::endl;
  while(!done()) {
    Node assertion = get();
    Debug("quantifiers") << "quantifiers::check(): " << assertion << std::endl;
    switch(assertion.getKind()) {
    case kind::FORALL:
      assertUniversal( assertion );
      break;
    case kind::EXISTS:
      assertExistential( assertion );
      break;
    case kind::NO_COUNTEREXAMPLE:
      assertCounterexample( assertion );
      break;
    case kind::NOT:
      {
        switch( assertion[0].getKind()) {
        case kind::FORALL:
          assertExistential( assertion );
          break;
        case kind::EXISTS:
          assertUniversal( assertion );
          break;
        case kind::NO_COUNTEREXAMPLE:
          assertCounterexample( assertion );
          break;
        default:
          Unhandled(assertion[0].getKind());
          break;
        }
      }
      break;
    default:
      Unhandled(assertion.getKind());
      break;
    }
  }
  if( e == FULL_EFFORT ) {
    bool quantActive = false;
    //for each n in d_forall_asserts, 
    // such that NO_COUNTEREXAMPLE( n ) is not in positive in d_counterexample_asserts
    for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
      if( (*i).second ) {
        Node n = (*i).first;
        if( d_counterexample_asserts.find( n )==d_counterexample_asserts.end() ||
            !d_counterexample_asserts[n] ){   //DO_THIS: make sure that NO_COUNTEREXAMPLE is not a decision
          quantActive = true;
        }
      }
    }
    if( quantActive && !d_instEngine->doInstantiation( d_out ) ){
      //instantiation did not add a lemma to d_out

      //flip a previous decision? DO_THIS

      Debug("quantifiers") << "Return unknown." << std::endl;
      d_out->setIncomplete();
    }
  }
}

Node TheoryQuantifiers::getCounterexampleLiteralFor( Node n ){
  Assert( n.getKind()==FORALL || ( n.getKind()==NOT && n[0].getKind()==EXISTS ) );
  if( d_counterexamples.find( n )==d_counterexamples.end() ){
    d_counterexamples[n] = NodeManager::currentNM()->mkNode( NO_COUNTEREXAMPLE, n );
  }
  return d_counterexamples[n];
}

void TheoryQuantifiers::assertUniversal( Node n ){
  if( d_abstract_inst.find( n )==d_abstract_inst.end() ){
    //counterexample instantiate, add lemma
    std::vector< Node > vars;
    std::vector< Node > inst_constants;
    d_instEngine->getInstantiationConstantsFor( n, vars, inst_constants );
    Node quant = ( n.getKind()==kind::NOT ? n[0] : n );
    Node body = quant[ quant.getNumChildren() - 1 ].substitute( vars.begin(), vars.end(), 
                                                                inst_constants.begin(), inst_constants.end() ); 
    Node cel = getCounterexampleLiteralFor( n );

    NodeBuilder<> nb(kind::OR);
    nb << ( n.getKind()==kind::NOT ? n[0] : NodeManager::currentNM()->mkNode( NOT, n ) ) << cel;
    nb << ( n.getKind()==kind::NOT ? body : NodeManager::currentNM()->mkNode( NOT, body ) );
    Node lem = nb;
    Debug("quantifiers") << "Counterexample instantiation lemma : " << lem << std::endl;
    d_out->lemma( lem );

    //mark all literals in the body of n as dependent on cel
    markLiteralsAsDependent( body, n, cel );
    //mark cel as dependent on n
    //d_out->dependentDecision( cel, quant);
    //require any decision on cel to be phase=false
    d_out->requirePhase( cel, false );


    d_abstract_inst[n] = true;
  }
  d_forall_asserts[n] = true;
}

void TheoryQuantifiers::assertExistential( Node n ){
  if( d_skolemized.find( n )==d_skolemized.end() ){
    //skolemize, add lemma
    std::vector< Node > vars;
    std::vector< Node > skolems;
    Node quant = ( n.getKind()==kind::NOT ? n[0] : n );
    for( int i=0; i<(int)quant.getNumChildren()-1; i++ ){
      vars.push_back( quant[i] );
      skolems.push_back( NodeManager::currentNM()->mkInstConstant( quant[i].getType() ) );
    }
    Node body = quant[ quant.getNumChildren() - 1 ].substitute( vars.begin(), vars.end(), 
                                                                skolems.begin(), skolems.end() );
    NodeBuilder<> nb(kind::OR);
    nb << ( n.getKind()==kind::NOT ? n[0] : NodeManager::currentNM()->mkNode( NOT, n ) );
    nb << ( n.getKind()==kind::NOT ? NodeManager::currentNM()->mkNode( NOT, body ) : body );
    Node lem = nb;
    Debug("quantifiers") << "Skolemize lemma : " << lem << std::endl;
    d_out->lemma( lem );

    d_skolemized[n] = true;
  }
  d_exists_asserts[n] = true;
}

void TheoryQuantifiers::assertCounterexample( Node n ){
  if( n.getKind()==NO_COUNTEREXAMPLE ){
    Debug("quantifiers") << n << " is valid in current context!" << std::endl;
    d_counterexample_asserts[ n[0] ] = true;
  }else{
    Assert( n.getKind()==NOT );
    d_counterexample_asserts[ n[0][0] ] = false;
  }
}

bool TheoryQuantifiers::markLiteralsAsDependent( Node n, Node f, Node cel )
{
  if( n.getKind()==INST_CONSTANT ){
    InstantitionConstantAttribute icai;
    n.setAttribute(icai,f);
    return true;
  }else{
    bool retVal = false;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( markLiteralsAsDependent( n[i], f, cel ) ){
        retVal = true;
      }
    }
    if( retVal ){
      //set n to have instantiation constants from f
      InstantitionConstantAttribute icai;
      n.setAttribute(icai,f);
      if( d_valuation.isSatLiteral( n ) ){
        Debug("quantifiers-ce") << "Make " << n << " dependent on " << cel << std::endl;
        d_out->dependentDecision( cel, n );
      }
    }
    return retVal;
  }
}

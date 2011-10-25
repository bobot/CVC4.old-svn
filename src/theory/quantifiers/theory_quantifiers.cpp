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
#include "theory/quantifiers/theory_quantifiers_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

TheoryQuantifiers::TheoryQuantifiers(Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_QUANTIFIERS, c, u, out, valuation),
  d_forall_asserts(c),
  d_exists_asserts(c),
  d_counterexample_asserts(c),
  d_numInstantiations(c,0),
  d_numRestarts(0){

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
}


void TheoryQuantifiers::presolve() {
  Debug("quantifiers-other") << "TheoryQuantifiers::presolve()" << endl;
}

Node TheoryQuantifiers::getValue(TNode n) {
  //NodeManager* nodeManager = NodeManager::currentNM();
  switch(n.getKind()) {
  case FORALL:
  case EXISTS:
  case NO_COUNTEREXAMPLE:
    bool value;
    if( d_valuation.hasSatValue( n, value ) ){
      return NodeManager::currentNM()->mkConst(value);
    }else{
      return NodeManager::currentNM()->mkConst(false);  //FIX_THIS?
    }
    break;
  default:
    Unhandled(n.getKind());
  }
}

void TheoryQuantifiers::check(Effort e) {
  Debug("quantifiers-check") << "quantifiers::check(" << e << ")" << std::endl;
  while(!done()) {
    Node assertion = get();
    Debug("quantifiers-check") << "quantifiers::check(): " << assertion << std::endl;
    switch(assertion.getKind()) {
    case kind::FORALL:
      assertUniversal( assertion );
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
    if( getInstantiator() ){
      getInstantiator()->check( assertion );
    }
  }
  if( e == FULL_EFFORT ) {
    Debug("quantifiers") << "quantifiers: FULL_EFFORT check" << std::endl;
    bool quantActive = false;
    //for each n in d_forall_asserts, 
    // such that NO_COUNTEREXAMPLE( n ) is not in positive in d_counterexample_asserts
    for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
      if( (*i).second ) {
        Node n = (*i).first;
        Node cel = d_instEngine->getCounterexampleLiteralFor( n );
        bool active, value;
        bool ceValue = false;
        if( d_valuation.hasSatValue( cel, value ) ){
          active = !value;
          ceValue = true;
        }else{
          //this should only happen if we have a set of ground terms that suffices 
          // to show the negation of the body of n
          active = true;
        }
        d_instEngine->setActive( n, active );
        if( active ){
          Debug("quantifiers") << "  Active : " << n;
          quantActive = true;
        }else{
          Debug("quantifiers") << "  NOT active : " << n;
          //note that NO_COUNTEREXAMPLE must not be a decision
        }
        if( d_valuation.hasSatValue( n, value ) ){
          Debug("quantifiers") << ", value = " << value; 
        }
        if( ceValue ){
          Debug("quantifiers") << ", ce is asserted";
        }
        Debug("quantifiers") << std::endl;
      }
    }
    if( quantActive ){  
      static bool enableLimit = true;
      static int limitInst = 20;
      bool doInst = true;
      if( enableLimit && d_numInstantiations.get()==limitInst ){
        Debug("quantifiers") << "Give up in current branch." << std::endl;
        doInst = false;
      }

      if( doInst && d_instEngine->doInstantiation( d_out ) ){
        d_numInstantiations.set( d_numInstantiations.get() + 1 );
        //Debug("quantifiers") << "Done instantiation " << d_numInstantiations.get() << "." << std::endl;
      }else{
        std::cout << "unknown" << std::endl;
        exit( 7 );
        Debug("quantifiers") << "No instantiation given." << std::endl;
        if( d_instEngine->getStatus()==Instantiator::STATUS_UNKNOWN ){
#if 1
          d_out->setIncomplete();
#else
          //instantiation did not add a lemma to d_out, try to flip a previous decision
          if( !d_out->flipDecision() ){
            //maybe restart?
            static int restartLimit = 1;
            if( d_numRestarts==restartLimit ){
              Debug("quantifiers") << "Return unknown." << std::endl;
              d_out->setIncomplete();
            }else{
              d_numRestarts++;
              Debug("quantifiers") << "Do restart." << std::endl;
            }
          }else{
            Debug("quantifiers") << "Flipped decision." << std::endl;
          }
#endif
        }
      }
    }else{
      Debug("quantifiers") << "No quantifier is active." << std::endl;
    }
  }
}

void TheoryQuantifiers::assertUniversal( Node n ){
  Assert( n.getKind()==FORALL );
  if( !n.hasAttribute(InstConstantAttribute()) ){
    if( d_abstract_inst.find( n )==d_abstract_inst.end() ){
      //counterexample instantiate, add lemma
      std::vector< Node > inst_constants;
      Node body;
      d_instEngine->getInstantiationConstantsFor( n, inst_constants, body );
      //get the counterexample literal
      Node cel = d_instEngine->getCounterexampleLiteralFor( n );

      NodeBuilder<> nb(kind::OR);
      nb << n.notNode() << cel << body.notNode();
      Node lem = nb;
      Debug("quantifiers") << "Counterexample instantiation lemma : " << lem << std::endl;
      d_out->lemma( lem );

      //mark all literals in the body of n as dependent on cel
      d_instEngine->registerLiterals( body, n, d_out );

      ////mark cel as dependent on n
      //Node quant = ( n.getKind()==kind::NOT ? n[0] : n );
      //Debug("quant-dep-dec") << "Make " << cel << " dependent on " << quant << std::endl;
      //d_out->dependentDecision( quant, cel );    //FIXME?

      //require any decision on cel to be phase=false
      d_out->requirePhase( cel, false );

      d_abstract_inst[n] = true;
    }
    d_forall_asserts[n] = true;
  }
}

void TheoryQuantifiers::assertExistential( Node n ){
  Assert( n.getKind()== NOT && n[0].getKind()==FORALL );
  if( !n[0].hasAttribute(InstConstantAttribute()) ){
    if( d_skolemized.find( n )==d_skolemized.end() ){
      //skolemize, add lemma
      std::vector< Node > vars;
      d_instEngine->getVariablesFor( n, vars );
      std::vector< Node > skolems;
      d_instEngine->getSkolemConstantsFor( n, skolems );
      Node body = n[0][ n[0].getNumChildren() - 1 ].substitute( vars.begin(), vars.end(), 
                                                                skolems.begin(), skolems.end() );
      NodeBuilder<> nb(kind::OR);
      nb << n[0] << body.notNode();
      Node lem = nb;
      Debug("quantifiers-sk") << "Skolemize lemma : " << lem << std::endl;
      d_out->lemma( lem );

      d_skolemized[n] = true;
    }
    d_exists_asserts[n] = true;
  }
}

void TheoryQuantifiers::assertCounterexample( Node n ){
  if( n.getKind()==NO_COUNTEREXAMPLE ){
    Debug("quantifiers") << n[0] << " is valid in current context." << std::endl;
    d_counterexample_asserts[ n[0] ] = true;
  }else{
    Assert( n.getKind()==NOT );
    d_counterexample_asserts[ n[0][0] ] = false;
  }
}

Instantiator* TheoryQuantifiers::makeInstantiator(){
  Debug("quant-quant") << "Make Quantifiers instantiator" << endl;
  return new InstantiatorTheoryQuantifiers( getContext(), d_instEngine, this );
}

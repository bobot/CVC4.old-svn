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
#include <time.h>
#include "theory/quantifiers/theory_quantifiers_instantiator.h"

//#define USE_FLIP_DECISION

static bool clockSet = false;
double initClock;

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

static bool enableLimit = false; 
static int limitInst = 20;

TheoryQuantifiers::TheoryQuantifiers(Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_QUANTIFIERS, c, u, out, valuation),
  d_forall_asserts(c),
  d_exists_asserts(c),
  d_counterexample_asserts(c),
  d_numRestarts(0){
  d_numInstantiations = 0;
  d_baseDecLevel = -1;
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
  //if( n.getKind()==FORALL ){
  //  d_out->requirePhase( n, false );
  //}
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
    Debug("quantifiers-assert") << "quantifiers::assert(): " << assertion << std::endl;
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
    fullEffortCheck();
  }
}

void TheoryQuantifiers::assertUniversal( Node n ){
  Assert( n.getKind()==FORALL );
  if( !n.hasAttribute(InstConstantAttribute()) ){
    if( d_abstract_inst.find( n )==d_abstract_inst.end() ){
      d_instEngine->registerQuantifier( n, d_out, d_valuation );
      NodeBuilder<> nb(kind::OR);
      nb << n << d_instEngine->getCounterexampleLiteralFor( n );
      Node lem = nb;
      Debug("quantifiers") << "Counterexample instantiation lemma : " << lem << std::endl;
      d_out->lemma( lem );

      ////mark cel as dependent on n
      //Node quant = ( n.getKind()==kind::NOT ? n[0] : n );
      //Debug("quant-dep-dec") << "Make " << cel << " dependent on " << quant << std::endl;
      //d_out->dependentDecision( quant, cel );    //FIXME?

      d_abstract_inst[n] = true;
    }
    d_forall_asserts[n] = true;
  }
}

void TheoryQuantifiers::assertExistential( Node n ){
  Assert( n.getKind()== NOT && n[0].getKind()==FORALL );
  if( !n[0].hasAttribute(InstConstantAttribute()) ){
    if( d_skolemized.find( n )==d_skolemized.end() ){
      Node body = d_instEngine->getSkolemizedBody( n[0] );
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

bool TheoryQuantifiers::flipDecision(){
#ifndef USE_FLIP_DECISION
  return false;
#else
  Debug("quantifiers-flip") << "No instantiation given, flip decision, level = " << d_valuation.getDecisionLevel() << std::endl;
  //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
  //  Debug("quantifiers-flip") << "   " << d_valuation.getDecision( i ) << std::endl;
  //}
  if( enableLimit && d_numInstantiations==limitInst ){
    if( d_baseDecLevel>0 ){
      d_out->flipDecision( (unsigned int)d_baseDecLevel );
    }
    d_baseDecLevel = -1;
  }else{
    if( !d_out->flipDecision() ){
      return restart();
    }
  }
  return true;
#endif
}

bool TheoryQuantifiers::restart(){
  static int restartLimit = 1;
  if( d_numRestarts==restartLimit ){
    Debug("quantifiers-flip") << "No more restarts." << std::endl;
    return false;
  }else{
    d_numRestarts++;
    Debug("quantifiers-flip") << "Do restart." << std::endl;
    return true;
  }
}

void TheoryQuantifiers::fullEffortCheck(){
  if( !clockSet ){
    initClock = double(clock())/double(CLOCKS_PER_SEC);
    clockSet = true;
  }else{
    double currClock = double(clock())/double(CLOCKS_PER_SEC);
    if( currClock-initClock>10 ){
      NodeManager::currentNM()->getStatisticsRegistry()->flushStatistics(std::cout);
      exit( 55 );
    }
  }

  if( d_baseDecLevel==-1 || (int)d_valuation.getDecisionLevel()<d_baseDecLevel){
    d_baseDecLevel = d_valuation.getDecisionLevel();
    d_numInstantiations = 0;
  }
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
        active = value;
        ceValue = true;
      }else{
        active = true;
      }
      d_instEngine->setActive( n, active );
      if( active ){
        Debug("quantifiers") << "  Active : " << n;
        quantActive = true;
      }else{
        Debug("quantifiers") << "  NOT active : " << n;
        if( d_valuation.isDecision( cel ) ){
          Debug("quant-req-phase") << "Bad decision : " << cel << std::endl;
        }
        //note that the counterexample literal must not be a decision
        Assert( !d_valuation.isDecision( cel ) );
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
    //std::cout << "unknown ";
    //exit( 9 );
    if( enableLimit && d_numInstantiations==limitInst ){
      Debug("quantifiers-flip") << "Give up in current branch. " << d_valuation.getDecisionLevel() << " " << d_baseDecLevel << std::endl;
    }else{
#if 0
      d_out->setIncomplete();
      return;
#endif
      Debug("quantifiers") << "Do instantiation, level = " << d_valuation.getDecisionLevel() << std::endl;
      //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
      //  Debug("quantifiers-dec") << "   " << d_valuation.getDecision( i ) << std::endl;
      //}
      if( d_instEngine->doInstantiationRound( d_out ) ){
        d_numInstantiations++;
        Debug("quantifiers") << "Done instantiation " << d_numInstantiations << "." << std::endl;
      }else{
        Debug("quantifiers") << "No instantiation given, returning unknown..." << std::endl;
        //if( d_instEngine->getStatus()==Instantiator::STATUS_UNKNOWN ){
        d_out->setIncomplete();
        //}

        //code for flip decision used to go here....(but it needs to be done after sharing)
        ////if( d_instEngine->getStatus()==Instantiator::STATUS_UNKNOWN ){
        //  //instantiation did not add a lemma to d_out, try to flip a previous decision
        //  if( !flipDecision() ){
        //    //maybe restart?
        //    restart();
        //  }else{
        //    Debug("quantifiers") << "Flipped decision." << std::endl;
        //  }
        ////}
      } 
    }
  }else{
    //debugging
    Debug("quantifiers-sat") << "Decisions:" << std::endl;
    for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
      Debug("quantifiers-sat") << "   " << i << ": " << d_valuation.getDecision( i ) << std::endl;
    }
    for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
      if( (*i).second ) {
        Node cel = d_instEngine->getCounterexampleLiteralFor( (*i).first );
        bool value;
        if( d_valuation.hasSatValue( cel, value ) ){
          if( !value ){
            if( d_valuation.isDecision( cel ) ){
              Debug("quantifiers-sat") << "sat, but decided cel=" << cel << std::endl;
              std::cout << "unknown ";
              exit( 17 );
            }
          }
        }
      }
    }
    Debug("quantifiers-sat") << "No quantifier is active. " << d_valuation.getDecisionLevel() << std::endl;
    //static bool setTrust = false;
    //if( !setTrust ){
    //  setTrust = true;
    //  std::cout << "trust-";
    //}
    //debugging-end
  }
}

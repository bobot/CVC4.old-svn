#include "theory/quantifiers/instantiation_engine.h"

#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

//static bool clockSet = false;
//double initClock;

InstantiationEngine::InstantiationEngine( TheoryQuantifiers* th ) : 
d_th( th ), d_forall_asserts( d_th->getContext() ){

}

QuantifiersEngine* InstantiationEngine::getQuantifiersEngine(){
  return d_th->getQuantifiersEngine();
}

bool InstantiationEngine::doInstantiationRound(){
  Debug("inst-engine") << "IE: Reset instantiation." << std::endl;
  //reset instantiators
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( getQuantifiersEngine()->getInstantiator( i ) ){
      getQuantifiersEngine()->getInstantiator( i )->resetInstantiationRound();
      getQuantifiersEngine()->getInstantiator( i )->resetInstantiationStrategies();
    }
  }
  int e = 0;
  d_status = InstStrategy::STATUS_UNFINISHED;
  while( d_status==InstStrategy::STATUS_UNFINISHED ){
    Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    //std::cout << "IE: Prepare instantiation (" << e << ")." << std::endl; 
    d_status = InstStrategy::STATUS_SAT;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( getQuantifiersEngine()->getInstantiator( i ) ){
        Debug("inst-engine-debug") << "Do " << getQuantifiersEngine()->getInstantiator( i )->identify() << " " << e << std::endl;
        //std::cout << "Do " << d_instTable[i]->identify() << " " << e << std::endl;
        getQuantifiersEngine()->getInstantiator( i )->doInstantiation( e );
        Debug("inst-engine-debug") << " -> status is " << getQuantifiersEngine()->getInstantiator( i )->getStatus() << std::endl;
        //std::cout << " -> status is " << d_instTable[i]->getStatus() << std::endl;
        InstStrategy::updateStatus( d_status, getQuantifiersEngine()->getInstantiator( i )->getStatus() );
      }
    }
    if( getQuantifiersEngine()->hasAddedLemma() ){
      d_status = InstStrategy::STATUS_UNKNOWN;
    }
    e++;
  }
  Debug("inst-engine") << "All instantiators finished, # added lemmas = ";
  Debug("inst-engine") << (int)getQuantifiersEngine()->d_lemmas_waiting.size() << std::endl;
  //std::cout << "All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
  if( !getQuantifiersEngine()->hasAddedLemma() ){
    Debug("inst-engine-stuck") << "No instantiations produced at this state: " << std::endl;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( getQuantifiersEngine()->getInstantiator( i ) ){
        getQuantifiersEngine()->getInstantiator( i )->debugPrint("inst-engine-stuck");
        Debug("inst-engine-stuck") << std::endl;
      }
    }
    return false;
  }else{
    getQuantifiersEngine()->flushLemmas( &d_th->getOutputChannel() );
    return true;
  }
}

void InstantiationEngine::check( Theory::Effort e ){
  if( e==Theory::FULL_EFFORT ){
    //  if( !clockSet ){
    //    initClock = double(clock())/double(CLOCKS_PER_SEC);
    //    clockSet = true;
    //  }else{
    //    double currClock = double(clock())/double(CLOCKS_PER_SEC);
    //    if( currClock-initClock>10 ){
    //      NodeManager::currentNM()->getStatisticsRegistry()->flushStatistics(std::cout);
    //      exit( 55 );
    //    }
    //  }

    Debug("quantifiers") << "quantifiers: FULL_EFFORT check" << std::endl;
    bool quantActive = false;
    //for each n in d_forall_asserts, 
    // such that the counterexample literal is not in positive in d_counterexample_asserts
    for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
      if( (*i).second ) {
        Node n = (*i).first;
        Node cel = getQuantifiersEngine()->getCounterexampleLiteralFor( n );
        bool active, value;
        bool ceValue = false;
        if( d_th->getValuation().hasSatValue( cel, value ) ){
          active = value;
          ceValue = true;
        }else{
          active = true;
        }
        getQuantifiersEngine()->setActive( n, active );
        if( active ){
          Debug("quantifiers") << "  Active : " << n;
          quantActive = true;
        }else{
          Debug("quantifiers") << "  NOT active : " << n;
          if( d_th->getValuation().isDecision( cel ) ){
            Debug("quant-req-phase") << "Bad decision : " << cel << std::endl;
          }
          //note that the counterexample literal must not be a decision
          Assert( !d_th->getValuation().isDecision( cel ) );
        }
        if( d_th->getValuation().hasSatValue( n, value ) ){
          Debug("quantifiers") << ", value = " << value; 
        }
        if( ceValue ){
          Debug("quantifiers") << ", ce is asserted";
        }
        Debug("quantifiers") << std::endl;
      }
    }
    if( quantActive ){  
      Debug("quantifiers") << "Do instantiation, level = " << d_th->getValuation().getDecisionLevel() << std::endl;
      //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
      //  Debug("quantifiers-dec") << "   " << d_valuation.getDecision( i ) << std::endl;
      //}
      if( doInstantiationRound() ){
        //d_numInstantiations++;
        //Debug("quantifiers") << "Done instantiation " << d_numInstantiations << "." << std::endl;
      }else{
        Debug("quantifiers") << "No instantiation given, returning unknown..." << std::endl;
        //if( getQuantifiersEngine()->getStatus()==Instantiator::STATUS_UNKNOWN ){
        d_th->getOutputChannel().setIncomplete();
        //}
      }
    }else{
      debugSat();
    }
  }
}

void InstantiationEngine::registerQuantifier( Node f ){
  if( !TheoryQuantifiers::isRewriteKind( f[1].getKind() ) ){
    //code for counterexample-based quantifier instantiation
    Node ceBody = f[1].substitute( getQuantifiersEngine()->d_vars[f].begin(), getQuantifiersEngine()->d_vars[f].end(),
                                   getQuantifiersEngine()->d_inst_constants[f].begin(), 
                                   getQuantifiersEngine()->d_inst_constants[f].end() );
    getQuantifiersEngine()->d_counterexample_body[ f ] = ceBody;
    //get the counterexample literal
    Node ceLit = d_th->getValuation().ensureLiteral( ceBody.notNode() );
    getQuantifiersEngine()->d_ce_lit[ f ] = ceLit;
    Debug("quantifiers") << ceLit << " is the ce literal for " << f << std::endl;
    // set attributes, mark all literals in the body of n as dependent on cel
    registerLiterals( ceLit, f );
    computePhaseReqs( ceBody, false );
    //require any decision on cel to be phase=true
    d_th->getOutputChannel().requirePhase( ceLit, true );
    Debug("quant-req-phase") << "Require phase " << ceLit << " = true." << std::endl;
    //add counterexample lemma
    NodeBuilder<> nb(kind::OR);
    nb << f << ceLit;
    Node lem = nb;
    Debug("quantifiers") << "Counterexample lemma : " << lem << std::endl;
    d_th->getOutputChannel().lemma( lem );
    ////mark cel as dependent on n?
    //Node quant = ( n.getKind()==kind::NOT ? n[0] : n );
    //Debug("quant-dep-dec") << "Make " << cel << " dependent on " << quant << std::endl;
    //d_out->dependentDecision( quant, cel );

    //take into account user patterns
    if( f.getNumChildren()==3 ){
      Node subsPat = getQuantifiersEngine()->getSubstitutedNode( f[2], f );
      //add patterns
      for( int i=0; i<(int)subsPat.getNumChildren(); i++ ){
        //std::cout << "Add pattern " << subsPat[i] << " for " << f << std::endl;
        ((uf::InstantiatorTheoryUf*)getQuantifiersEngine()->getInstantiator( theory::THEORY_UF ))->addUserPattern( f, subsPat[i] );
      }
    }
  }
}

void InstantiationEngine::assertNode( Node n ){
  if( !TheoryQuantifiers::isRewriteKind( n[1].getKind() ) ){
    d_forall_asserts[n] = true;
  }
}
















void InstantiationEngine::registerLiterals( Node n, Node f ){
  if( !n.hasAttribute(InstConstantAttribute()) ){
    bool setAttr = false;
    if( n.getKind()==INST_CONSTANT ){
      setAttr = true;
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        registerLiterals( n[i], f );
        if( n[i].hasAttribute(InstConstantAttribute()) ){
          setAttr = true;
        }
      }
    }
    if( setAttr ){
      if( getQuantifiersEngine()->d_te->getPropEngine()->isSatLiteral( n ) && n.getKind()!=NOT ){
        if( n!=getQuantifiersEngine()->d_ce_lit[f] && n.notNode()!=getQuantifiersEngine()->d_ce_lit[f] ){
          Debug("quant-dep-dec") << "Make " << n << " dependent on " << getQuantifiersEngine()->d_ce_lit[f] << std::endl;
          d_th->getOutputChannel().dependentDecision( getQuantifiersEngine()->d_ce_lit[f], n );
        }
      }
      InstConstantAttribute ica;
      n.setAttribute(ica,f);
    }
  }
}

void InstantiationEngine::computePhaseReqs( Node n, bool polarity ){
  bool newReqPol = false;
  bool newPolarity;
  getQuantifiersEngine()->d_phase_reqs[n] = polarity;
  if( n.getKind()==NOT ){
    newReqPol = true;
    newPolarity = !polarity;
  }else if( n.getKind()==OR || n.getKind()==IMPLIES ){
    if( !polarity ){
      newReqPol = true;
      newPolarity = false;
    }
  }else if( n.getKind()==AND ){
    if( polarity ){
      newReqPol = true;
      newPolarity = true;
    }
  }
  if( newReqPol ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n.getKind()==IMPLIES && i==0 ){
        computePhaseReqs( n[i], !newPolarity );
      }else{
        computePhaseReqs( n[i], newPolarity );
      }
    }
  }
}


void InstantiationEngine::debugSat(){
  //debugging
  Debug("quantifiers-sat") << "Decisions:" << std::endl;
  for( int i=1; i<=(int)d_th->getValuation().getDecisionLevel(); i++ ){
    Debug("quantifiers-sat") << "   " << i << ": " << d_th->getValuation().getDecision( i ) << std::endl;
  }
  for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
    if( (*i).second ) {
      Node cel = getQuantifiersEngine()->getCounterexampleLiteralFor( (*i).first );
      bool value;
      if( d_th->getValuation().hasSatValue( cel, value ) ){
        if( !value ){
          if( d_th->getValuation().isDecision( cel ) ){
            Debug("quantifiers-sat") << "sat, but decided cel=" << cel << std::endl;
            std::cout << "unknown ";
            exit( 17 );
          }
        }
      }
    }
  }
  Debug("quantifiers-sat") << "No quantifier is active. " << d_th->getValuation().getDecisionLevel() << std::endl;
  //static bool setTrust = false;
  //if( !setTrust ){
  //  setTrust = true;
  //  std::cout << "trust-";
  //}
  //debugging-end
}

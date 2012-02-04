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
  //InstMatchGenerator::resetInstantiationRoundAll( (uf::InstantiatorTheoryUf*)d_instTable[theory::THEORY_UF] );
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
        //update status
        InstStrategy::updateStatus( d_status, getQuantifiersEngine()->getInstantiator( i )->getStatus() );
      }
    }
    if( !getQuantifiersEngine()->d_lemmas_waiting.empty() ){
      d_status = InstStrategy::STATUS_UNKNOWN;
    }
    e++;
  }
  Debug("inst-engine") << "All instantiators finished, # added lemmas = " << (int)getQuantifiersEngine()->d_lemmas_waiting.size() << std::endl;
  //std::cout << "All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
  if( getQuantifiersEngine()->d_lemmas_waiting.empty() ){
    Debug("inst-engine-stuck") << "No instantiations produced at this state: " << std::endl;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( getQuantifiersEngine()->getInstantiator( i ) ){
        getQuantifiersEngine()->getInstantiator( i )->debugPrint("inst-engine-stuck");
        Debug("inst-engine-stuck") << std::endl;
      }
    }
    return false;
  }else{
    for( int i=0; i<(int)getQuantifiersEngine()->d_lemmas_waiting.size(); i++ ){
      d_th->getOutputChannel().lemma( getQuantifiersEngine()->d_lemmas_waiting[i] );
    }
    getQuantifiersEngine()->d_lemmas_waiting.clear();
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
    // such that NO_COUNTEREXAMPLE( n ) is not in positive in d_counterexample_asserts
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

        //code for flip decision used to go here....(but it needs to be done after sharing)
        ////if( getQuantifiersEngine()->getStatus()==Instantiator::STATUS_UNKNOWN ){
        //  //instantiation did not add a lemma to d_out, try to flip a previous decision
        //  if( !flipDecision() ){
        //    //maybe restart?
        //    restart();
        //  }else{
        //    Debug("quantifiers") << "Flipped decision." << std::endl;
        //  }
        ////}
      }
    }else{
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
  }
}

void InstantiationEngine::registerQuantifier( Node f ){
  if( !TheoryQuantifiers::isRewriteKind( f[1].getKind() ) ){
    if( getQuantifiersEngine()->d_counterexample_body.find( f )==getQuantifiersEngine()->d_counterexample_body.end() ){
      for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
        Node ic = NodeManager::currentNM()->mkInstConstant( f[0][i].getType() );
        getQuantifiersEngine()->d_inst_constants_map[ic] = f;
        getQuantifiersEngine()->d_inst_constants[ f ].push_back( ic );
      }
      std::vector< Node > vars;
      getQuantifiersEngine()->getVariablesFor( f, vars );
      getQuantifiersEngine()->d_counterexample_body[ f ] = f[ 1 ].substitute( getQuantifiersEngine()->d_vars[f].begin(), getQuantifiersEngine()->d_vars[f].end(), 
                                                            getQuantifiersEngine()->d_inst_constants[ f ].begin(), getQuantifiersEngine()->d_inst_constants[ f ].end() ); 

      //get the counterexample literal
      getQuantifiersEngine()->d_ce_lit[ f ] = d_th->getValuation().ensureLiteral( getQuantifiersEngine()->d_counterexample_body[ f ].notNode() );
      Debug("quantifiers") << getQuantifiersEngine()->d_ce_lit[ f ] << " is the ce literal for " << f << std::endl;

      // set attributes, mark all literals in the body of n as dependent on cel
      registerTerm( getQuantifiersEngine()->d_ce_lit[ f ], f );
      computePhaseReqs( getQuantifiersEngine()->d_counterexample_body[ f ], false );
      //require any decision on cel to be phase=true
      d_th->getOutputChannel().requirePhase( getQuantifiersEngine()->d_ce_lit[ f ], true );
      Debug("quant-req-phase") << "Require phase " << getQuantifiersEngine()->d_ce_lit[ f ] << " = true." << std::endl;

      //make the match generator
      if( f.getNumChildren()==3 ){
        //getCounterexampleBody( f );
        Node subsPat = f[2].substitute( getQuantifiersEngine()->d_vars[f].begin(), getQuantifiersEngine()->d_vars[f].end(), 
                                        getQuantifiersEngine()->d_inst_constants[ f ].begin(), getQuantifiersEngine()->d_inst_constants[ f ].end() ); 

        //add patterns
        for( int i=0; i<(int)subsPat.getNumChildren(); i++ ){
          registerTerm( subsPat[i], f );
          //std::cout << "Add pattern " << subsPat[i] << " for " << f << std::endl;
          ((uf::InstantiatorTheoryUf*)getQuantifiersEngine()->getInstantiator( theory::THEORY_UF ))->addUserPattern( f, subsPat[i] );
        }
      }
      NodeBuilder<> nb(kind::OR);
      nb << f << getQuantifiersEngine()->d_ce_lit[ f ];
      Node lem = nb;
      Debug("quantifiers") << "Counterexample instantiation lemma : " << lem << std::endl;
      d_th->getOutputChannel().lemma( lem );
      ////mark cel as dependent on n
      //Node quant = ( n.getKind()==kind::NOT ? n[0] : n );
      //Debug("quant-dep-dec") << "Make " << cel << " dependent on " << quant << std::endl;
      //d_out->dependentDecision( quant, cel );    //FIXME?
    }
  }
}

void InstantiationEngine::registerTerm( Node n, Node f ){
  if( !n.hasAttribute(InstConstantAttribute()) ){
    bool setAttr = false;
    if( n.getKind()==INST_CONSTANT ){
      setAttr = true;
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        registerTerm( n[i], f );
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

void InstantiationEngine::assertNode( Node n ){
  if( !TheoryQuantifiers::isRewriteKind( n[1].getKind() ) ){
    d_forall_asserts[n] = true;
  }
}

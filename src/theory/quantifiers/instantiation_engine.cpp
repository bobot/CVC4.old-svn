/*********************                                                        */
/*! \file instantiation_engine.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): bobot, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of instantiation engine class
 **/

#include "theory/quantifiers/instantiation_engine.h"

#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

InstantiationEngine::InstantiationEngine( QuantifiersEngine* qe, bool setIncomplete ) :
QuantifiersModule( qe ), d_setIncomplete( setIncomplete ), d_ierCounter( 0 ){

}


bool InstantiationEngine::doInstantiationRound( Theory::Effort effort ){
  //if counterexample-based quantifier instantiation is active
  if( options::cbqi() ){
    //check if any cbqi lemma has not been added yet
    bool addedLemma = false;
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( doCbqi( f ) && !hasAddedCbqiLemma( f ) ){
        d_added_cbqi_lemma[f] = true;
        Debug("cbqi") << "Do cbqi for " << f << std::endl;
        //add cbqi lemma
        //get the counterexample literal
        Node ceLit = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( f );
        //require any decision on cel to be phase=true
        d_quantEngine->getOutputChannel().requirePhase( ceLit, true );
        Debug("cbqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
        //add counterexample lemma
        NodeBuilder<> nb(kind::OR);
        nb << f << ceLit;
        Node lem = nb;
        Debug("cbqi-debug") << "Counterexample lemma : " << lem << std::endl;
        d_quantEngine->getOutputChannel().lemma( lem );
        addedLemma = true;
      }
    }
    if( addedLemma ){
      return true;
    }
  }
  //if not, proceed to instantiation round
  Debug("inst-engine") << "IE: Instantiation Round." << std::endl;
  Debug("inst-engine-ctrl") << "IE: Instantiation Round." << std::endl;
  //reset the quantifiers engine
  Debug("inst-engine-ctrl") << "Reset IE" << std::endl;
  d_quantEngine->resetInstantiationRound( effort );
  //iterate over an internal effort level e
  int e = 0;
  int eLimit = effort==Theory::EFFORT_LAST_CALL ? 10 : 2;
  d_inst_round_status = InstStrategy::STATUS_UNFINISHED;
  //while unfinished, try effort level=0,1,2....
  while( d_inst_round_status==InstStrategy::STATUS_UNFINISHED && e<=eLimit ){
    Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    d_inst_round_status = InstStrategy::STATUS_SAT;
    //instantiate each quantifier
    for( int q=0; q<d_quantEngine->getModel()->getNumAssertedQuantifiers(); q++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( q );
      Debug("inst-engine-debug") << "IE: Instantiate " << f << "..." << std::endl;
      //if this quantifier is active
      if( d_quant_active[ f ] ){
        //int e_use = d_quantEngine->getRelevance( f )==-1 ? e - 1 : e;
        int e_use = e;
        if( e_use>=0 ){
          //use each theory instantiator to instantiate f
          for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
            if( d_quantEngine->getInstantiator( i ) ){
              Debug("inst-engine-debug") << "Do " << d_quantEngine->getInstantiator( i )->identify() << " " << e_use << std::endl;
              int quantStatus = d_quantEngine->getInstantiator( i )->doInstantiation( f, effort, e_use );
              Debug("inst-engine-debug") << " -> status is " << quantStatus << std::endl;
              InstStrategy::updateStatus( d_inst_round_status, quantStatus );
            }
          }
        }
      }
    }
    //do not consider another level if already added lemma at this level
    if( d_quantEngine->hasAddedLemma() ){
      d_inst_round_status = InstStrategy::STATUS_UNKNOWN;
    }
    e++;
  }
  Debug("inst-engine") << "All instantiators finished, # added lemmas = ";
  Debug("inst-engine") << (int)d_quantEngine->d_lemmas_waiting.size() << std::endl;
  //Notice() << "All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
  if( !d_quantEngine->hasAddedLemma() ){
    Debug("inst-engine-stuck") << "No instantiations produced at this state: " << std::endl;
    for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
      if( d_quantEngine->getInstantiator( i ) ){
        d_quantEngine->getInstantiator( i )->debugPrint("inst-engine-stuck");
        Debug("inst-engine-stuck") << std::endl;
      }
    }
    Debug("inst-engine-ctrl") << "---Fail." << std::endl;
    return false;
  }else{
    Debug("inst-engine-ctrl") << "---Done. " << (int)d_quantEngine->d_lemmas_waiting.size() << std::endl;
    Trace("inst-engine") << "Added lemmas = " << (int)d_quantEngine->d_lemmas_waiting.size() << std::endl;
    //flush lemmas to output channel
    d_quantEngine->flushLemmas( &d_quantEngine->getOutputChannel() );
    return true;
  }
}

void InstantiationEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_FULL ){
    d_ierCounter++;
  }
  //determine if we should perform check, based on instWhenMode
  bool performCheck = false;
  if( options::instWhenMode()==INST_WHEN_FULL ){
    performCheck = ( e >= Theory::EFFORT_FULL );
  }else if( options::instWhenMode()==INST_WHEN_FULL_LAST_CALL ){
    performCheck = ( ( e==Theory::EFFORT_FULL  && d_ierCounter%2==0 ) || e==Theory::EFFORT_LAST_CALL );
  }else if( options::instWhenMode()==INST_WHEN_LAST_CALL ){
    performCheck = ( e >= Theory::EFFORT_LAST_CALL );
  }else{
    performCheck = true;
  }
  if( performCheck ){
    Debug("inst-engine") << "IE: Check " << e << " " << d_ierCounter << std::endl;
    double clSet = 0;
    if( Trace.isOn("inst-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "---Instantiation Engine Round, effort = " << e << "---" << std::endl;
    }
    bool quantActive = false;
    Debug("quantifiers") << "quantifiers:  check:  asserted quantifiers size"
                         << d_quantEngine->getModel()->getNumAssertedQuantifiers() << std::endl;
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node n = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( options::cbqi() && hasAddedCbqiLemma( n ) ){
        Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( n );
        bool active, value;
        bool ceValue = false;
        if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          active = value;
          ceValue = true;
        }else{
          active = true;
        }
        d_quant_active[n] = active;
        if( active ){
          Debug("quantifiers") << "  Active : " << n;
          quantActive = true;
        }else{
          Debug("quantifiers") << "  NOT active : " << n;
          if( d_quantEngine->getValuation().isDecision( cel ) ){
            Debug("quant-req-phase") << "Bad decision : " << cel << std::endl;
          }
          //note that the counterexample literal must not be a decision
          Assert( !d_quantEngine->getValuation().isDecision( cel ) );
        }
        if( d_quantEngine->getValuation().hasSatValue( n, value ) ){
          Debug("quantifiers") << ", value = " << value;
        }
        if( ceValue ){
          Debug("quantifiers") << ", ce is asserted";
        }
        Debug("quantifiers") << std::endl;
      }else{
        d_quant_active[n] = true;
        quantActive = true;
        Debug("quantifiers") << "  Active : " << n << ", no ce assigned." << std::endl;
      }
      Debug("quantifiers-relevance")  << "Quantifier : " << n << std::endl;
      Debug("quantifiers-relevance")  << "   Relevance : " << d_quantEngine->getQuantifierRelevance()->getRelevance( n ) << std::endl;
      Debug("quantifiers") << "   Relevance : " << d_quantEngine->getQuantifierRelevance()->getRelevance( n ) << std::endl;
    }
    if( quantActive ){
      bool addedLemmas = doInstantiationRound( e );
      //Debug("quantifiers-dec") << "Do instantiation, level = " << d_quantEngine->getValuation().getDecisionLevel() << std::endl;
      //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
      //  Debug("quantifiers-dec") << "   " << d_valuation.getDecision( i ) << std::endl;
      //}
      if( e==Theory::EFFORT_LAST_CALL ){
        if( !addedLemmas ){
          if( d_inst_round_status==InstStrategy::STATUS_SAT ){
            Debug("inst-engine") << "No instantiation given, returning SAT..." << std::endl;
            debugSat( SAT_INST_STRATEGY );
          }else if( d_setIncomplete ){
            Debug("inst-engine") << "No instantiation given, returning unknown..." << std::endl;
            d_quantEngine->getOutputChannel().setIncomplete();
          }else{
            Assert( options::finiteModelFind() );
            Debug("inst-engine") << "No instantiation given, defer to another engine..." << std::endl;
          }
        }
      }
    }else{
      if( e==Theory::EFFORT_LAST_CALL ){
        if( options::cbqi() ){
          debugSat( SAT_CBQI );
        }
      }
    }
    if( Trace.isOn("inst-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "Finished instantiation engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

void InstantiationEngine::registerQuantifier( Node f ){
  //Notice() << "do cbqi " << f << " ? " << std::endl;
  Node ceBody = d_quantEngine->getTermDatabase()->getInstConstantBody( f );
  if( !doCbqi( f ) ){
    d_quantEngine->addTermToDatabase( ceBody, true );
    //need to tell which instantiators will be responsible
    //by default, just chose the UF instantiator
    d_quantEngine->getInstantiator( theory::THEORY_UF )->setQuantifierActive( f );
  }

  //take into account user patterns
  if( f.getNumChildren()==3 ){
    Node subsPat = d_quantEngine->getTermDatabase()->getInstConstantNode( f[2], f );
    //add patterns
    for( int i=0; i<(int)subsPat.getNumChildren(); i++ ){
      //Notice() << "Add pattern " << subsPat[i] << " for " << f << std::endl;
      ((uf::InstantiatorTheoryUf*)d_quantEngine->getInstantiator( theory::THEORY_UF ))->addUserPattern( f, subsPat[i] );
    }
  }
}

void InstantiationEngine::assertNode( Node f ){
  ////if we are doing cbqi and have not added the lemma yet, do so
  //if( doCbqi( f ) && !hasAddedCbqiLemma( f ) ){
  //  addCbqiLemma( f );
  //}
}

bool InstantiationEngine::hasApplyUf( Node f ){
  if( f.getKind()==APPLY_UF ){
    return true;
  }else{
    for( int i=0; i<(int)f.getNumChildren(); i++ ){
      if( hasApplyUf( f[i] ) ){
        return true;
      }
    }
    return false;
  }
}
bool InstantiationEngine::hasNonArithmeticVariable( Node f ){
  for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
    TypeNode tn = f[0][i].getType();
    if( !tn.isInteger() && !tn.isReal() ){
      return true;
    }
  }
  return false;
}

bool InstantiationEngine::doCbqi( Node f ){
  if( options::cbqi.wasSetByUser() ){
    return options::cbqi();
  }else if( options::cbqi() ){
    //if quantifier has a non-arithmetic variable, then do not use cbqi
    //if quantifier has an APPLY_UF term, then do not use cbqi
    return !hasNonArithmeticVariable( f ) && !hasApplyUf( f[1] );
  }else{
    return false;
  }
}














void InstantiationEngine::debugSat( int reason ){
  if( reason==SAT_CBQI ){
    //Debug("quantifiers-sat") << "Decisions:" << std::endl;
    //for( int i=1; i<=(int)d_quantEngine->getValuation().getDecisionLevel(); i++ ){
    //  Debug("quantifiers-sat") << "   " << i << ": " << d_quantEngine->getValuation().getDecision( i ) << std::endl;
    //}
    //for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
    //  if( (*i).second ) {
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
      Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( f );
      Assert( !cel.isNull() );
      bool value;
      if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
        if( !value ){
          AlwaysAssert(! d_quantEngine->getValuation().isDecision( cel ),
                       "bad decision on counterexample literal");
        }
      }
    }
    //}
    Debug("quantifiers-sat") << "return SAT: Cbqi, no quantifier is active. " << std::endl;
    //static bool setTrust = false;
    //if( !setTrust ){
    //  setTrust = true;
    //  Notice() << "trust-";
    //}
  }else if( reason==SAT_INST_STRATEGY ){
    Debug("quantifiers-sat") << "return SAT: No strategy chose to add an instantiation." << std::endl;
    //Notice() << "sat ";
    //Unimplemented();
  }
}

Node InstantiationEngine::getNextDecisionRequest(){
  //propagate as decision all counterexample literals that are not asserted
  if( options::cbqi() ){
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( hasAddedCbqiLemma( f ) ){
        Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( f );
        bool value;
        if( !d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          //if not already set, propagate as decision
          Debug("cbqi-prop-as-dec") << "CBQI: propagate as decision " << cel << std::endl;
          return cel;
        }
      }
    }
  }
  return Node::null();
}
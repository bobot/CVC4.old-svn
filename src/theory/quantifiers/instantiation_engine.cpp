#include "theory/quantifiers/instantiation_engine.h"

#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_instantiator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

//#define IE_PRINT_PROCESS_TIMES

InstantiationEngine::InstantiationEngine( TheoryQuantifiers* th ) :
d_th( th ), d_forall_asserts( d_th->getContext() ), d_in_instRound( false, d_th->getContext() ){
  d_in_instRound_no_c = false;
}

QuantifiersEngine* InstantiationEngine::getQuantifiersEngine(){
  return d_th->getQuantifiersEngine();
}

bool InstantiationEngine::doInstantiationRound( Theory::Effort effort ){
  Debug("inst-engine") << "IE: Instantiation Round." << std::endl;
  Debug("inst-engine-ctrl") << "IE: Instantiation Round." << std::endl;
  bool success;
  do{
    bool startedInstRound = false;
    //reset instantiators
#if 0
    if( !d_in_instRound ){
      d_in_instRound = true;
#elif 0
    if( !d_in_instRound_no_c ){
      d_in_instRound_no_c = true;
#else
    if( true ){
#endif
      Debug("inst-engine-ctrl") << "Reset IE" << std::endl;
      startedInstRound = true;
      for( int i=0; i<theory::THEORY_LAST; i++ ){
        if( getQuantifiersEngine()->getInstantiator( i ) ){
          getQuantifiersEngine()->getInstantiator( i )->resetInstantiationRound( effort );
          //getQuantifiersEngine()->getInstantiator( i )->resetInstantiationStrategies();
        }
      }
    }
    int eLimit = effort==Theory::EFFORT_LAST_CALL ? 10 : 2;
    int e = 0;
    d_inst_round_status = InstStrategy::STATUS_UNFINISHED;
    //while unfinished, try effort level=0,1,2....
    while( d_inst_round_status==InstStrategy::STATUS_UNFINISHED && e<=eLimit ){
      //if( e==3 ){
      //  std::cout << "unknown ";
      //  exit( 24 );
      //}
      Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
      d_inst_round_status = InstStrategy::STATUS_SAT;
      //instantiate each quantifier
      for( int q=0; q<getQuantifiersEngine()->getNumQuantifiers(); q++ ){
        Node f = getQuantifiersEngine()->getQuantifier( q );
        Debug("inst-engine-debug") << "IE: Instantiate " << f << "..." << std::endl;
        //if this quantifier is active
        if( getQuantifiersEngine()->getActive( f ) ){
          //std::cout << "Process " << f << " " << effort << " " << e << std::endl;
          //int e_use = getQuantifiersEngine()->getRelevance( f )==-1 ? e - 1 : e;
          int e_use = e;
          if( e_use>=0 ){
            //use each theory instantiator to instantiate f
            for( int i=0; i<theory::THEORY_LAST; i++ ){
              if( getQuantifiersEngine()->getInstantiator( i ) ){
                Debug("inst-engine-debug") << "Do " << getQuantifiersEngine()->getInstantiator( i )->identify() << " " << e_use << std::endl;
                //std::cout << "Do " << d_instTable[i]->identify() << " " << e << std::endl;
                int limitInst = 0;
                int quantStatus = getQuantifiersEngine()->getInstantiator( i )->doInstantiation( f, effort, e_use, limitInst );
                Debug("inst-engine-debug") << " -> status is " << quantStatus << std::endl;
                //std::cout << " -> status is " << d_instTable[i]->getStatus() << std::endl;
                InstStrategy::updateStatus( d_inst_round_status, quantStatus );
              }
            }
          }
          //std::cout << "Done" << std::endl;
        }
      }
      //do not consider another level if already added lemma at this level
      if( getQuantifiersEngine()->hasAddedLemma() ){
        d_inst_round_status = InstStrategy::STATUS_UNKNOWN;
      }
      e++;
    }
    Debug("inst-engine") << "All instantiators finished, # added lemmas = ";
    Debug("inst-engine") << (int)getQuantifiersEngine()->d_lemmas_waiting.size() << std::endl;
    //std::cout << "All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
    if( !getQuantifiersEngine()->hasAddedLemma() ){
      if( startedInstRound ){
        Debug("inst-engine-stuck") << "No instantiations produced at this state: " << std::endl;
        for( int i=0; i<theory::THEORY_LAST; i++ ){
          if( getQuantifiersEngine()->getInstantiator( i ) ){
            getQuantifiersEngine()->getInstantiator( i )->debugPrint("inst-engine-stuck");
            Debug("inst-engine-stuck") << std::endl;
          }
        }
        Debug("inst-engine-ctrl") << "---Fail." << std::endl;
        return false;
      }else{
        d_in_instRound = false;
        d_in_instRound_no_c = false;
        success = false;
      }
    }else{
      success = true;
    }
  }while( !success );
  Debug("inst-engine-ctrl") << "---Done. " << (int)getQuantifiersEngine()->d_lemmas_waiting.size() << std::endl;
#ifdef IE_PRINT_PROCESS_TIMES
  std::cout << "lemmas = " << (int)getQuantifiersEngine()->d_lemmas_waiting.size() << std::endl;
#endif
  //flush lemmas to output channel
  getQuantifiersEngine()->flushLemmas( &d_th->getOutputChannel() );
  return true;
}

int ierCounter = 0;

void InstantiationEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_FULL ){
    ierCounter++;
  }
  if( ( e==Theory::EFFORT_FULL  && ierCounter%2==0 ) || e==Theory::EFFORT_LAST_CALL ){
  //if( e==Theory::EFFORT_LAST_CALL ){
    if( e==Theory::EFFORT_LAST_CALL ){
      ++(getQuantifiersEngine()->d_statistics.d_instantiation_rounds_lc); 
    }else{
      ++(getQuantifiersEngine()->d_statistics.d_instantiation_rounds); 
    }
    Debug("inst-engine") << "IE: Check " << e << " " << ierCounter << std::endl;
#ifdef IE_PRINT_PROCESS_TIMES
    double clSet = double(clock())/double(CLOCKS_PER_SEC);
    std::cout << "Run instantiation round " << e << " " << ierCounter << std::endl;
#endif
    bool quantActive = false;
    //for each n in d_forall_asserts,
    // such that the counterexample literal is not in positive in d_counterexample_asserts
    for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
      if( (*i).second ) {
        Node n = (*i).first;
        Node cel = getQuantifiersEngine()->getCounterexampleLiteralFor( n );
        if( !cel.isNull() && !Options::current()->finiteModelFind ){
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
        }else{
          getQuantifiersEngine()->setActive( n, true );
          quantActive = true;
          Debug("quantifiers") << "  Active : " << n << ", no ce assigned." << std::endl;
        }
        Debug("quantifiers-relevance")  << "Quantifier : " << n << std::endl;
        Debug("quantifiers-relevance")  << "   Relevance : " << getQuantifiersEngine()->getRelevance( n ) << std::endl;
        Debug("quantifiers") << "   Relevance : " << getQuantifiersEngine()->getRelevance( n ) << std::endl;
      }
    }
    if( quantActive ){
      bool addedLemmas = doInstantiationRound( e );
      //Debug("quantifiers-dec") << "Do instantiation, level = " << d_th->getValuation().getDecisionLevel() << std::endl;
      //for( int i=1; i<=(int)d_valuation.getDecisionLevel(); i++ ){
      //  Debug("quantifiers-dec") << "   " << d_valuation.getDecision( i ) << std::endl;
      //}
      if( e==Theory::EFFORT_LAST_CALL ){
        if( !addedLemmas ){
          if( d_inst_round_status==InstStrategy::STATUS_SAT ){
            Debug("inst-engine") << "No instantiation given, returning SAT..." << std::endl;
            debugSat( SAT_INST_STRATEGY );
          }else{
            Debug("inst-engine") << "No instantiation given, returning unknown..." << std::endl;
            d_th->getOutputChannel().setIncomplete();
          }
        }
      }
    }else{
      if( e==Theory::EFFORT_LAST_CALL ){
        if( Options::current()->cbqi ){
          debugSat( SAT_CBQI );
        }
      }
    }
#ifdef IE_PRINT_PROCESS_TIMES
    double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
    std::cout << "Done Run instantiation round " << (clSet2-clSet) << std::endl;
#endif
  }
}

void InstantiationEngine::registerQuantifier( Node f ){
  if( !TheoryQuantifiers::isRewriteKind( f[1].getKind() ) ){
    //std::cout << "do cbqi " << f << " ? " << std::endl;
    if( doCbqi( f ) ){
      Debug("cbqi") << "Do cbqi for " << f << std::endl;
      //make the counterexample body
      Node ceBody = f[1].substitute( getQuantifiersEngine()->d_vars[f].begin(), getQuantifiersEngine()->d_vars[f].end(),
                                    getQuantifiersEngine()->d_inst_constants[f].begin(),
                                    getQuantifiersEngine()->d_inst_constants[f].end() );
      getQuantifiersEngine()->d_counterexample_body[ f ] = ceBody;
      //code for counterexample-based quantifier instantiation
      //get the counterexample literal
      Node ceLit = d_th->getValuation().ensureLiteral( ceBody.notNode() );
      getQuantifiersEngine()->d_ce_lit[ f ] = ceLit;
      // set attributes, mark all literals in the body of n as dependent on cel
      registerLiterals( ceLit, f );
      getQuantifiersEngine()->generatePhaseReqs( f );
      //require any decision on cel to be phase=true
      d_th->getOutputChannel().requirePhase( ceLit, true );
      Debug("cbqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
      //add counterexample lemma
      NodeBuilder<> nb(kind::OR);
      nb << f << ceLit;
      Node lem = nb;
      Debug("cbqi-debug") << "Counterexample lemma : " << lem << std::endl;
      d_th->getOutputChannel().lemma( lem );
      ////mark cel as dependent on n?
      //Node quant = ( n.getKind()==kind::NOT ? n[0] : n );
      //Debug("quant-dep-dec") << "Make " << cel << " dependent on " << quant << std::endl;
      //d_out->dependentDecision( quant, cel );
      ////set has constraints from
      //for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      //  getQuantifiersEngine()->getTheoryEngine()->theoryOf( f[0][i] )->getInstantiator()->setHasConstraintsFrom( f );
      //}
    }else{
      getQuantifiersEngine()->addTermToDatabase( getQuantifiersEngine()->getOrCreateCounterexampleBody( f ), true );
      //compute phase requirements
      getQuantifiersEngine()->generatePhaseReqs( f );
      //need to tell which instantiators will be responsible
      //by default, just chose the UF instantiator
      getQuantifiersEngine()->getInstantiator( theory::THEORY_UF )->setHasConstraintsFrom( f );
    }

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
  if( Options::current()->cbqiSetByUser ){
    return Options::current()->cbqi;
  }else if( Options::current()->cbqi ){
    //if quantifier has a non-arithmetic variable, then do not use cbqi
    //if quantifier has an APPLY_UF term, then do not use cbqi
    return !hasNonArithmeticVariable( f ) && !hasApplyUf( f[1] );
  }else{
    return false;
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
      if( !getQuantifiersEngine()->getCounterexampleLiteralFor( f ).isNull() ){
        if( getQuantifiersEngine()->d_te->getPropEngine()->isSatLiteral( n ) && n.getKind()!=NOT ){
          if( n!=getQuantifiersEngine()->getCounterexampleLiteralFor( f ) && 
              n.notNode()!=getQuantifiersEngine()->getCounterexampleLiteralFor( f ) ){
            Debug("quant-dep-dec") << "Make " << n << " dependent on ";
            Debug("quant-dep-dec") << getQuantifiersEngine()->getCounterexampleLiteralFor( f ) << std::endl;
            d_th->getOutputChannel().dependentDecision( getQuantifiersEngine()->getCounterexampleLiteralFor( f ), n );
          }
        }
      }
      if( n.getKind()==FORALL ){
        Debug("cbqi-debug") << "Set instantiation constant attribute on " << n << std::endl;
      }
      InstConstantAttribute ica;
      n.setAttribute(ica,f);
    }
  }
}

void InstantiationEngine::debugSat( int reason ){
  if( reason==SAT_CBQI ){
    //Debug("quantifiers-sat") << "Decisions:" << std::endl;
    //for( int i=1; i<=(int)d_th->getValuation().getDecisionLevel(); i++ ){
    //  Debug("quantifiers-sat") << "   " << i << ": " << d_th->getValuation().getDecision( i ) << std::endl;
    //}
    for( BoolMap::iterator i = d_forall_asserts.begin(); i != d_forall_asserts.end(); i++ ) {
      if( (*i).second ) {
        Node cel = getQuantifiersEngine()->getCounterexampleLiteralFor( (*i).first );
        Assert( !cel.isNull() );
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
    Debug("quantifiers-sat") << "return SAT: Cbqi, no quantifier is active. " << std::endl;
    //static bool setTrust = false;
    //if( !setTrust ){
    //  setTrust = true;
    //  std::cout << "trust-";
    //}
  }else if( reason==SAT_INST_STRATEGY ){
    Debug("quantifiers-sat") << "return SAT: No strategy chose to add an instantiation." << std::endl;
    //std::cout << "sat ";
    //exit( 11 );
  }
}

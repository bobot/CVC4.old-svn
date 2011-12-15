/*********************                                                        */
/*! \file instantiation_engine.cpp
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
 ** \brief Implementation of instantiation engine class
 **/

#include "theory/instantiation_engine.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

bool InstStrategyModerator::process( int effort ){

  return false;
}

Instantiator::Instantiator(context::Context* c, InstantiationEngine* ie, Theory* th) : 
d_status( STATUS_UNFINISHED ),
d_instEngine( ie ),
d_th( th ){

}

Instantiator::~Instantiator(){
}

void Instantiator::doInstantiation( int effort ){
  d_status = STATUS_SAT;
  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    if( d_instEngine->getActive( it->first ) && hasConstraintsFrom( it->first ) ){
      d_quantStatus = STATUS_UNFINISHED;
      //call the instantiator's process method
      process( it->first, effort );
      //now call all instantiation strategies process methods
      //d_instStrategies[ it->first ].process( effort );
      updateStatus( d_status, d_quantStatus );
    }
  }
}

void Instantiator::updateStatus( int& currStatus, int addStatus ){
  if( addStatus==STATUS_UNFINISHED ){
    currStatus = STATUS_UNFINISHED;
  }else if( addStatus==STATUS_UNKNOWN ){
    if( currStatus==STATUS_SAT ){
      currStatus = STATUS_UNKNOWN;
    }
  }
}

void Instantiator::setHasConstraintsFrom( Node f ){
  d_hasConstraints[f] = true;
  if( d_instEngine->d_owner.find( f )==d_instEngine->d_owner.end() ){
    d_instEngine->d_owner[f] = getTheory();
  }else if( d_instEngine->d_owner[f]!=getTheory() ){
    d_instEngine->d_owner[f] = NULL;
  }
}

bool Instantiator::hasConstraintsFrom( Node f ) { 
  return d_hasConstraints.find( f )!=d_hasConstraints.end() && d_hasConstraints[f]; 
}

bool Instantiator::isOwnerOf( Node f ){
  return d_instEngine->d_owner.find( f )!=d_instEngine->d_owner.end() &&
         d_instEngine->d_owner[f]==getTheory();
}

InstantiationEngine::InstantiationEngine(context::Context* c, TheoryEngine* te):
d_te( te ),
d_active( c ){
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_instTable[theoryId] = NULL;
  }
}

bool InstantiationEngine::addLemma( Node lem ){
  //AJR: the following check is necessary until FULL_CHECK is guarenteed after d_out->lemma(...)
  Debug("inst-engine-debug") << "Adding lemma : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  if( d_lemmas_produced.find( lem )==d_lemmas_produced.end() ){
    //d_curr_out->lemma( lem );
    d_lemmas_produced[ lem ] = true;
    d_lemmas_waiting.push_back( lem );
    Debug("inst-engine-debug") << "Added lemma : " << lem << std::endl;
    return true;
  }else{
    return false;
  }
}

bool InstantiationEngine::addInstantiation( Node f, std::vector< Node >& terms )
{
  //std::cout << "***& Instantiate " << f << " with " << std::endl;
  //for( int i=0; i<(int)terms.size(); i++ ){
  //  std::cout << "   " << terms[i] << std::endl;
  //}
  Assert( f.getKind()==FORALL );
  Assert( !f.hasAttribute(InstConstantAttribute()) );
  Assert( d_vars[f].size()==terms.size() && d_vars[f].size()==f[0].getNumChildren() );
  Node body = f[ 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                 terms.begin(), terms.end() ); 
  NodeBuilder<> nb(kind::OR);
  nb << f.notNode() << body;
  Node lem = nb;
  if( addLemma( lem ) ){
    Debug("inst-engine") << "*** Instantiate " << f << " with " << std::endl;
    //std::cout << "*** Instantiate " << f << " with " << std::endl;
    uint64_t maxInstLevel = 0;
    for( int i=0; i<(int)terms.size(); i++ ){
      if( terms[i].hasAttribute(InstConstantAttribute()) ){
        //std::cout << "***& Instantiate " << f << " with " << std::endl;
        //for( int i=0; i<(int)terms.size(); i++ ){
        //  std::cout << "   " << terms[i] << std::endl;
        //}
        std::cout << "unknown ";
        exit( 19 );
      }
      Assert( !terms[i].hasAttribute(InstConstantAttribute()) );
      Debug("inst-engine") << "   " << terms[i];
      //std::cout << "   " << terms[i] << std::endl;
      //Debug("inst-engine") << " " << terms[i].getAttribute(InstLevelAttribute());
      Debug("inst-engine") << std::endl;
      if( terms[i].hasAttribute(InstLevelAttribute()) ){
        if( terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
          maxInstLevel = terms[i].getAttribute(InstLevelAttribute()); 
        }
      }else{
        setInstantiationLevel( terms[i], 0 );
      }
    }
    setInstantiationLevel( body, maxInstLevel+1 );
    ++(d_statistics.d_instantiations);
    d_statistics.d_total_inst_var.setData( d_statistics.d_total_inst_var.getData() + (int)terms.size() );
    d_statistics.d_max_instantiation_level.maxAssign( maxInstLevel+1 );
    return true;
  }else{
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
}

bool InstantiationEngine::addInstantiation( InstMatch* m, bool addSplits ){
  //Assert( m->isComplete() );
  //std::cout << "compute vec " << m << std::endl;
  int origTermSize = 0;
  for( std::map< Node, Node >::iterator it = m->d_map.begin(); it != m->d_map.end(); ++it ){
    if( it->second!=Node::null() ){
      origTermSize++;
    }
  }
  m->computeTermVec( this );
  //std::cout << "done" << std::endl;
  //std::cout << "m's quant is " << m->getQuantifier() << std::endl;
  //std::cout << "*** Instantiate " << m->getQuantifier() << " with " << std::endl;
  //for( int i=0; i<(int)m->d_match.size(); i++ ){
  //  std::cout << "   " << m->d_match[i] << std::endl;
  //}

  if( addInstantiation( m->getQuantifier(), m->d_match ) ){
    d_statistics.d_total_inst_var_unspec.setData( d_statistics.d_total_inst_var_unspec.getData() + (int)m->d_match.size() - origTermSize );
    if( (int)m->d_match.size()!=origTermSize ){
      //std::cout << "Unspec. " << std::endl;
      //std::cout << "*** Instantiate " << m->getQuantifier() << " with " << std::endl;
      //for( int i=0; i<(int)m->d_match.size(); i++ ){
      //  std::cout << "   " << m->d_match[i] << std::endl;
      //}
      ++(d_statistics.d_inst_unspec);
    }
    if( addSplits ){
      for( std::map< Node, Node >::iterator it = m->d_splits.begin(); it != m->d_splits.end(); ++it ){
        addSplitEquality( it->first, it->second, true, true );
      }
    }
    return true;
  }
  return false;
}

bool InstantiationEngine::addSplit( Node n, bool reqPhase, bool reqPhasePol ){
  n = Rewriter::rewrite( n );
  Node lem = NodeManager::currentNM()->mkNode( OR, n, n.notNode() );
  if( addLemma( lem ) ){
    ++(d_statistics.d_splits);
    Debug("inst-engine") << "*** Add split " << n<< std::endl;
    //if( reqPhase ){
    //  d_curr_out->requirePhase( n, reqPhasePol );
    //}
    return true;
  }
  return false;
}

bool InstantiationEngine::addSplitEquality( Node n1, Node n2, bool reqPhase, bool reqPhasePol ){
  //Assert( !n1.hasAttribute(InstConstantAttribute()) );
  //Assert( !n2.hasAttribute(InstConstantAttribute()) );
  //Assert( !areEqual( n1, n2 ) );
  //Assert( !areDisequal( n1, n2 ) );
  Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  Node fm = NodeManager::currentNM()->mkNode( knd, n1, n2 );
  return addSplit( fm );
}

void InstantiationEngine::registerQuantifier( Node f, OutputChannel* out, Valuation& valuation ){
  Assert( f.getKind()==FORALL );
  if( d_counterexample_body.find( f )==d_counterexample_body.end() ){
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      Node ic = NodeManager::currentNM()->mkInstConstant( f[0][i].getType() );
      d_inst_constants_map[ic] = f;
      d_inst_constants[ f ].push_back( ic );
    }
    std::vector< Node > vars;
    getVariablesFor( f, vars );
    d_counterexample_body[ f ] = f[ 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                                    d_inst_constants[ f ].begin(), d_inst_constants[ f ].end() ); 

    //get the counterexample literal
    d_ce_lit[ f ] = valuation.ensureLiteral( d_counterexample_body[ f ].notNode() );
    Debug("quantifiers") << d_ce_lit[ f ] << " is the ce literal for " << f << std::endl;

    // set attributes, mark all literals in the body of n as dependent on cel
    registerTerm( d_ce_lit[ f ], f, out );
    computePhaseReqs( d_counterexample_body[ f ], false );
    //require any decision on cel to be phase=true
    out->requirePhase( d_ce_lit[ f ], true );
    Debug("quant-req-phase") << "Require phase " << d_ce_lit[ f ] << " = true." << std::endl;

    //make the match generator
    d_qmg[ f ] = new QuantMatchGenerator( this, f );
    if( f.getNumChildren()==3 ){
      //getCounterexampleBody( f );
      Node subsPat = f[2].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                      d_inst_constants[ f ].begin(), d_inst_constants[ f ].end() ); 

      //add patterns
      for( int i=0; i<(int)subsPat.getNumChildren(); i++ ){
        registerTerm( subsPat[i], f, out );
        //std::cout << "Add pattern " << subsPat[i] << " for " << f << std::endl;
        d_qmg[ f ]->addUserPattern( subsPat[i] );
      }
      //the UF instantiator now has a say in how to instantiation f
      d_instTable[theory::THEORY_UF]->setHasConstraintsFrom( f );
    }
  }
}

void InstantiationEngine::registerTerm( Node n, Node f, OutputChannel* out ){
  if( !n.hasAttribute(InstConstantAttribute()) ){
    bool setAttr = false;
    if( n.getKind()==INST_CONSTANT ){
      setAttr = true;
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        registerTerm( n[i], f, out );
        if( n[i].hasAttribute(InstConstantAttribute()) ){
          setAttr = true;
        }
      }
    }
    if( setAttr ){
      if( d_te->getPropEngine()->isSatLiteral( n ) && n.getKind()!=NOT ){
        if( n!=d_ce_lit[f] && n.notNode()!=d_ce_lit[f] ){
          Debug("quant-dep-dec") << "Make " << n << " dependent on " << d_ce_lit[f] << std::endl;
          out->dependentDecision( d_ce_lit[f], n );
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
  d_phase_reqs[n] = polarity;
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

Node InstantiationEngine::getSkolemizedBody( Node f ){
  Assert( f.getKind()==FORALL );
  if( d_skolem_body.find( f )==d_skolem_body.end() ){
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      Node skv = NodeManager::currentNM()->mkSkolem( f[0][i].getType() );
      d_skolem_constants[ f ].push_back( skv );
    }
    std::vector< Node > vars;
    getVariablesFor( f, vars );
    d_skolem_body[ f ] = f[ 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                            d_skolem_constants[ f ].begin(), d_skolem_constants[ f ].end() );
    if( f.hasAttribute(InstLevelAttribute()) ){
      setInstantiationLevel( d_skolem_body[ f ], f.getAttribute(InstLevelAttribute()) );
    }
  }
  return d_skolem_body[ f ];
}

void InstantiationEngine::getVariablesFor( Node f, std::vector< Node >& vars )
{
  Assert( vars.empty() );
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==FORALL ) );
  Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
  if( d_vars.find( quant )==d_vars.end() ){
    for( int i=0; i<(int)quant[0].getNumChildren(); i++ ){
      vars.push_back( quant[0][i] );
    }
    d_vars[ quant ].insert( d_vars[ quant ].begin(), vars.begin(), vars.end() );
  }else{
    vars.insert( vars.begin(), d_vars[ quant ].begin(), d_vars[ quant ].end() );
  }
}

bool InstantiationEngine::doInstantiationRound( OutputChannel* out ){
  ++(d_statistics.d_instantiation_rounds);
  //std::cout << "Instantiation Round" << std::endl;
  Debug("inst-engine") << "IE: Reset instantiation." << std::endl;
  //reset instantiators
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( d_instTable[i] ){
      d_instTable[i]->resetInstantiationRound();
    }
  }
  int e = 0;
  d_status = Instantiator::STATUS_UNFINISHED;
  while( d_status==Instantiator::STATUS_UNFINISHED ){
    Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    //std::cout << "IE: Prepare instantiation (" << e << ")." << std::endl; 
    d_status = Instantiator::STATUS_SAT;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] ){
        d_instTable[i]->doInstantiation( e );
        Debug("inst-engine-debug") << e << " " << d_instTable[i]->identify() << " is " << d_instTable[i]->getStatus() << std::endl;
        //update status
        Instantiator::updateStatus( d_status, d_instTable[i]->getStatus() );
      }
    }
    if( !d_lemmas_waiting.empty() ){
      d_status = Instantiator::STATUS_UNKNOWN;
    }
    e++;
  }
  Debug("inst-engine") << "IE: All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
  if( d_lemmas_waiting.empty() ){
    Debug("inst-engine-stuck") << "No instantiations produced at this state: " << std::endl;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] ){
        d_instTable[i]->debugPrint("inst-engine-stuck");
        Debug("inst-engine-stuck") << std::endl;
      }
    }
    return false;
  }else{
    for( int i=0; i<(int)d_lemmas_waiting.size(); i++ ){
      out->lemma( d_lemmas_waiting[i] );
    }
    d_lemmas_waiting.clear();
    return true;
  }
}

void InstantiationEngine::setInstantiationLevel( Node n, uint64_t level ){
  if( !n.hasAttribute(InstLevelAttribute()) ){
    InstLevelAttribute ila;
    n.setAttribute(ila,level);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setInstantiationLevel( n[i], level );
  }
}

InstantiationEngine::Statistics::Statistics():
  d_instantiation_rounds("InstantiationEngine::Instantiation_Rounds", 0),
  d_instantiations("InstantiationEngine::Total_Instantiations", 0),
  d_max_instantiation_level("InstantiationEngine::Max_Instantiation_Level", 0),
  d_splits("InstantiationEngine::Total_Splits", 0),
  d_total_inst_var("InstantiationEngine::Inst_Vars", 0),
  d_total_inst_var_unspec("InstantiationEngine::Inst_Vars_Unspecified", 0),
  d_inst_unspec("InstantiationEngine::Inst_Unspecified", 0),
  d_inst_duplicate("InstantiationEngine::Inst_Duplicate", 0)
{
  StatisticsRegistry::registerStat(&d_instantiation_rounds);
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_max_instantiation_level);
  StatisticsRegistry::registerStat(&d_splits);
  StatisticsRegistry::registerStat(&d_total_inst_var);
  StatisticsRegistry::registerStat(&d_total_inst_var_unspec);
  StatisticsRegistry::registerStat(&d_inst_unspec);
  StatisticsRegistry::registerStat(&d_inst_duplicate);
}

InstantiationEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds);
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_max_instantiation_level);
  StatisticsRegistry::unregisterStat(&d_splits);
  StatisticsRegistry::unregisterStat(&d_total_inst_var);
  StatisticsRegistry::unregisterStat(&d_total_inst_var_unspec);
  StatisticsRegistry::unregisterStat(&d_inst_unspec);
  StatisticsRegistry::unregisterStat(&d_inst_duplicate);
}

Node InstantiationEngine::getFreeVariableForInstConstant( Node n ){
  if( d_free_vars.find( n )==d_free_vars.end() ){
    //if integer or real, make zero
    TypeNode tn = n.getType();
    if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
      Rational z(0);
      d_free_vars[n] = NodeManager::currentNM()->mkConst( z );
    }else{
      d_free_vars[n] = NodeManager::currentNM()->mkVar( tn );
    }
  }
  return d_free_vars[n];
}

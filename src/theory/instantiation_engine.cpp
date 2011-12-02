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
      process( it->first, effort );
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


void TermMatchEngine::processMatch( Node pat, Node g ){
  if( pat.getType()==g.getType() ){
    if( pat.getKind()==APPLY_UF && g.getKind()==APPLY_UF ){
      if( pat.getOperator()==g.getOperator() ){
        Debug("term-match") << "Process match " << pat << " " << g << std::endl;
        d_matches[pat][g] = InstMatchGenerator::mkMergeInstMatchGenerator( pat, g );
      }
    }
  }
}

void TermMatchEngine::registerTerm( Node n ){
  Debug("term-match") << "Register " << n << std::endl;
  if( n.hasAttribute(InstConstantAttribute()) ){
    d_patterns[n] = true;
    for( std::map< Node, bool >::iterator it = d_ground_terms.begin(); it != d_ground_terms.end(); ++it ){
      processMatch( n, it->first );
    }
  }else{
    d_ground_terms[n] = true;
    for( std::map< Node, bool >::iterator it = d_patterns.begin(); it != d_patterns.end(); ++it ){
      processMatch( it->first, n );
    }
  }
}

InstMatchGenerator* TermMatchEngine::makeMatchGenerator( std::vector< Node >& nodes ){
  if( nodes.empty() ){
    return NULL;
  }else{
    InstMatchGenerator* uit = InstMatchGenerator::mkInstMatchGenerator( false );
    for( int i=0; i<(int)nodes.size(); i++ ){
      if( d_matches[ nodes[i] ].empty() ){
        return NULL;
      }else{
        InstMatchGenerator* cit = InstMatchGenerator::mkInstMatchGenerator( true );
        for( std::map< Node, InstMatchGenerator* >::iterator it = d_matches[ nodes[i] ].begin(); it !=d_matches[ nodes[i] ].end(); ++it ){
          if( it->second ){
            cit->d_children.push_back( it->second );
          }
        }
        uit->d_children.push_back( cit );
      }
    }
    return uit;
  }
}

std::map< Node, std::vector< Node > > QuantMatchGenerator::Trigger::d_var_contains;

void QuantMatchGenerator::Trigger::computeVarContains2( Node n, Node parent ){
  if( n.getKind()==INST_CONSTANT ){
    if( std::find( d_var_contains[parent].begin(), d_var_contains[parent].end(), n )==d_var_contains[parent].end() ){
      d_var_contains[parent].push_back( n );
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeVarContains2( n[i], parent );
    }
  }
}

bool QuantMatchGenerator::Trigger::addNode( Node n ){
  Assert( std::find( d_nodes.begin(), d_nodes.end(), n )==d_nodes.end() );
  computeVarContains( n );
  bool success = false;
  for( int i=0; i<(int)d_var_contains[n].size(); i++ ){
    Node v = d_var_contains[n][i];
    if( d_vars.find( v )==d_vars.end() ){
      d_vars[ v ] = true;
      success = true;
    }
  }
  if( success ){
    d_nodes.push_back( n );
  }
  return success;
}

void QuantMatchGenerator::Trigger::debugPrint( const char* c ){
  for( int i=0; i<(int)d_nodes.size(); i++ ){
    if( i!=0 ){
      Debug( c ) << ", ";
    }
    Debug( c ) << d_nodes[i];
  }
}

void QuantMatchGenerator::addPatTerm( Node n ){
  Debug( "qmg-debug" ) << "Add pattern term " << n << std::endl;
  Assert( std::find( d_patTerms.begin(), d_patTerms.end(), n )==d_patTerms.end() );
  d_patTerms.push_back( n );
  if( n.getKind()==APPLY_UF && n.getType()!=NodeManager::currentNM()->booleanType() ){
    d_img_map[n] = InstMatchGenerator::mkAnyMatchInstMatchGenerator( n );
  }else{
    bool pol = n.getKind()!=NOT;
    Node eq = n.getKind()==NOT ? n[0] : n;
    Node t[2];
    if( eq.getKind()==EQUAL || eq.getKind()==IFF ){
      if( eq[0].getAttribute(InstConstantAttribute())!=d_f ){
        t[0] = eq[1];
        t[1] = eq[0];
      }else{
        t[0] = eq[0];
        t[1] = eq[1];
      }
    }else if( pol ){
      t[0] = eq;
      t[1] = NodeManager::currentNM()->mkConst<bool>(true);
    }else{
      pol = true;
      t[0] = eq;
      t[1] = NodeManager::currentNM()->mkConst<bool>(false);
    }
    Assert( t[0].getAttribute(InstConstantAttribute())==d_f );
    if( d_instEngine->d_phase_reqs.find( eq )!=d_instEngine->d_phase_reqs.end() ){
      //we know this literal must be matched with this polarity
      d_img_map[n] = InstMatchGenerator::mkCombineInstMatchGenerator( t[0], t[1], pol );
    }else{
      //this literal can be matched with either polarity
      //if( t[0].getType()==NodeManager::currentNM()->booleanType() ) {
      //  //for boolean apply uf, just use an any match generator
      //  d_img_map[n] = InstMatchGenerator::mkAnyMatchInstMatchGenerator( t[0] );
      //}else{
        d_img_map[n] = InstMatchGenerator::mkInstMatchGenerator( true );
        d_img_map[n]->d_children.push_back( InstMatchGenerator::mkCombineInstMatchGenerator( t[0], t[1], pol ) );
        d_img_map[n]->d_children.push_back( InstMatchGenerator::mkCombineInstMatchGenerator( t[0], t[1], !pol ) );
      //}
    }
  }
}

void QuantMatchGenerator::collectPatTerms( Node n ){
  if( n.getAttribute(InstConstantAttribute())==d_f ){
    if( n.getKind()==APPLY_UF ){
      if( std::find( d_patTerms.begin(), d_patTerms.end(), n )==d_patTerms.end() ){
        addPatTerm( n );
      }
    }else if( n.getKind()!=FORALL ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        collectPatTerms( n[i] );
      }
    }
  }
}

void QuantMatchGenerator::decomposePatTerm( Node n ){
  //DO_THIS
}

bool QuantMatchGenerator::hasCurrentGenerator( bool allowMakeNext ) { 
  if( d_index<(int)d_match_gen.size() ){
    return true;
  }else if( allowMakeNext ){
    Assert( d_index==(int)d_match_gen.size() );
    InstMatchGenerator* curr = getNextGenerator();
    if( curr ){
      d_match_gen.push_back( curr );
      return true;
    }
  }
  return false;
}

InstMatchGenerator* QuantMatchGenerator::getNextGenerator(){
  if( d_produceTrigger ){
    Assert( d_index==(int)d_match_gen.size() );
    InstMatchGenerator* next = NULL;
    if( d_match_gen.empty() ){
      //first iteration: produce matches for the nodes in d_patTerms
      if( !d_patTerms.empty() ){
        std::random_shuffle( d_patTerms.begin(), d_patTerms.end() );
        //generate a trigger
        next = InstMatchGenerator::mkInstMatchGenerator( false );
        //add terms to pattern that contribute at least one new variable
        int index = 0;
        do{
          Node tn = d_patTerms[index];
          if( d_currTrigger.addNode( tn ) ){
            //add term to trigger
            d_img_map[ tn ]->reset();
            next->d_children.push_back( d_img_map[ tn ] );
          }
          index++;
        }while( !d_currTrigger.isComplete( d_f ) && index<(int)d_patTerms.size() );

        Debug("qmg") << "Generated trigger ";
        d_currTrigger.debugPrint("qmg");
        Debug("qmg") << " for " << d_f << std::endl;
      }
    }else{
      ////subsequent iterations: create another trigger
      ////step 1: determine if any term failed to produce any match, if this is the case, decompose the pattern term
      //for( std::map< Node, bool >::iterator it = d_currTrigger.begin(); it != d_currTrigger.end(); ++it ){
      //  InstMatchGenerator* mg = d_img_map[ it->first ];
      //  if( mg->empty() ){
      //  }
      //}
      //DO_THIS
    }
    return next;
  }else{
    return NULL;
  }
}

void QuantMatchGenerator::resetInstantiationRound(){
  clearMatches();
  for( int i=0; i<(int)d_user_gen.size(); i++ ){
    clearMatches( i );
  }
  d_patTerms.clear();
  d_img_map.clear();
  d_currTrigger.clear();
}

/** add pattern */
int QuantMatchGenerator::addUserPattern( Node pat ) {
  //add to generators
  InstMatchGenerator* emg = InstMatchGenerator::mkInstMatchGenerator( false );
  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    emg->d_children.push_back( InstMatchGenerator::mkAnyMatchInstMatchGenerator( pat[i] ) );
  }
  d_user_gen.push_back( emg );
  return (int)d_user_gen.size()-1;
}

void QuantMatchGenerator::initializePatternTerms(){
  d_patTerms.clear();
  collectPatTerms( d_instEngine->d_counterexample_body[d_f] );
  d_produceTrigger = true;
}

void QuantMatchGenerator::initializePatternTerms( std::vector< Node >& patTerms ){
  d_patTerms.clear();
  for( int i=0; i<(int)patTerms.size(); i++ ){
    addPatTerm( patTerms[i] );
  }
  d_produceTrigger = true;
}

/** clear matches from this generator */
void QuantMatchGenerator::clearMatches( int pat ){
  if( pat!=-1 ){
    d_user_gen[pat]->clearMatches();
  }else{
    d_index = 0;
    d_match_gen.clear();
  }
}

/** reset the generator */
void QuantMatchGenerator::reset( int pat ) {
  if( pat!=-1 ){
    d_user_gen[pat]->reset();
  }else{
    d_index = 0;
    for( int i=0; i<(int)d_match_gen.size(); i++ ){
      d_match_gen[i]->reset();
    }
  }
}

/** get current match */
InstMatch* QuantMatchGenerator::getCurrent( int pat ) { 
  if( pat!=-1 ){
    //use provided patterns
    return d_user_gen[pat]->getCurrent();
  }else{
    return getCurrentGenerator()->getCurrent();
  }
}

/** get next match */
bool QuantMatchGenerator::getNextMatch( int pat, int triggerThresh ){ 
  if( pat!=-1 ){
    //use provided patterns
    //std::cout << "get next match " << pat << " " << d_user_gen[pat]->d_t << std::endl;
    return d_user_gen[pat]->getNextMatch();
  }else{
    while( hasCurrentGenerator( triggerThresh==-1 || d_index<triggerThresh ) ){
      if( getCurrentGenerator()->getNextMatch() ){
        return true;
      }
      d_index++;
    }
    return false;
  }
}


InstantiationEngine::InstantiationEngine(context::Context* c, TheoryEngine* te):
d_te( te ),
d_active( c ),
d_ic_active( c ){
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_instTable[theoryId] = NULL;
  }
  d_tme = TermMatchEngine( this );
}

bool InstantiationEngine::addLemma( Node lem ){
  //AJR: the following check is necessary until FULL_CHECK is guarenteed after d_out->lemma(...)
  Debug("inst-engine-debug") << "Adding lemma : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  if( d_lemmas_produced.find( lem )==d_lemmas_produced.end() ){
    d_addedLemma = true;
    d_curr_out->lemma( lem );
    d_lemmas_produced[ lem ] = true;
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
    uint64_t maxInstLevel = 0;
    for( int i=0; i<(int)terms.size(); i++ ){
      Assert( !terms[i].hasAttribute(InstConstantAttribute()) );
      Debug("inst-engine") << "   " << terms[i];
      //Debug("inst-engine") << " " << terms[i].getAttribute(InstLevelAttribute());
      Debug("inst-engine") << std::endl;
      if( terms[i].hasAttribute(InstLevelAttribute()) &&
          terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
        maxInstLevel = terms[i].getAttribute(InstLevelAttribute()); 
      }
    }
    setInstantiationLevel( body, maxInstLevel+1 );
    ++(d_statistics.d_instantiations);
    d_statistics.d_max_instantiation_level.maxAssign( maxInstLevel+1 );
    return true;
  }else{
    return false;
  }
}

bool InstantiationEngine::addInstantiation( InstMatch* m, bool addSplits ){
  //Assert( m->isComplete() );
  //std::cout << "compute vec " << m << std::endl;
  m->computeTermVec();
  //std::cout << "done" << std::endl;
  //std::cout << "m's quant is " << m->getQuantifier() << std::endl;
  //std::cout << "*** Instantiate " << m->getQuantifier() << " with " << std::endl;
  //for( int i=0; i<(int)m->d_match.size(); i++ ){
  //  std::cout << "   " << m->d_match[i] << std::endl;
  //}

  if( addInstantiation( m->getQuantifier(), m->d_match ) ){
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
    if( reqPhase ){
      d_curr_out->requirePhase( n, reqPhasePol );
    }
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

    d_curr_out = out;
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
    d_counterexamples[ f ] = valuation.ensureLiteral( d_counterexample_body[ f ].notNode() );
    Debug("quantifiers") << d_counterexamples[ f ] << " is the ce literal for " << f << std::endl;

    // set attributes, mark all literals in the body of n as dependent on cel
    registerTerm( d_counterexamples[ f ], f, out );
    computePhaseReqs( d_counterexample_body[ f ], false );
    //require any decision on cel to be phase=true
    out->requirePhase( d_counterexamples[ f ], true );
    Debug("quantifiers-req-phase") << "Require phase " << d_counterexamples[ f ] << " = true." << std::endl;

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
        if( n!=d_counterexamples[f] && n.notNode()!=d_counterexamples[f] ){
          Debug("quant-dep-dec") << "Make " << n << " dependent on " << d_counterexamples[f] << std::endl;
          out->dependentDecision( d_counterexamples[f], n );
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
  d_curr_out = out;
  ++(d_statistics.d_instantiation_rounds);
  Debug("inst-engine") << "IE: Reset instantiation." << std::endl;
  //reset instantiators
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( d_instTable[i] ){
      d_instTable[i]->resetInstantiationRound();
    }
  }
  int e = 0;
  d_status = Instantiator::STATUS_UNFINISHED;
  d_addedLemma = false;
  while( d_status==Instantiator::STATUS_UNFINISHED ){
    Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    d_instQueue.clear();
    d_status = Instantiator::STATUS_SAT;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] ){
        d_instTable[i]->doInstantiation( e );
        Debug("inst-engine-debug") << e << " " << d_instTable[i]->identify() << " is " << d_instTable[i]->getStatus() << std::endl;
        //update status
        Instantiator::updateStatus( d_status, d_instTable[i]->getStatus() );
      }
    }
    //try to piece together instantiations across theories
    processPartialInstantiations();
    if( d_addedLemma ){
      d_status = Instantiator::STATUS_UNKNOWN;
    }
    e++;
  }
  Debug("inst-engine") << "IE: All instantiators finished, addedLemma = " << d_addedLemma << std::endl;
  if( !d_addedLemma ){
    Debug("inst-engine-stuck") << "No instantiations produced at this state: " << std::endl;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] ){
        d_instTable[i]->debugPrint("inst-engine-stuck");
        Debug("inst-engine-stuck") << std::endl;
      }
    }
  }
  return d_addedLemma;
}

bool InstantiationEngine::addPartialInstantiation( InstMatch& m, Instantiator* i ){
  if( i->isOwnerOf( m.getQuantifier() ) ){
    return addInstantiation( &m );
  }else{
    d_instQueue[ m.getQuantifier() ][ i ].d_matches.push_back( m );
    return false;
  }
}

void InstantiationEngine::processPartialInstantiations(){
  for( std::map< Node, std::map< Instantiator*, InstMatchGroup > >::iterator it = d_instQueue.begin(); 
       it != d_instQueue.end(); ++it ){
    std::vector< InstMatchGroup* > merges;
    //try to piece together instantiations produced over multiple theories
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] && d_instTable[i]->hasConstraintsFrom( it->first ) ){
        if( it->second[ d_instTable[i] ].getNumMatches()>0 ){
          merges.push_back( &it->second[ d_instTable[i] ] );
        }else{
          merges.clear();
          break;
        }
      }
    }
    if( !merges.empty() ){
      //try to merge each instantiation across theories
      InstMatchGroup combined;
      InstMatch m( it->first, this );
      combined.d_matches.push_back( m );
      for( int i=0; i<(int)merges.size(); i++ ){
        InstMatchGroup mg( merges[i] );
        combined.merge( mg );
        if( combined.empty() ){
          break;
        }
      }
      for( int i=0; i<(int)combined.d_matches.size(); i++ ){
        addInstantiation( &combined.d_matches[i] );
      }
    }
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
  d_instantiation_rounds("InstantiationEngine::Instantiation Rounds", 0),
  d_instantiations("InstantiationEngine::Total Instantiations", 0),
  d_max_instantiation_level("InstantiationEngine::Max Instantiation Level", 0),
  d_splits("InstantiationEngine::Total Splits", 0)
{
  StatisticsRegistry::registerStat(&d_instantiation_rounds);
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_max_instantiation_level);
  StatisticsRegistry::registerStat(&d_splits);
}

InstantiationEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds);
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_max_instantiation_level);
  StatisticsRegistry::unregisterStat(&d_splits);
}


//Node InstantiationEngine::getCounterexampleBody( Node f ){
//  Assert( f.getKind()==FORALL );
//  if( d_counterexample_body.find( f )==d_counterexample_body.end() ){
//    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
//      Node ic = NodeManager::currentNM()->mkInstConstant( f[0][i].getType() );
//      d_inst_constants_map[ic] = f;
//      d_inst_constants[ f ].push_back( ic );
//    }
//    std::vector< Node > vars;
//    getVariablesFor( f, vars );
//    d_counterexample_body[ f ] = f[ 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
//                                                    d_inst_constants[ f ].begin(), d_inst_constants[ f ].end() ); 
//  }
//  return d_counterexample_body[ f ];
//}


Node InstantiationEngine::getCounterexampleBody( Node f ){
  //registerQuantifier( f );
  return d_counterexample_body[f];
}

Node InstantiationEngine::getCounterexampleLiteralFor( Node f ){
  //registerQuantifier( f );
  return d_counterexamples[f];
}

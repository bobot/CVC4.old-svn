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

void TermMatchEngine::computeVarContains( Node n ){
  if( n.getKind()==INST_CONSTANT ){
    d_var_contains[n][n] = true;
  }else{
    if( d_var_contains.find( n )==d_var_contains.end() ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        computeVarContains( n[i] );
      }
      if( n.getKind()==APPLY_UF ){
        //take union of all subterms
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          for( std::map< Node, bool >::iterator it = d_var_contains[ n[i] ].begin();
               it != d_var_contains[ n[i] ].end(); ++it ){
            d_var_contains[n][it->first] = true;
          }
        }
      }
    }
  }
}

void TermMatchEngine::collectApplyUf( Node n, std::vector< Node >& pat_terms ){
  if( n.getKind()==APPLY_UF ){
    pat_terms.push_back( n );
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      collectApplyUf( n[i], pat_terms );
    }
  }
}

void TermMatchEngine::makePatterns( Node ce_body ){
  Assert( ce_body.hasAttribute(InstConstantAttribute()) );
  computeVarContains( ce_body );
  Node f = ce_body.getAttribute(InstConstantAttribute());
  int numVars = d_instEngine->d_vars[f].size();

  std::vector< Node > pat_terms;
  collectApplyUf( ce_body, pat_terms );
  for( int i=0; i<(int)pat_terms.size(); i++ ){
    if( d_var_contains[ pat_terms[i] ].empty() ){
      pat_terms.erase( pat_terms.begin() + i, pat_terms.begin() + i + 1 );
      i--;
    }
  }
  
}

void TermMatchEngine::addPattern( Node f, Node pat ){
  d_ematch_patterns[f].push_back( pat );
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
  m->computeTermVec();
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

Node InstantiationEngine::getCounterexampleBody( Node f ){
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
  }
  return d_counterexample_body[ f ];
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

bool InstantiationEngine::doInstantiation( OutputChannel* out ){
  d_curr_out = out;
  //call instantiators to search for an instantiation
  ++(d_statistics.d_instantiation_rounds);
  Debug("inst-engine") << "IE: Reset instantiation." << std::endl;
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( d_instTable[i] ){
      d_instTable[i]->resetInstantiation();
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
        //Debug("inst-engine-debug") << e << " " << d_instTable[i]->identify() << " is " << d_instTable[i]->getStatus() << std::endl;
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

Node InstantiationEngine::getCounterexampleLiteralFor( Node n ){
  Assert( n.getKind()==FORALL );
#if 0
  if( d_counterexamples.find( n )==d_counterexamples.end() ){
    d_counterexamples[n] = NodeManager::currentNM()->mkNode( NO_COUNTEREXAMPLE, n );
  }
#endif
  return d_counterexamples[n];
}

void InstantiationEngine::setCounterexampleLiteralFor( Node n, Node l ){
  Assert( n.getKind()==FORALL );
  Assert( d_counterexamples.find( n )==d_counterexamples.end() );
  d_counterexamples[n] = l;
}

void InstantiationEngine::registerLiterals( Node n, Node cel, Node f, OutputChannel* out, bool polarity, bool reqPol )
{
  if( n.getKind()==INST_CONSTANT ){
    if( !n.hasAttribute(InstConstantAttribute()) ){
      InstConstantAttribute ica;
      n.setAttribute(ica,f);
    }
  }else{
    bool newReqPol = false;
    bool newPolarity = false;
    if( reqPol ){
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
    }
    Node fa;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n.getKind()==IMPLIES && i==0 ){
        registerLiterals( n[i], cel, f, out, !newPolarity, newReqPol );
      }else{
        registerLiterals( n[i], cel, f, out, newPolarity, newReqPol );
      }
      if( n[i].hasAttribute(InstConstantAttribute()) ){
        Assert( n[i].getAttribute(InstConstantAttribute())==f );
        fa = f;
      }
    }
    if( fa!=Node::null() ){
      //set n to have instantiation constants from f
      if( !n.hasAttribute(InstConstantAttribute()) ){
        if( d_te->getPropEngine()->isSatLiteral( n ) && n.getKind()!=NOT ){
          if( n!=cel && n.notNode()!=cel ){
            Debug("quant-dep-dec") << "Make " << n << " dependent on " << cel << std::endl;
            out->dependentDecision( cel, n );
          }
          if( reqPol ){
            //note that n will be require to be a particular polarity 
            //  this information is useful for instantiator algorithms
            //Debug("quant-req-phase") << "Required phase for " << n << " is " << polarity << std::endl;
            d_phase_reqs[n] = polarity;
          }
        }else{
          //Debug("quant-dep-dec") << n << " is not sat literal" << std::endl;
        }
        InstConstantAttribute ica;
        n.setAttribute(ica,f);
      }
    }else{
      //Debug("quant-dep-dec") << n << " does not have instantiation constants" << std::endl;
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


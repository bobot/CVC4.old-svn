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

InstMatch::InstMatch( Node f, InstantiationEngine* ie ){
  d_computeVec = true;
  for( int i=0; i<(int)ie->d_inst_constants[f].size(); i++ ){
    d_vars.push_back( ie->d_inst_constants[f][i] );
  }
}
InstMatch::InstMatch( InstMatch* m ){
  d_computeVec = true;
  d_vars.insert( d_vars.begin(), m->d_vars.begin(), m->d_vars.end() );
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m->d_map[ d_vars[i] ] );
    }
  }
  d_splits = m->d_splits;
}

bool InstMatch::add( InstMatch& m ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m.d_map[ d_vars[i] ] );
    }
  }
  return true;
}

bool InstMatch::merge( InstMatch& m, bool allowSplit ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m.d_map[ d_vars[i] ] );
    }else if( m.d_map[ d_vars[i] ]!=Node::null() ){
      if( d_map[ d_vars[i] ]!=m.d_map[ d_vars[i] ] ){
        //split?
        if( allowSplit ){
          addSplit( d_map[ d_vars[i] ], m.d_map[ d_vars[i] ] );
        }else{
          d_map.clear();
          return false;
        }
      }
    }
  }
  if( allowSplit ){
    //also add splits
    for( std::map< Node, Node >::iterator it = m.d_splits.begin(); it != m.d_splits.end(); ++it ){
      addSplit( it->first, it->second );
    }
  }
  return true;
}

// -1 : keep this, 1 : keep m, 0 : keep both
int InstMatch::checkSubsume( InstMatch& m ){
  bool nsubset1 = true;
  bool nsubset2 = true;
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( m.d_map[ d_vars[i] ]!=d_map[ d_vars[i] ] ){
      if( d_map[ d_vars[i] ]!=Node::null() ){
        nsubset1 = false;
        if( !nsubset2 ) break;
      }
      if( m.d_map[ d_vars[i] ]!=Node::null() ){
        nsubset2 = false;
        if( !nsubset1 ) break;
      }
    }
  }
  if( nsubset1 ){
    return -1;
  }else if( nsubset2 ){
    return 1;
  }else{
    return 0;
  }
}
bool InstMatch::isEqual( InstMatch& m ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( m.d_map[ d_vars[i] ]!=d_map[ d_vars[i] ] ){
      return false;
    }
  }
  return true;
}
void InstMatch::debugPrint( const char* c ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    Debug( c ) << "   " << d_vars[i] << " -> " << d_map[ d_vars[i] ] << std::endl;
  }
  if( !d_splits.empty() ){
    Debug( c ) << "   Conditions: ";
    for( std::map< Node, Node >::iterator it = d_splits.begin(); it !=d_splits.end(); ++it ){
      Debug( c ) << it->first << " = " << it->second << " ";
    }
    Debug( c ) << std::endl;
  }
}
bool InstMatch::isComplete( InstMatch* mbase ){
  Assert( !mbase || getQuantifier()==mbase->getQuantifier() );
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() &&
        ( !mbase || mbase->d_map[ d_vars[i] ]==Node::null() ) ){
      return false;
    }
  }
  return true;
}

void InstMatch::computeTermVec(){
  if( d_computeVec ){
    d_match.clear();
    for( int i=0; i<(int)d_vars.size(); i++ ){
      if( d_map[ d_vars[i] ]!=Node::null() ){
        d_match.push_back( d_map[ d_vars[i] ] );
      }else{
        //if integer or real, make zero
        TypeNode tn = d_vars[i].getType();
        if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
          Rational z(0);
          d_match.push_back( NodeManager::currentNM()->mkConst( z ) );
        }else{
          d_match.push_back( NodeManager::currentNM()->mkVar( tn ) );
        }
      }
    }
    d_computeVec = false;
  }
}

void InstMatch::addSplit( Node n1, Node n2 ){
  if( n2<n1 ){
    Node ntemp = n1;
    n1 = n2;
    n2 = ntemp;
  }
  if( d_splits.find( n1 )!=d_splits.end() ){
    if( d_splits[n1]!=n2 ){
      addSplit( d_splits[n1], n2 );
    }
  }else{
    d_splits[n1] = n2;
  }
}

bool InstMatchGroup::merge( InstMatchGroup& mg )
{
  std::vector< InstMatch > newMatches;
  for( int l=0; l<(int)d_matches.size(); l++ ){
    for( int k=0; k<(int)mg.d_matches.size(); k++ ){
      InstMatch temp( &d_matches[l] );
      if( temp.merge( mg.d_matches[k] ) ){
        newMatches.push_back( temp );
      }
    }
  }
  d_matches.clear();
  d_matches.insert( d_matches.begin(), newMatches.begin(), newMatches.end() );
  removeRedundant();
  return (d_matches.size()>0);
}

void InstMatchGroup::add( InstMatchGroup& mg ){
  if( !mg.d_matches.empty() ){
    d_matches.insert( d_matches.end(), mg.d_matches.begin(), mg.d_matches.end() );
  }
}

void InstMatchGroup::combine( InstMatchGroup& mg ){
  InstMatchGroup temp( this );
  merge( mg );
  add( temp );
  add( mg );
  removeDuplicate();
}

void InstMatchGroup::addComplete( InstMatchGroup& mg, InstMatch* mbase ){
  for( int i=0; i<(int)mg.d_matches.size(); i++ ){
    if( mg.d_matches[i].isComplete( mbase ) ){
      if( mbase ){
        mg.d_matches[i].add( *mbase );
      }
      d_matches.push_back( mg.d_matches[i] );
      mg.d_matches.erase( mg.d_matches.begin() + i, mg.d_matches.begin() + i + 1 );
      i--;
    }
  }
}

void InstMatchGroup::removeRedundant(){
  std::vector< bool > active;
  active.resize( d_matches.size(), true );
  for( int k=0; k<(int)d_matches.size(); k++ ){
    for( int l=(k+1); l<(int)d_matches.size(); l++ ){
      if( k!=l && active[k] && active[l] ){
        int result = d_matches[k].checkSubsume( d_matches[l] );
        if( result==1 ){
          active[k] = false;
        }else if( result==-1 ){
          active[l] = false;
        }
      }
    }
  }
  std::vector< InstMatch > temp;
  temp.insert( temp.begin(), d_matches.begin(), d_matches.end() );
  d_matches.clear();
  for( int i=0; i<(int)temp.size(); i++ ){
    if( active[i] ){
      d_matches.push_back( temp[i] );
    }
  }
}
bool InstMatchGroup::contains( InstMatch& m ){
  for( int k=0; k<(int)d_matches.size(); k++ ){
    if( d_matches[k].isEqual( m ) ){
      return true;
    }
  }
  return false;
}
void InstMatchGroup::removeDuplicate(){
  std::vector< bool > active;
  active.resize( d_matches.size(), true );
  for( int k=0; k<(int)d_matches.size(); k++ ){
    for( int l=(k+1); l<(int)d_matches.size(); l++ ){
      if( k!=l && active[k] && active[l] ){
        if( d_matches[k].isEqual( d_matches[l] ) ){
          active[l] = false;
        }
      }
    }
  }
  std::vector< InstMatch > temp;
  temp.insert( temp.begin(), d_matches.begin(), d_matches.end() );
  d_matches.clear();
  for( int i=0; i<(int)temp.size(); i++ ){
    if( active[i] ){
      d_matches.push_back( temp[i] );
    }
  }
}

void InstMatchGroup::debugPrint( const char* c ){
  for( int j=0; j<(int)d_matches.size(); j++ ){
    Debug( c ) << "Match " << j << " : " << std::endl;
    d_matches[j].debugPrint( c );
  }
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

InstantiationEngine::InstantiationEngine(context::Context* c, TheoryEngine* te):
d_te( te ),
d_active( c ),
d_ic_active( c ){
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_instTable[theoryId] = NULL;
  }
}

bool InstantiationEngine::addLemma( Node lem ){
  //AJR: the following check is necessary until FULL_CHECK is guarenteed after d_out->lemma(...)
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
  Assert( d_vars[f].size()==terms.size() && d_vars[f].size()==(f.getNumChildren()-1) );
  Node body = f[ f.getNumChildren() - 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                                       terms.begin(), terms.end() ); 
  NodeBuilder<> nb(kind::OR);
  nb << f.notNode() << body;
  Node lem = nb;
  if( addLemma( lem ) ){
    Debug("inst-engine") << "*** Instantiate " << f << " with " << std::endl;
    //int maxInstLevel = 0;
    for( int i=0; i<(int)terms.size(); i++ ){
      Assert( !terms[i].hasAttribute(InstConstantAttribute()) );
      Debug("inst-engine") << "   " << terms[i] << std::endl;
      //if( terms[i].hasAttribute((InstLevelAttribute()) &&
      //    terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
      //  maxInstLevel = terms[i].getAttribute(InstLevelAttribute()); 
      //}
    }
    //setInstantiationLevel( body, maxInstLevel+1 );
    return true;
  }else{
    return false;
  }
}

bool InstantiationEngine::addInstantiation( InstMatch* m ){
  //Assert( m->isComplete() );
  m->computeTermVec();
  return addInstantiation( m->getQuantifier(), m->d_match );
}

bool InstantiationEngine::addSplit( Node n ){
  Node lem = NodeManager::currentNM()->mkNode( OR, n, n.notNode() );
  return addLemma( lem );
}

Node InstantiationEngine::getCounterexampleBody( Node f ){
  Assert( f.getKind()==FORALL );
  if( d_counterexample_body.find( f )==d_counterexample_body.end() ){
    for( int i=0; i<(int)f.getNumChildren()-1; i++ ){
      Node ic = NodeManager::currentNM()->mkInstConstant( f[i].getType() );
      d_inst_constants_map[ic] = f;
      d_inst_constants[ f ].push_back( ic );
    }

    //set the counterexample body
    std::vector< Node > vars;
    getVariablesFor( f, vars );
    d_counterexample_body[ f ] = f[ f.getNumChildren() - 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                                            d_inst_constants[ f ].begin(), d_inst_constants[ f ].end() ); 
  }
  return d_counterexample_body[ f ];
}

void InstantiationEngine::getSkolemConstantsFor( Node f, std::vector< Node >& scs ){
  Assert( scs.empty() );
  Assert( f.getKind()==NOT && f[0].getKind()==FORALL );
  if( d_skolem_constants.find( f[0] )==d_skolem_constants.end() ){
    for( int i=0; i<(int)f[0].getNumChildren()-1; i++ ){
      Node ic = NodeManager::currentNM()->mkSkolem( f[0][i].getType() );
      scs.push_back( ic );
    }
    d_skolem_constants[ f[0] ].insert( d_skolem_constants[ f[0] ].begin(), scs.begin(), scs.end() );
  }else{
    scs.insert( scs.begin(), d_skolem_constants[ f[0] ].begin(), d_skolem_constants[ f[0] ].end() );
  }
}

void InstantiationEngine::getVariablesFor( Node f, std::vector< Node >& vars )
{
  Assert( vars.empty() );
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==FORALL ) );
  Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
  if( d_vars.find( quant )==d_vars.end() ){
    for( int i=0; i<(int)quant.getNumChildren()-1; i++ ){
      vars.push_back( quant[i] );
    }
    d_vars[ quant ].insert( d_vars[ quant ].begin(), vars.begin(), vars.end() );
  }else{
    vars.insert( vars.begin(), d_vars[ quant ].begin(), d_vars[ quant ].end() );
  }
}

bool InstantiationEngine::doInstantiation( OutputChannel* out ){
  d_curr_out = out;
  //call instantiators to search for an instantiation
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

void InstantiationEngine::registerLiterals( Node n, Node f, OutputChannel* out )
{
  n = Rewriter::rewrite( n );
  if( n.getKind()==INST_CONSTANT ){
    if( !n.hasAttribute(InstConstantAttribute()) ){
      InstConstantAttribute ica;
      n.setAttribute(ica,f);
    }
  }else{
    Node fa;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerLiterals( n[i], f, out );
      if( n[i].hasAttribute(InstConstantAttribute()) ){
        if( fa!=f ){
          fa = n[i].getAttribute(InstConstantAttribute());
        }
      }
    }
    if( fa!=Node::null() ){
      //set n to have instantiation constants from f
      if( !n.hasAttribute(InstConstantAttribute()) ){
        if( d_te->getPropEngine()->isSatLiteral( n ) && n.getKind()!=NOT ){
          Node cel = getCounterexampleLiteralFor( fa );
          if( n!=cel && n.notNode()!=cel ){
            Debug("quant-dep-dec") << "Make " << n << " dependent on " << cel << std::endl;
            out->dependentDecision( cel, n );
            //Debug("quant-dep-dec") << "Require phase " << n << " to be " << polarity << std::endl;
            //out->requirePhase( n, polarity );
          }
        }
        InstConstantAttribute ica;
        n.setAttribute(ica,fa);
      }
    }
  }
}

void InstantiationEngine::setInstantiationLevel( Node n, int level ){
  if( !n.hasAttribute(InstLevelAttribute()) ){
    InstLevelAttribute ila;
    n.setAttribute(ila,level);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setInstantiationLevel( n[i], level );
  }
}

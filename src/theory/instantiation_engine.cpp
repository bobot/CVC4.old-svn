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
}

bool InstMatch::add( InstMatch& m ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m.d_map[ d_vars[i] ] );
    }
  }
  return true;
}

bool InstMatch::merge( InstMatch& m ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m.d_map[ d_vars[i] ] );
    }else{
      if( m.d_map[ d_vars[i] ]!=Node::null() &&
          d_map[ d_vars[i] ]!=m.d_map[ d_vars[i] ] ){
        d_map.clear();
        return false;
      }
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
    Debug( c )  << "   " << d_vars[i] << " -> " << d_map[ d_vars[i] ] << std::endl;
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
      Assert( d_map[ d_vars[i] ]!=Node::null() );
      d_match.push_back( d_map[ d_vars[i] ] );
    }
    d_computeVec = false;
  }
}

void InstMatch::partialMerge( InstMatch& m, std::map< Node, Node >& splits ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    Node n1 = d_map[ d_vars[i] ];
    Node n2 = m.d_map[ d_vars[i] ];
    if( n1!=Node::null() && n2!=Node::null() && n1!=n2 ){
      if( n1>n2 ){
        splits[n1] = n2;
      }else{
        splits[n2] = n1;
      }
    }
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

void Instantiator::updateStatus( int& currStatus, int addStatus ){
  if( addStatus==Instantiator::STATUS_UNFINISHED ){
    currStatus = Instantiator::STATUS_UNFINISHED;
  }else if( addStatus==Instantiator::STATUS_UNKNOWN ){
    if( currStatus==Instantiator::STATUS_SAT ){
      currStatus = Instantiator::STATUS_UNKNOWN;
    }
  }
}

InstantiationEngine::InstantiationEngine(context::Context* c, TheoryEngine* te):
d_te( te ),
d_active( c ){
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_instTable[theoryId] = NULL;
  }
}

bool InstantiationEngine::addInstantiation( Node f, std::vector< Node >& terms )
{
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==EXISTS ) );
  Assert( !f.hasAttribute(InstConstantAttribute()) );
  Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
  Assert( d_vars[f].size()==terms.size() && d_vars[f].size()==(quant.getNumChildren()-1) );
  Node body = quant[ quant.getNumChildren() - 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                                              terms.begin(), terms.end() ); 
  NodeBuilder<> nb(kind::OR);
  nb << ( f.getKind()==kind::NOT ? f[0] : NodeManager::currentNM()->mkNode( NOT, f ) );
  nb << ( f.getKind()==kind::NOT ? NodeManager::currentNM()->mkNode( NOT, body ) : body );
  Node lem = nb;
  //AJR: the following two lines are necessary until FULL_CHECK is guarenteed after d_out->lemma(...)
  if( addLemma( lem ) ){
    Debug("inst-engine") << "*** Instantiate " << f << " with " << std::endl;
    for( int i=0; i<(int)terms.size(); i++ ){
      Assert( !terms[i].hasAttribute(InstConstantAttribute()) );
      Debug("inst-engine") << "   " << terms[i] << std::endl;
    }
    //associate all nested quantifiers with their counterexample equivalents
    associateNestedQuantifiers( body, d_counterexample_body[f] );
    return true;
  }else{
    return false;
  }
}

bool InstantiationEngine::addInstantiation( InstMatch* m ){
  Assert( m->isComplete() );
  m->computeTermVec();
  return addInstantiation( m->getQuantifier(), m->d_match );
}

bool InstantiationEngine::addLemma( Node lem ){
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

bool InstantiationEngine::addSplit( Node n ){
  Node lem = NodeManager::currentNM()->mkNode( OR, n, n.notNode() );
  return addLemma( lem );
}

void InstantiationEngine::getInstantiationConstantsFor( Node f, std::vector< Node >& ics, Node& cebody ){
  Assert( ics.empty() );
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==EXISTS ) );
  if( d_inst_constants.find( f )==d_inst_constants.end() ){
    Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
    for( int i=0; i<(int)quant.getNumChildren()-1; i++ ){
      Node ic = NodeManager::currentNM()->mkInstConstant( quant[i].getType() );
      d_inst_constants_map[ic] = f;
      ics.push_back( ic );
      ////store in the instantiation constant for the proper instantiator
      //Assert( d_te->theoryOf( ic )!=NULL );
      //theory::Instantiator* tinst = d_instTable[ d_te->theoryOf( ic )->getId() ];
      //if( tinst ){
      //  tinst->d_inst_constants[ f ].push_back( ic );
      //  tinst->d_solved_ic[ ic ] = Node::null();
      //}
    }
    d_inst_constants[ f ].insert( d_inst_constants[ f ].begin(), ics.begin(), ics.end() );

    //set the counterexample body
    std::vector< Node > vars;
    getVariablesFor( f, vars );
    cebody = quant[ quant.getNumChildren() - 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                                             d_inst_constants[ f ].begin(), d_inst_constants[ f ].end() ); 
    d_counterexample_body[ f ] = cebody;
  }else{
    ics.insert( ics.begin(), d_inst_constants[ f ].begin(), d_inst_constants[ f ].end() );
    cebody = d_counterexample_body[ f ];
  }
}

void InstantiationEngine::getSkolemConstantsFor( Node f, std::vector< Node >& scs ){
  Assert( scs.empty() );
  Assert( f.getKind()==EXISTS || ( f.getKind()==NOT && f[0].getKind()==FORALL ) );
  if( d_skolem_constants.find( f )==d_skolem_constants.end() ){
    Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
    for( int i=0; i<(int)quant.getNumChildren()-1; i++ ){
      Node ic = NodeManager::currentNM()->mkSkolem( quant[i].getType() );
      scs.push_back( ic );
    }
    d_skolem_constants[ f ].insert( d_skolem_constants[ f ].begin(), scs.begin(), scs.end() );
  }else{
    scs.insert( scs.begin(), d_skolem_constants[ f ].begin(), d_skolem_constants[ f ].end() );
  }
}

void InstantiationEngine::getVariablesFor( Node f, std::vector< Node >& vars )
{
  Assert( vars.empty() );
  Assert( f.getKind()==FORALL || f.getKind()==EXISTS ||
          ( f.getKind()==NOT && ( f[0].getKind()==FORALL || f[0].getKind()==EXISTS ) ) );
  if( d_vars.find( f )==d_vars.end() ){
    Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
    for( int i=0; i<(int)quant.getNumChildren()-1; i++ ){
      vars.push_back( quant[i] );
    }
    d_vars[ f ].insert( d_vars[ f ].begin(), vars.begin(), vars.end() );
  }else{
    vars.insert( vars.begin(), d_vars[ f ].begin(), d_vars[ f ].end() );
  }
}

bool InstantiationEngine::doInstantiation( OutputChannel* out ){
  d_curr_out = out;
  //call instantiators to search for an instantiation
  Debug("inst-engine") << "Reset instantiation." << std::endl;
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( d_instTable[i] ){
      d_instTable[i]->resetInstantiation();
    }
  }
  int e = 0;
  d_status = Instantiator::STATUS_UNFINISHED;
  d_addedLemma = false;
  while( d_status==Instantiator::STATUS_UNFINISHED ){
    Debug("inst-engine") << "Prepare instantiation (" << e << ")." << std::endl;
    d_status = Instantiator::STATUS_SAT;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] ){
        d_instTable[i]->doInstantiation( e );
        //update status
        Instantiator::updateStatus( d_status, d_instTable[i]->getStatus() );
      }
    }
    if( d_addedLemma ){
      d_status = Instantiator::STATUS_UNKNOWN;
      return true;
    }
    e++;
  }
  return false;
}

Node InstantiationEngine::getCounterexampleLiteralFor( Node n ){
  Assert( n.getKind()==FORALL || ( n.getKind()==NOT && n[0].getKind()==EXISTS ) );
  if( d_counterexamples.find( n )==d_counterexamples.end() ){
    d_counterexamples[n] = NodeManager::currentNM()->mkNode( NO_COUNTEREXAMPLE, n );
  }
  return d_counterexamples[n];
}

void InstantiationEngine::registerLiterals( Node n, Node f, OutputChannel* out )
{
  if( n.getKind()==INST_CONSTANT ){
    if( !n.hasAttribute(InstConstantAttribute()) ){
      InstConstantAttribute icai;
      n.setAttribute(icai,f);
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
      Node nr = Rewriter::rewrite( n );
      if( !nr.hasAttribute(InstConstantAttribute()) ){
        if( d_te->getPropEngine()->isSatLiteral( nr ) && n.getKind()!=NOT ){
          Node cel = getCounterexampleLiteralFor( fa );
          Debug("quant-dep-dec") << "Make " << nr << " dependent on " << cel << std::endl;
          out->dependentDecision( cel, nr );
        }
        InstConstantAttribute icai;
        nr.setAttribute(icai,fa);
      }
    }
  }
}

void InstantiationEngine::associateNestedQuantifiers( Node n, Node cen )
{
  if( n.getKind()==FORALL || n.getKind()==EXISTS ){
    d_quant_to_ceq[n] = cen.notNode();
    d_quant_to_ceq[n.notNode()] = cen; 
  }else if (n.getKind()==NOT && ( n[0].getKind()==FORALL || n[0].getKind()==EXISTS ) ){
    d_quant_to_ceq[n] = cen[0];
    d_quant_to_ceq[n[0]] = cen; 
  }else if( n.getKind()==cen.getKind() && n.getNumChildren()==cen.getNumChildren() ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      associateNestedQuantifiers( n[i], cen[i] );
    }
  }
}

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
  for( int i=0; i<(int)ie->d_inst_constants[f].size(); i++ ){
    d_vars.push_back( ie->d_inst_constants[f][i] );
  }
}
InstMatch::InstMatch( InstMatch* m ){
  d_vars.insert( d_vars.begin(), m->d_vars.begin(), m->d_vars.end() );
  add( m );
}

void InstMatch::add( InstMatch* m ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m->d_map[ d_vars[i] ] );
    }
  }
}

bool InstMatch::merge( InstMatch* m ){
  std::map< Node, Node > temp = d_map;
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( d_map[ d_vars[i] ]==Node::null() ){
      setMatch( d_vars[i], m->d_map[ d_vars[i] ] );
    }else{
      if( m->d_map[ d_vars[i] ]!=Node::null() &&
          d_map[ d_vars[i] ]!=m->d_map[ d_vars[i] ] ){
        d_map = temp;
        return false;
      }
    }
  }
  return true;
}

// -1 : keep this, 1 : keep m, 0 : keep both
int InstMatch::checkSubsume( InstMatch* m ){
  bool nsubset1 = true;
  bool nsubset2 = true;
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( m->d_map[ d_vars[i] ]!=d_map[ d_vars[i] ] ){
      if( d_map[ d_vars[i] ]!=Node::null() ){
        nsubset1 = false;
        if( !nsubset2 ) break;
      }
      if( m->d_map[ d_vars[i] ]!=Node::null() ){
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
bool InstMatch::isEqual( InstMatch* m ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    if( m->d_map[ d_vars[i] ]!=d_map[ d_vars[i] ] ){
      return false;
    }
  }
  return true;
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

void InstMatch::debugPrint( const char* c ){
  for( int i=0; i<(int)d_vars.size(); i++ ){
    Debug( c )  << "   " << d_vars[i] << " -> " << d_map[ d_vars[i] ] << std::endl;
  }
}

bool InstMatchGroup::merge( InstMatchGroup& mg )
{
  std::vector< InstMatch* > newMatches;
  for( int l=0; l<(int)d_matches.size(); l++ ){
    InstMatch* temp = new InstMatch( d_matches[l] );
    for( int k=0; k<(int)mg.d_matches.size(); k++ ){
      if( temp->merge( mg.d_matches[k] ) ){
        newMatches.push_back( temp );
        temp = new InstMatch( d_matches[l] );
      }
    }
    //delete temp;
  }
  if( newMatches.size()>0 ){
    //for( int i=0; i<(int)d_matches.size(); i++ ){
    //  delete d_matches[i];
    //}
    d_matches.clear();
    d_matches.insert( d_matches.begin(), newMatches.begin(), newMatches.end() );
    removeRedundant();
    return true;
  }else{
    return false;
  }
}

void InstMatchGroup::add( InstMatchGroup& mg ){
  if( !mg.d_matches.empty() ){
    d_matches.insert( d_matches.end(), mg.d_matches.begin(), mg.d_matches.end() );
  }
}

void InstMatchGroup::combine( InstMatchGroup& mg ){
  InstMatchGroup temp( this );
  if( merge( mg ) ){
    add( temp );
  }
  add( mg );
  removeDuplicate();
}

void InstMatchGroup::addComplete( InstMatchGroup& mg, InstMatch* mbase ){
  for( int i=0; i<(int)mg.d_matches.size(); i++ ){
    if( mg.d_matches[i]->isComplete( mbase ) ){
      if( mbase ){
        mg.d_matches[i]->add( mbase );
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
        int result = d_matches[k]->checkSubsume( d_matches[l] );
        if( result==1 ){
          active[k] = false;
        }else if( result==-1 ){
          active[l] = false;
        }
      }
    }
  }
  std::vector< InstMatch* > temp;
  temp.insert( temp.begin(), d_matches.begin(), d_matches.end() );
  d_matches.clear();
  for( int i=0; i<(int)temp.size(); i++ ){
    if( active[i] ){
      d_matches.push_back( temp[i] );
    }else{
      //delete temp[i];
    }
  }
}
void InstMatchGroup::removeDuplicate(){
  std::vector< bool > active;
  active.resize( d_matches.size(), true );
  for( int k=0; k<(int)d_matches.size(); k++ ){
    for( int l=(k+1); l<(int)d_matches.size(); l++ ){
      if( k!=l && active[k] && active[l] ){
        if( d_matches[k]->isEqual( d_matches[l] ) ){
          active[l] = false;
        }
      }
    }
  }
  std::vector< InstMatch* > temp;
  temp.insert( temp.begin(), d_matches.begin(), d_matches.end() );
  d_matches.clear();
  for( int i=0; i<(int)temp.size(); i++ ){
    if( active[i] ){
      d_matches.push_back( temp[i] );
    }else{
      //delete temp[i];
    }
  }
}

void InstMatchGroup::debugPrint( const char* c ){
  for( int j=0; j<(int)d_matches.size(); j++ ){
    Debug( c ) << "Match " << j << " : " << std::endl;
    d_matches[j]->debugPrint( c );
  }
}


Instantiator::Instantiator(context::Context* c, InstantiationEngine* ie) : 
d_instEngine( ie ){

}

Instantiator::~Instantiator(){
}

InstantiationEngine::InstantiationEngine(context::Context* c, TheoryEngine* te):
d_te( te ),
d_active( c ){
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_instTable[theoryId] = NULL;
  }
}

bool InstantiationEngine::instantiate( Node f, std::vector< Node >& terms, OutputChannel* out )
{
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==EXISTS ) );
  Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
  Assert( d_vars[f].size()==terms.size() && d_vars[f].size()==(quant.getNumChildren()-1) );
  Node body = quant[ quant.getNumChildren() - 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                                              terms.begin(), terms.end() ); 
  NodeBuilder<> nb(kind::OR);
  nb << ( f.getKind()==kind::NOT ? f[0] : NodeManager::currentNM()->mkNode( NOT, f ) );
  nb << ( f.getKind()==kind::NOT ? NodeManager::currentNM()->mkNode( NOT, body ) : body );
  Node lem = nb;
  if( d_lemmas_produced.find( lem )==d_lemmas_produced.end() ){
    Debug("inst-engine") << "Instantiate " << f << " with " << std::endl;
    for( int i=0; i<(int)terms.size(); i++ ){
      Assert( !terms[i].hasAttribute(InstantitionConstantAttribute()) );
      Debug("inst-engine") << "   " << terms[i] << std::endl;
    }
    Debug("inst-engine-debug") << "Instantiation lemma : " << lem << std::endl;
    out->lemma( lem );
    d_lemmas_produced[ lem ] = true;
    //if the quantifier or any term has instantiation constants, then mark terms as dependent
    if( f.hasAttribute(InstantitionConstantAttribute()) ){
      registerLiterals( body, f, out );
    }

    //associate all nested quantifiers with their counterexample equivalents
    associateNestedQuantifiers( body, d_counterexample_body[f] );
    return true;
  }else{
    return false;
  }
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
  //call instantiators to search for an instantiation
  Debug("inst-engine") << "Reset instantiation." << std::endl;
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( d_instTable[i] ){
      d_instTable[i]->resetInstantiation();
    }
  }
  for( int e=0; e<=3; e++ ){
    Debug("inst-engine") << "Prepare instantiation (" << e << ")." << std::endl;
    bool retVal = false;
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] ){
        d_instTable[i]->prepareInstantiation( (Instantiator::Effort)e );
        //do instantiations
        for( int j=0; j<(int)d_instTable[i]->getNumMatches(); j++ ){
          //do instantiation
          InstMatch* m = d_instTable[i]->getMatch( j );
          Assert( m->isComplete() );
          m->computeTermVec();
          if( instantiate( m->getQuantifier(), m->d_match, out ) ){
            retVal = true;
          }
        }
        d_instTable[i]->clearMatches();
        //add lemmas
        for( int j=0; j<(int)d_instTable[i]->getNumLemmas(); j++ ){
          Node lem = Rewriter::rewrite(d_instTable[i]->getLemma( j ));
          if( d_lemmas_produced.find( lem )==d_lemmas_produced.end() ){
            Debug("inst-engine") << "Add lemma : " << lem << std::endl;
            d_lemmas_produced[ lem ] = true;
            out->split( lem );
            retVal = true;
          }
        }
        d_instTable[i]->clearLemmas();
      }
    }
    if( retVal ){
      return true;
    }
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
    if( !n.hasAttribute(InstantitionConstantAttribute()) ){
      InstantitionConstantAttribute icai;
      n.setAttribute(icai,f);
    }
  }else{
    Node fa;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerLiterals( n[i], f, out );
      if( n[i].hasAttribute(InstantitionConstantAttribute()) ){
        if( fa!=f ){
          fa = n[i].getAttribute(InstantitionConstantAttribute());
        }
      }
    }
    if( fa!=Node::null() ){
      //set n to have instantiation constants from f
      Node nr = Rewriter::rewrite( n );
      if( !nr.hasAttribute(InstantitionConstantAttribute()) ){
        if( d_te->getPropEngine()->isSatLiteral( nr ) && n.getKind()!=NOT ){
          Node cel = getCounterexampleLiteralFor( fa );
          Debug("inst-engine-debug") << "Make " << nr << " dependent on " << cel << std::endl;
          out->dependentDecision( cel, nr );
        }
        InstantitionConstantAttribute icai;
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

bool InstantiationEngine::isSubQuantifier( Node sub, Node f ){
  //DO_THIS
  return sub==f;
}

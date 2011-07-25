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

Instantiatior::Instantiatior(context::Context* c, InstantiationEngine* ie) : 
d_ie( ie ){

}

Instantiatior::~Instantiatior(){
}

bool Instantiatior::isInstantiationReady( Node n ){
  Assert( d_inst_constants.find( n )!=d_inst_constants.end() );
  for( int i=0; i<(int)d_inst_constants[n].size(); i++ ){
    if( d_solved_ic[d_inst_constants[n][i]]==Node::null() ){
      return false;
    }
  }
  return true;
}

InstantiationEngine::InstantiationEngine(context::Context* c, TheoryEngine* te):
d_te( te ){
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_instTable[theoryId] = NULL;
  }
}

void InstantiationEngine::instantiate( Node f, std::vector< Node >& terms, OutputChannel* out )
{
  //TODO: assert that no t in terms has instantiation constants from f

  bool hasInstConst = f.hasAttribute(InstantitionConstantAttribute());
  Debug("inst-engine") << "Instantiate " << f << " with " << std::endl;
  for( int i=0; i<(int)terms.size(); i++ ){
    Debug("inst-engine") << "   " << terms[i] << std::endl;
    hasInstConst = hasInstConst || terms[i].hasAttribute(InstantitionConstantAttribute());
  }
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==EXISTS ) );
  Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
  Assert( d_vars[f].size()==terms.size() && d_vars[f].size()==(quant.getNumChildren()-1) );
  Node body = quant[ quant.getNumChildren() - 1 ].substitute( d_vars[f].begin(), d_vars[f].end(), 
                                                              terms.begin(), terms.end() ); 
  NodeBuilder<> nb(kind::OR);
  nb << ( f.getKind()==kind::NOT ? f[0] : NodeManager::currentNM()->mkNode( NOT, f ) );
  nb << ( f.getKind()==kind::NOT ? NodeManager::currentNM()->mkNode( NOT, body ) : body );
  Node lem = nb;
  Debug("inst-engine-debug") << "Instantiation lemma : " << lem << std::endl;
  out->lemma( lem );

  //if the quantifier or any term has instantiation constants, then mark terms as dependent
  if( hasInstConst ){
    Node cel = getCounterexampleLiteralFor( f );
    markLiteralsAsDependent( body, f, cel, out );
  }
}

void InstantiationEngine::getInstantiationConstantsFor( Node f, std::vector< Node >& vars, 
                                                        std::vector< Node >& ics ){
  Assert( vars.empty() && ics.empty() );
  Assert( f.getKind()==FORALL || ( f.getKind()==NOT && f[0].getKind()==EXISTS ) );
  if( d_inst_constants.find( f )==d_inst_constants.end() ){
    Node quant = ( f.getKind()==kind::NOT ? f[0] : f );
    std::map< Theory*, std::map< Node, Node > > instMap;
    for( int i=0; i<(int)quant.getNumChildren()-1; i++ ){
      vars.push_back( quant[i] );
      Node ic = NodeManager::currentNM()->mkInstConstant( quant[i].getType() );
      d_inst_constants_map[ic] = f;
      ics.push_back( ic );
      //store in the instantiation constant for the proper instantiator
      Assert( d_te->theoryOf( ic )!=NULL );
      theory::Instantiatior* tinst = d_instTable[ d_te->theoryOf( ic )->getId() ];
      if( tinst ){
        tinst->d_inst_constants[ f ].push_back( ic );
        tinst->d_solved_ic[ ic ] = Node::null();
      }
    }
    d_vars[ f ].insert( d_vars[ f ].begin(), vars.begin(), vars.end() );
    d_inst_constants[ f ].insert( d_inst_constants[ f ].begin(), ics.begin(), ics.end() );
  }else{
    vars.insert( vars.begin(), d_vars[ f ].begin(), d_vars[ f ].end() );
    ics.insert( ics.begin(), d_inst_constants[ f ].begin(), d_inst_constants[ f ].end() );
  }
}

bool InstantiationEngine::doInstantiation( OutputChannel* out ){
  //call instantiators to search for an instantiation
  Debug("inst-engine") << "Prepare instantiation." << std::endl;
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( d_instTable[i] ){
      d_instTable[i]->prepareInstantiation();
    }
  }
  //check whether any quantifier is instantiation-ready, and if so, add the instantiation clause as a lemma
  bool retVal = false;
  for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); it!=d_inst_constants.end(); ++it ){
    bool instReady = true;
    for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
      Assert( d_te->theoryOf( *it2 )!=NULL );
      if( d_instTable[ d_te->theoryOf( *it2 )->getId() ]->d_solved_ic[ *it2 ]==Node::null() ){
        instReady = false;
        break;
      }
    }
    if( instReady ){
      std::vector< Node > terms;
      for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
        terms.push_back( d_instTable[ d_te->theoryOf( *it2 )->getId() ]->d_solved_ic[ *it2 ] );
      }
      instantiate( it->first, terms, out );
      retVal = true;
    }
  }
  //otherwise, add splitting lemmas
  if( !retVal ){
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] ){
        for( int j=0; j<(int)d_instTable[i]->getNumLemmas(); j++ ){
          Node lem = d_instTable[i]->getLemma( j );
          Debug("inst-engine") << "Split on : " << lem << std::endl;

         //NodeBuilder<> nb(kind::OR);
         // nb << lem << lem.notNode();
         // lem = nb; 
          out->split( lem );
          Debug("inst-engine-debug") << "require phase for " << lem << std::endl;
          out->requirePhase( lem, true );

          retVal = true;
        }
        d_instTable[i]->clearLemmas();
      }
    }
  }
  return retVal;
}

Node InstantiationEngine::getCounterexampleLiteralFor( Node n ){
  Assert( n.getKind()==FORALL || ( n.getKind()==NOT && n[0].getKind()==EXISTS ) );
  if( d_counterexamples.find( n )==d_counterexamples.end() ){
    d_counterexamples[n] = NodeManager::currentNM()->mkNode( NO_COUNTEREXAMPLE, n );
  }
  return d_counterexamples[n];
}

bool InstantiationEngine::markLiteralsAsDependent( Node n, Node f, Node cel, OutputChannel* out )
{
  if( n.getKind()==INST_CONSTANT ){
    InstantitionConstantAttribute icai;
    n.setAttribute(icai,f);
    return true;
  }else{
    bool retVal = false;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( markLiteralsAsDependent( n[i], f, cel, out ) ){
        retVal = true;
      }
    }
    if( retVal ){
      //set n to have instantiation constants from f
      InstantitionConstantAttribute icai;
      if( d_te->getPropEngine()->isSatLiteral( n ) && n.getKind()!=NOT && !n.hasAttribute(icai) ){
        Debug("inst-engine-debug") << "Make " << n << " dependent on " << cel << std::endl;
        out->dependentDecision( cel, n );
      }
      n.setAttribute(icai,f);
    }
    return retVal;
  }
}

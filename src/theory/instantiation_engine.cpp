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
d_instEngine( ie ){

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
d_te( te ),
d_active( c ){
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_instTable[theoryId] = NULL;
  }
}

void InstantiationEngine::instantiate( Node f, std::vector< Node >& terms, OutputChannel* out )
{
  Debug("inst-engine") << "Instantiate " << f << " with " << std::endl;
  for( int i=0; i<(int)terms.size(); i++ ){
    Assert( !terms[i].hasAttribute(InstantitionConstantAttribute()) );
    Debug("inst-engine") << "   " << terms[i] << std::endl;
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
  if( f.hasAttribute(InstantitionConstantAttribute()) ){
    registerLiterals( body, f, out );
  }

  //associate all nested quantifiers with their counterexample equivalents
  associateNestedQuantifiers( body, d_counterexample_body[f] );
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
      //store in the instantiation constant for the proper instantiator
      Assert( d_te->theoryOf( ic )!=NULL );
      theory::Instantiatior* tinst = d_instTable[ d_te->theoryOf( ic )->getId() ];
      if( tinst ){
        tinst->d_inst_constants[ f ].push_back( ic );
        tinst->d_solved_ic[ ic ] = Node::null();
      }
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
  Debug("inst-engine") << "Prepare instantiation." << std::endl;
  for( int i=0; i<theory::THEORY_LAST; i++ ){
    if( d_instTable[i] ){
      d_instTable[i]->prepareInstantiation();
    }
  }
  //check whether any quantifier is instantiation-ready, and if so, add the instantiation clause as a lemma
  bool retVal = false;
  for( std::map< Node, std::vector< Node > >::iterator it = d_inst_constants.begin(); it!=d_inst_constants.end(); ++it ){
    if( getActive( it->first ) ){
      bool instReady = true;
      for( std::vector< Node >::iterator it2 = it->second.begin(); it2!=it->second.end(); ++it2 ){
        Assert( d_te->theoryOf( *it2 )!=NULL );
        if( d_instTable[ d_te->theoryOf( *it2 )->getId() ]->d_solved_ic[ *it2 ]==Node::null() ){
          Debug("inst-engine-debug") << it->first << " is not ready because of " << *it2 << std::endl;
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
    }else{
      Debug("inst-engine-debug") << it->first << " is not active" << std::endl;
    }
  }
  //otherwise, add splitting lemmas
  if( !retVal ){
    for( int i=0; i<theory::THEORY_LAST; i++ ){
      if( d_instTable[i] ){
        for( int j=0; j<(int)d_instTable[i]->getNumLemmas(); j++ ){
          Node lem = Rewriter::rewrite(d_instTable[i]->getLemma( j ));
          Debug("inst-engine") << "Split on : " << lem << std::endl;

         //NodeBuilder<> nb(kind::OR);
         // nb << lem << lem.notNode();
         // lem = nb; 
          out->split( lem );
          Assert( d_te->getPropEngine()->isSatLiteral( lem ) );
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

bool InstantiationEngine::isSubQuantifier( Node sub, Node f )
{
  //DO_THIS
  return sub==f;
}

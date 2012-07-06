/*********************                                                        */
/*! \file relevant_domain.cpp
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
 ** \brief Implementation of relevant domain class
 **/

#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/first_order_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

RelevantDomain::RelevantDomain( QuantifiersEngine* qe ) : d_quantEngine( qe ){

}

void RelevantDomain::compute(){
  d_quant_inst_domain.clear();
  for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
    d_quant_inst_domain[f].resize( f[0].getNumChildren() );
  }
  //add ground terms to domain (rule 1 of complete instantiation essentially uf fragment)
  for( std::map< Node, uf::UfModel >::iterator it = d_quantEngine->getModel()->d_uf_model.begin();
       it != d_quantEngine->getModel()->d_uf_model.end(); ++it ){
    Node op = it->first;
    for( int i=0; i<(int)it->second.d_ground_asserts.size(); i++ ){
      Node n = it->second.d_ground_asserts[i];
      //add arguments to domain
      for( int j=0; j<(int)n.getNumChildren(); j++ ){
        if( d_quantEngine->getModel()->d_ra.hasType( n[j].getType() ) ){
          Node ra = d_quantEngine->getModel()->getRepresentative( n[j] );
          int raIndex = d_quantEngine->getModel()->d_ra.getIndexFor( ra );
          Assert( raIndex!=-1 );
          if( std::find( d_active_domain[op][j].begin(), d_active_domain[op][j].end(), raIndex )==d_active_domain[op][j].end() ){
            d_active_domain[op][j].push_back( raIndex );
          }
        }
      }
    }
  }
  //find fixed point for relevant domain computation
  bool success;
  do{
    success = true;
    for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
      //compute the domain of relevant instantiations (rule 3 of complete instantiation, essentially uf fragment)
      if( computeRelevantInstantiationDomain( d_quantEngine->getCounterexampleBody( f ), Node::null(), -1, d_quant_inst_domain[f] ) ){
        success = false;
      }
      //extend the possible domain for functions (rule 2 of complete instantiation, essentially uf fragment)
      RepDomain range;
      if( extendFunctionDomains( d_quantEngine->getCounterexampleBody( f ), range ) ){
        success = false;
      }
    }
  }while( !success );
}

bool RelevantDomain::computeRelevantInstantiationDomain( Node n, Node parent, int arg, std::vector< RepDomain >& rd ){
  bool domainChanged = false;
  if( n.getKind()==INST_CONSTANT ){
    bool domainSet = false;
    int vi = n.getAttribute(InstVarNumAttribute());
    Assert( !parent.isNull() );
    if( parent.getKind()==APPLY_UF ){
      //if the child of APPLY_UF term f( ... ), only consider the active domain of f at given argument
      Node op = parent.getOperator();
      if( d_quantEngine->getModel()->d_uf_model.find( op )!=d_quantEngine->getModel()->d_uf_model.end() ){
        for( size_t i=0; i<d_active_domain[op][arg].size(); i++ ){
          int d = d_active_domain[op][arg][i];
          if( std::find( rd[vi].begin(), rd[vi].end(), d )==rd[vi].end() ){
            rd[vi].push_back( d );
            domainChanged = true;
          }
        }
        domainSet = true;
      }
    }
    if( !domainSet ){
      //otherwise, we must consider the entire domain
      TypeNode tn = n.getType();
      Assert( d_quantEngine->getModel()->d_ra.hasType( tn ) );
      if( rd[vi].size()!=d_quantEngine->getModel()->d_ra.d_type_reps[tn].size() ){
        rd[vi].clear();
        for( size_t i=0; i<d_quantEngine->getModel()->d_ra.d_type_reps[tn].size(); i++ ){
          rd[vi].push_back( i );
          domainChanged = true;
        }
      }
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( computeRelevantInstantiationDomain( n[i], n, i, rd ) ){
        domainChanged = true;
      }
    }
  }
  return domainChanged;
}

bool RelevantDomain::extendFunctionDomains( Node n, RepDomain& range ){
  if( n.getKind()==INST_CONSTANT ){
    Node f = n.getAttribute(InstConstantAttribute());
    int index = n.getAttribute(InstVarNumAttribute());
    range.insert( range.begin(), d_quant_inst_domain[f][index].begin(), d_quant_inst_domain[f][index].end() );
    return false;
  }else{
    Node op;
    if( n.getKind()==APPLY_UF ){
      op = n.getOperator();
    }
    bool domainChanged = false;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      RepDomain childRange;
      if( extendFunctionDomains( n[i], childRange ) ){
        domainChanged = true;
      }
      if( n.getKind()==APPLY_UF ){
        for( int j=0; j<(int)childRange.size(); j++ ){
          int v = childRange[j];
          if( std::find( d_active_domain[op][i].begin(), d_active_domain[op][i].end(), v )==d_active_domain[op][i].end() ){
            d_active_domain[op][i].push_back( v );
            domainChanged = true;
          }
        }
      }
    }
    //get the range
    if( n.hasAttribute(InstConstantAttribute()) ){
      if( n.getKind()==APPLY_UF ){
        range.insert( range.end(), d_quantEngine->getModel()->d_uf_model[op].d_active_range.begin(),
                                   d_quantEngine->getModel()->d_uf_model[op].d_active_range.end() );
      }
    }else{
      Node r = d_quantEngine->getModel()->getRepresentative( n );
      range.push_back( d_quantEngine->getModel()->d_ra.getIndexFor( r ) );
    }
    return domainChanged;
  }
}
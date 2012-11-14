/*********************                                                        */
/*! \file inst_match.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: bobot
 ** Minor contributors (to current version): barrett, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of inst match class
 **/

#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {
namespace theory {
namespace inst {

InstMatch::InstMatch() {
}

InstMatch::InstMatch( InstMatch* m ) {
  d_map = m->d_map;
}

bool InstMatch::setMatch( EqualityQuery* q, TNode v, TNode m, bool & set ){
  std::map< Node, Node >::iterator vn = d_map.find( v );
  if( vn==d_map.end() || vn->second.isNull() ){
    set = true;
    this->set(v,m);
    Debug("matching-debug") << "Add partial " << v << "->" << m << std::endl;
    return true;
  }else{
    set = false;
    return q->areEqual( vn->second, m );
  }
}

bool InstMatch::setMatch( EqualityQuery* q, TNode v, TNode m ){
  bool set;
  return setMatch(q,v,m,set);
}

bool InstMatch::add( InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( !it->second.isNull() ){
      std::map< Node, Node >::iterator itf = d_map.find( it->first );
      if( itf==d_map.end() || itf->second.isNull() ){
        d_map[it->first] = it->second;
      }
    }
  }
  return true;
}

bool InstMatch::merge( EqualityQuery* q, InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( !it->second.isNull() ){
      std::map< Node, Node >::iterator itf = d_map.find( it->first );
      if( itf==d_map.end() || itf->second.isNull() ){
        d_map[ it->first ] = it->second;
      }else{
        if( !q->areEqual( it->second, itf->second ) ){
          d_map.clear();
          return false;
        }
      }
    }
  }
  return true;
}

void InstMatch::debugPrint( const char* c ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    Debug( c ) << "   " << it->first << " -> " << it->second << std::endl;
  }
  //if( !d_splits.empty() ){
  //  Debug( c ) << "   Conditions: ";
  //  for( std::map< Node, Node >::iterator it = d_splits.begin(); it !=d_splits.end(); ++it ){
  //    Debug( c ) << it->first << " = " << it->second << " ";
  //  }
  //  Debug( c ) << std::endl;
  //}
}

void InstMatch::makeComplete( Node f, QuantifiersEngine* qe ){
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Node ic = qe->getTermDatabase()->getInstantiationConstant( f, i );
    if( d_map.find( ic )==d_map.end() ){
      d_map[ ic ] = qe->getTermDatabase()->getFreeVariableForInstConstant( ic );
    }
  }
}

void InstMatch::makeInternalRepresentative( QuantifiersEngine* qe ){
  EqualityQueryQuantifiersEngine* eqqe = (EqualityQueryQuantifiersEngine*)qe->getEqualityQuery();
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    d_map[ it->first ] = eqqe->getInternalRepresentative( it->second );
  }
}

void InstMatch::makeRepresentative( QuantifiersEngine* qe ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    if( qe->getEqualityQuery()->getEngine()->hasTerm( it->second ) ){
      d_map[ it->first ] = qe->getEqualityQuery()->getEngine()->getRepresentative( it->second );
    }
  }
}

void InstMatch::applyRewrite(){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    it->second = Rewriter::rewrite(it->second);
  }
}

/** get value */
Node InstMatch::getValue( Node var ) const{
  std::map< Node, Node >::const_iterator it = d_map.find( var );
  if( it!=d_map.end() ){
    return it->second;
  }else{
    return Node::null();
  }
}

/** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
void InstMatchTrie::addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index, ImtIndexOrder* imtio ){
  if( long(index)<long(f[0].getNumChildren()) && ( !imtio || long(index)<long(imtio->d_order.size()) ) ){
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.getValue( qe->getTermDatabase()->getInstantiationConstant( f, i_index ) );
    d_data[n].addInstMatch2( qe, f, m, index+1, imtio );
  }
}

/** exists match */
bool InstMatchTrie::existsInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, int index, ImtIndexOrder* imtio ){
  if( long(index)==long(f[0].getNumChildren()) || ( imtio && long(index)==long(imtio->d_order.size()) ) ){
    return true;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.getValue( qe->getTermDatabase()->getInstantiationConstant( f, i_index ) );
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      if( it->second.existsInstMatch2( qe, f, m, modEq, modInst, index+1, imtio ) ){
        return true;
      }
    }
    //check if m is an instance of another instantiation if modInst is true
    if( modInst ){
      if( !n.isNull() ){
        Node nl;
        it = d_data.find( nl );
        if( it!=d_data.end() ){
          if( it->second.existsInstMatch2( qe, f, m, modEq, modInst, index+1, imtio ) ){
            return true;
          }
        }
      }
    }
    if( modEq ){
      //check modulo equality if any other instantiation match exists
      if( !n.isNull() && qe->getEqualityQuery()->getEngine()->hasTerm( n ) ){
        eq::EqClassIterator eqc( qe->getEqualityQuery()->getEngine()->getRepresentative( n ),
                                 qe->getEqualityQuery()->getEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en!=n ){
            std::map< Node, InstMatchTrie >::iterator itc = d_data.find( en );
            if( itc!=d_data.end() ){
              if( itc->second.existsInstMatch2( qe, f, m, modEq, modInst, index+1, imtio ) ){
                return true;
              }
            }
          }
          ++eqc;
        }
      }
    }
    return false;
  }
}

bool InstMatchTrie::existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, ImtIndexOrder* imtio ){
  return existsInstMatch2( qe, f, m, modEq, modInst, 0, imtio );
}

bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, bool modInst, ImtIndexOrder* imtio ){
  if( !existsInstMatch( qe, f, m, modEq, modInst, imtio ) ){
    addInstMatch2( qe, f, m, 0, imtio );
    return true;
  }else{
    return false;
  }
}


}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

/*********************                                                        */
/*! \file inst_match.h
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
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_MATCH_IMPL_H
#define __CVC4__INST_MATCH_IMPL_H

#include "theory/inst_match.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/uf/theory_uf_candidate_generator.h"
#include "theory/uf/equality_engine_impl.h"

namespace CVC4 {
namespace theory {


template<bool modEq>
InstMatchTrie2<modEq>::InstMatchTrie2(context::Context* c,  QuantifiersEngine* qe):
  d_mods(c), d_data(0){
  d_eQ = qe->getEqualityQuery();
  d_eE = ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine();
};

/** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
template<bool modEq>
void InstMatchTrie2<modEq>::addSubTree( Tree * root, mapIter current, mapIter end ) {
  if( current != end ){
    Assert(!current->second.isNull());
    Tree * & root2 = root->e[current->second];
    if(root2 == NULL) root2 = new Tree(root->level + 1);
    addSubTree(root2, ++current, end );
  }
}

/** exists match */
template<bool modEq>
bool InstMatchTrie2<modEq>::existsInstMatch(InstMatchTrie2<modEq>::Tree * root,
                                            mapIter current, mapIter end,
                                            Tree * & e, mapIter & diverge) const{
  if( current == end ) return true; //Already their

  if (current->second > diverge->second){
    // this point is the deepest point currently seen
    e = root;
    diverge = current;
  };

  TNode n = current->second;
  typename InstMatchTrie2<modEq>::Tree::MLevel::iterator it =
    root->e.find( n );
  if( it!=root->e.end() &&
      existsInstMatch( (*it).second, ++current, end, e, diverge) )
    return true;

  // Even if n is in the trie others of the equivalence class
  // can also be in it since the equality can have appeared
  // after they have been added
  if( modEq && d_eE->hasTerm( n ) ){
    //check modulo equality if any other instantiation match exists
    uf::EqClassIterator eqc =
      uf::EqClassIterator( d_eQ->getRepresentative( n ), d_eE );
    for( ;!eqc.isFinished();++eqc ){
      TNode en = (*eqc);
      if( en == n ) break; // already tested
      typename InstMatchTrie2<modEq>::Tree::MLevel::iterator itc =
        root->e.find( en );
      if( itc!=root->e.end() &&
          existsInstMatch( (*itc).second, ++current, end, e, diverge) )
        return true;
    }
  }
  return false;
}
template<bool modEq>
bool InstMatchTrie2<modEq>::addInstMatch( InstMatch& m ) {
 mapIter begin = m.d_map.begin();
 mapIter end = m.d_map.end();
 InstMatchTrie2<modEq>::Tree * e = &d_data;
 mapIter diverge = begin;
 if( !existsInstMatch(e, begin, end, e, diverge ) ){
   //std::cout << "~Exists, add." << std::endl;
   Assert(!diverge->second.isNull());
   addSubTree( e, diverge, end );
   d_mods.push_back(make_pair(e,diverge->second));
   return true;
 }else{
   //std::cout << "Exists, fail." << std::endl;
   return false;
 }
}

}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /*  __CVC4__INST_MATCH_IMPL_H */

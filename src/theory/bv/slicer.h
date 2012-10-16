/*********************                                                        */
/*! \file slicer.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__SLICER_BV_H
#define __CVC4__THEORY__BV__SLICER_BV_H


namespace CVC4 {
namespace theory {
namespace bv {

typedef std::vector<uint32_t> Base; 
typedef __gnu_cxx::hash_map<TNode, Base, TNodeHashFunction> BaseMap; 
typedef __gnu_cxx::hash_map<TNode, std::vector<TNode>, TNodeHashFunction > EqualityMap; 

class Slicer {
  std::vector<TNode> d_equalities;
  BaseMap d_bases;
  EqualityMap d_equalityMap; 
  
  
public:
  void Slicer();
  /** 
   * Process the given equality. The equality should not contain terms
   * have an extract over an axtract. 
   * 
   * @param node 
   */
  void addEquality(TNode node);
  void computeCoarsestBase(); 

private:
  

} /* Slicer class */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__SLICER_BV_H */

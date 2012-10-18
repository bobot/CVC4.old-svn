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

#include <vector>
#include <list>
#include <ext/hash_map>
#include "expr/node.h"

#ifndef __CVC4__THEORY__BV__SLICER_BV_H
#define __CVC4__THEORY__BV__SLICER_BV_H


namespace CVC4 {

class Integer;

namespace theory {
namespace bv {

typedef CVC4::Integer Base; 
typedef __gnu_cxx::hash_map<TNode, Base, TNodeHashFunction> BaseMap; 
typedef __gnu_cxx::hash_map<TNode, std::list<TNode>*, TNodeHashFunction > EqualityGraph; 
typedef __gnu_cxx::hash_map<TNode, std::list<TNode>*, TNodeHashFunction >::iterator EqualityGraphIterator; 
class Slicer {
  std::vector<TNode> d_equalities;
  BaseMap d_bases;
  EqualityGraph d_edgeMap; 
  
public:
  Slicer();
  void computeCoarsestBase();
  /** 
   * Takes an equality that is of the following form:
   *          a1 a2 ... an = b1 b2 ... bk
   * where ai, and bi are either variables or extracts over variables,
   * and consecutive extracts have been merged. 
   * 
   * @param node 
   */
  void processEquality(TNode node); 
private:
  void processSimpleEquality(TNode node);
  void splitEqualities(TNode node, std::vector<Node>& equalities);
  TNode addSimpleTerm(TNode t);
  void addEqualityEdge(TNode n1, TNode n2);
  Base getBase(TNode node);
  void updateBase(TNode node, const Base& base);


}; /* Slicer class */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__SLICER_BV_H */

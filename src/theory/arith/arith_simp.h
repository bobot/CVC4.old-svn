/*********************                                                        */
/*! \file arith_simp.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/arith_rewriter.h"
#include <map>
#include "theory/rewriter.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_SIMP_H
#define __CVC4__THEORY__ARITH__ARITH_SIMP_H

namespace CVC4 {
namespace theory {
namespace arith {

class ArithSimp {
private:

  /**
   * Simplification Map:
   * Represent a set of equalities { lhs = rhs }
   *  s.t. lhs can be rewritten as rhs.
   * The keys are the lhs values and the values are the rhs values.
   * Invariants: no rhs contains an lhs.
   */
  typedef std::map<Node, Node> SimplificationMap;
  SimplificationMap d_simps;


  /** Recursively replace the nodes that are in the simplification map. */
  Node replaceWithSimplifications(Node arithNode){
    if(isSimplified(arithNode)){
      return d_simps.find(arithNode)->second;
    }else if(arithNode.getNumChildren() > 0){
      Node::iterator node_it = arithNode.begin();
      Node::iterator node_it_end = arithNode.end();
      NodeBuilder<> nb(arithNode.getKind());
      for(; node_it != node_it_end; ++node_it) {
        nb << replaceWithSimplifications(*node_it);
      }
      return nb;
    }else{
      return arithNode;
    }
  }

public:
  ArithSimp() : d_simps() {}

  /**
   * Returned node is fully rewritten and equivalent to x under the assumptions
   * that all of the equalities that have been added via addSimplification
   * are valid.
   *
   * x is either an arithmetic term, or literal of an arithmetic atom.
   */
  Node simplify(TNode x){
    if(x.getKind() == kind::NOT){
      return NodeBuilder<1>(kind::NOT) << simplify(x[0]);
    }else{
      Node replaced = replaceWithSimplifications(x);
      return Rewriter::rewriteTo(THEORY_ARITH, x);
    }
  }

  /**
   * Adds an equality to the simplification map and updates:
   *  - the simplification map
   *  - and tableau accordingly.
   */
  void addSimplification(TNode lhs, TNode rhs){
    Unreachable();
  }

  /**
   * Given a simplified arithmetic normal form equality
   * attempt to introduce an additional simplification.
   *
   * returns true if a simplification is introduced.
   */
  bool addEquality(TNode eq){
    return false;
  }

  /** returns true if the node is a key in the simplification map
   * and thus may not appear to have the proper value, upper/lower bounds.
   */
  bool isSimplified(TNode lhs){
    return d_simps.find(lhs) != d_simps.end();
  }
};


}; /* namesapce rewrite */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__ARITH_SIMP_H */

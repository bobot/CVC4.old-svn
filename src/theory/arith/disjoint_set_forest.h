#include "expr/node.h"
#include "expr/attribute.h"

#include <ext/hash_map>

#ifndef __CVC4__THEORY__ARITH__DISJOINT_SET_FOREST_H
#define __CVC4__THEORY__ARITH__DISJOINT_SET_FOREST_H

namespace CVC4 {
namespace theory {
namespace arith {

class DisjointSetForest {
private:

  typedef __gnu_cxx::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_nodeMap;

public:
  /** Constructs an empty disjoint set forest. */
  DisjointSetForest(){}

  /** Adds a node to the forest. */
  void add(Node t){
    d_nodeMap[t] = t;
  }

  /** Adds a node to the forest. */
  bool inForest(Node t){
    return (d_nodeMap.end() != d_nodeMap.find(t));
  }

  /** Is this node the representative of the forest? */
  bool isClassRepresentative(TNode t){
    return t == parent(t);
  }

  /**
   * Returns the equivalence class representative.
   * Uses path compresion.
   */
  Node find(TNode t){
    Assert(inForest(t));
    Node p = parent(t);
    if(p == t){
      return t;
    }else{
      Node rep = find(p);
      d_nodeMap[t] = rep;
      return rep;
    }
  }

  /** Returns true when the nodes belong to the same equivalence class. */
  bool sameEquivalenceClass(Node x, Node y){
    Node xRoot = find(x);
    Node yRoot = find(y);

    return xRoot == yRoot;
  }

  /**
   * Merges two equivalence classes.
   * Returns an equality representing the union.
   */
  Node forestUnion(Node x, Node y){
    Assert(! sameEquivalenceClass(x,y));
    Node xRoot = find(x);
    Node yRoot = find(y);

    d_nodeMap[xRoot] = yRoot;
    return NodeBuilder<2>(kind::EQUAL) << xRoot << yRoot;
  }

private:
  Node parent(TNode t){
    Assert(inForest(t));
    return (d_nodeMap.find(t))->second;
  }
};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__DISJOINT_SET_FOREST_H */

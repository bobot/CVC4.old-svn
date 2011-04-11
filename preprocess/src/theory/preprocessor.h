#include "cvc4_private.h"

#ifndef __CVC4__THEORY__PREPROCESSOR_H
#define __CVC4__THEORY__PREPROCESSOR_H

#include <queue>

#include <ext/hash_map>

#include "expr/node.h"
#include "theory/rewriter.h"
#include "util/options.h"
#include "util/stats.h"

namespace CVC4 {

namespace theory {

class TheoryPreprocessor {
private:
  typedef __gnu_cxx::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_replacements;

  std::queue<Node>& d_learned;

  bool preregistered(TNode n) const;

public:
  TheoryPreprocessor(std::queue<Node>& queue) :
    d_learned(queue)
  {}

  bool replaced(TNode n) const;
  /**
   * Rewrite request is honored iff "from" has not been prereigstered.
   * Returns false if from has been prereigstered or if from is already in the rewrite
   * map.
   */
  bool requestReplacement(Node from, Node to);

  /** Adds a node to be handled as if it were a user made assertion. */
  void learn(Node assertion);

  /**
   * This is equivalent to:
   *    Rewriter::rewrite(removeTermITEs(applyReplacmentMap(f))));
   */
  Node preprocess(TNode f);

  Node skolemize(TNode f);

private:
  /**
   * This removes term ites from the node n,
   * replacing the node with a skolem.
   */
  Node removeTermITEs(TNode n);

  /**
   * Applies the all of the requested replacements that returned true
   * up to this point.
   */
  Node applyReplacementMap(TNode n);

};/* class TheoryPreprocessor */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__PREPROCESSOR_H */

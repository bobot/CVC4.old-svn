/*********************                                                        */
/*! \file model_postprocessor.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief 
 **
 ** 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_POSTPROCESSOR_H
#define __CVC4__MODEL_POSTPROCESSOR_H

#include "expr/node.h"

namespace CVC4 {
namespace smt {

class ModelPostprocessor {
public:
  typedef Node return_type;
  std::hash_map<TNode, Node, TNodeHashFunction> d_nodes;

  bool alreadyVisited(TNode current, TNode parent) {
    return d_nodes.find(current) != d_nodes.end();
  }

  void visit(TNode current, TNode parent);

  void start(TNode n) { }

  Node done(TNode n) {
    Assert(alreadyVisited(n, TNode::null()));
    TNode retval = d_nodes[n];
    return retval.isNull() ? n : retval;
  }
};/* class ModelPostprocessor */

}/* CVC4::smt namespace */
}/* CVC4 namespace */

#endif /* __CVC4__MODEL_POSTPROCESSOR_H */

/*********************                                                        */
/*! \file theory_builtin_rewriter.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/builtin/theory_builtin_rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace builtin {

Node TheoryBuiltinRewriter::blastDistinct(TNode in) {

  Assert(in.getKind() == kind::DISTINCT);

  if(in.getNumChildren() == 2) {
    // if this is the case exactly 1 != pair will be generated so the
    // AND is not required
    Node eq = NodeManager::currentNM()->mkNode(in[0].getType().isBoolean() ? kind::IFF : kind::EQUAL, in[0], in[1]);
    Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
    return neq;
  }

  // assume that in.getNumChildren() > 2 => diseqs.size() > 1
  vector<Node> diseqs;
  for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
    TNode::iterator j = i;
    while(++j != in.end()) {
      Node eq = NodeManager::currentNM()->mkNode((*i).getType().isBoolean() ? kind::IFF : kind::EQUAL, *i, *j);
      Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
      diseqs.push_back(neq);
    }
  }
  Node out = NodeManager::currentNM()->mkNode(kind::AND, diseqs);
  return out;
}

Node TheoryBuiltinRewriter::blastChain(TNode in) {

  Assert(in.getKind() == kind::CHAIN);

  Kind chainedOp = in.getOperator().getConst<Kind>();

  if(in.getNumChildren() == 2) {
    // if this is the case exactly 1 pair will be generated so the
    // AND is not required
    return NodeManager::currentNM()->mkNode(chainedOp, in[0], in[1]);
  } else {
    NodeBuilder<> conj(kind::AND);
    for(TNode::iterator i = in.begin(), j = i + 1; j != in.end(); ++i, ++j) {
      conj << NodeManager::currentNM()->mkNode(chainedOp, *i, *j);
    }
    return conj;
  }
}

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

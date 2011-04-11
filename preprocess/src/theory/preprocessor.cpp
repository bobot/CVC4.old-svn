/*********************                                                        */
/*! \file theory_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): cconway, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory engine.
 **
 ** The theory engine.
 **/

#include <vector>

#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/node_builder.h"
#include "util/options.h"

#include "theory/preregistered.h"
#include "theory/rewriter.h"
#include "theory/preprocessor.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {

namespace theory {

struct IteRewriteAttrTag {};
typedef expr::Attribute<IteRewriteAttrTag, Node> IteRewriteAttr;

}/* CVC4::theory namespace */
}/* CVC4 namespace */


bool TheoryPreprocessor::preregistered(TNode n) const {
  return n.getAttribute(PreRegistered());
}

bool TheoryPreprocessor::replaced(TNode n) const {
  return d_replacements.find(n) != d_replacements.end();
}

bool TheoryPreprocessor::requestReplacement(Node from, Node to){
  if(replaced(from) || preregistered(from)){
    return false;
  }else{
    d_replacements.insert(make_pair(from, to));
    return true;
  }
}


void TheoryPreprocessor::learn(Node assertion){
  d_learned.push(assertion);
}


Node TheoryPreprocessor::preprocess(TNode f){
  Node afterReplacements = applyReplacementMap(f);
  Node noTermItes = removeTermITEs(afterReplacements);
  Node rewritten = Rewriter::rewrite(noTermItes);

  Debug("preprocessor") << "preprocess:" << endl
                        << "\torig" << f << endl
                        << "\t" << afterReplacements << endl
                        << "\t" << noTermItes << endl
                        << "\t" << rewritten << endl;
  return rewritten;
}

Node TheoryPreprocessor::skolemize(TNode node){
  Assert(node.getKind() == kind::ITE);
  if(replaced(node)){
    Node replacement = applyReplacementMap(node);
    Assert(replacement.getKind() == kind::SKOLEM);
    return replacement;
  }else{
    TypeNode nodeType = node.getType();
    Node skolem = NodeManager::currentNM()->mkSkolem(nodeType);
    Node eqTrueBranch = NodeBuilder<2>(kind::EQUAL) << skolem << node[1];
    Node eqFalseBranch = NodeBuilder<2>(kind::EQUAL) << skolem << node[2];
    Node boolIte = NodeBuilder<3>(kind::ITE)<< node[0] << eqTrueBranch << eqFalseBranch;
    learn(boolIte);

    AlwaysAssert(requestReplacement(node, skolem));
    node.setAttribute(theory::IteRewriteAttr(), skolem);
    return skolem;
  }
}

Node TheoryPreprocessor::applyReplacementMap(TNode n){
  //TODO add cacheing
  if(replaced(n)){
    NodeMap::const_iterator i = d_replacements.find(n);
    return applyReplacementMap(i->second);
  }else{
    vector<Node> newChildren;
    bool somethingChanged = false;
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      // Make sure to push operator or it will be missing in new
      // (reformed) node.  This was crashing on the very simple input
      // "(f (ite c 0 1))"
      newChildren.push_back(n.getOperator());
    }
    for(TNode::const_iterator it = n.begin(), end = n.end(); it != end; ++it) {
      Node child = *it;
      Node newChild = applyReplacementMap(child);
      somethingChanged |= (newChild != child);
      newChildren.push_back(newChild);
    }
    if(somethingChanged) {
      Node replaced = NodeManager::currentNM()->mkNode(n.getKind(), newChildren);
      return replaced;
    }else{
      return n;
    }
  }
}




/* Our goal is to tease out any ITE's sitting under a theory operator. */
Node TheoryPreprocessor::removeTermITEs(TNode node) {
  Debug("ite") << "removeITEs(" << node << ")" << endl;

  /* The result may be cached already */
  Node cachedRewrite;
  NodeManager *nodeManager = NodeManager::currentNM();
  if(nodeManager->getAttribute(node, theory::IteRewriteAttr(), cachedRewrite)) {
    Debug("ite") << "removeITEs: in-cache: " << cachedRewrite << endl;
    return cachedRewrite.isNull() ? Node(node) : cachedRewrite;
  }

  if(node.getKind() == kind::ITE){
    Assert( node.getNumChildren() == 3 );
    TypeNode nodeType = node.getType();
    if(!nodeType.isBoolean()){
      Node skolem = skolemize(node);
      return skolem;
    }
  }
  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    // Make sure to push operator or it will be missing in new
    // (reformed) node.  This was crashing on the very simple input
    // "(f (ite c 0 1))"
    newChildren.push_back(node.getOperator());
  }
  for(TNode::const_iterator it = node.begin(), end = node.end();
      it != end;
      ++it) {
    Node newChild = removeTermITEs(*it);
    somethingChanged |= (newChild != *it);
    newChildren.push_back(newChild);
  }

  if(somethingChanged) {
    cachedRewrite = nodeManager->mkNode(node.getKind(), newChildren);
    nodeManager->setAttribute(node, theory::IteRewriteAttr(), cachedRewrite);
    return cachedRewrite;
  } else {
    nodeManager->setAttribute(node, theory::IteRewriteAttr(), Node::null());
    return node;
  }
}

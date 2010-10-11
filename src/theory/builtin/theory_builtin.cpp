/*********************                                                        */
/*! \file theory_builtin.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the builtin theory.
 **
 ** Implementation of the builtin theory.
 **/

#include "theory/builtin/theory_builtin.h"
#include "theory/theory_engine.h"
#include "expr/kind.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace builtin {

Node TheoryBuiltin::blastDistinct(TNode in) {
  Debug("theory-rewrite") << "TheoryBuiltin::blastDistinct: "
                          << in << std::endl;
  Assert(in.getKind() == kind::DISTINCT);
  if(in.getNumChildren() == 2) {
    // if this is the case exactly 1 != pair will be generated so the
    // AND is not required
    Node eq = NodeManager::currentNM()->mkNode(in[0].getType().isBoolean() ?
                                               kind::IFF : kind::EQUAL,
                                               in[0], in[1]);
    Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
    return neq;
  }
  // assume that in.getNumChildren() > 2 => diseqs.size() > 1
  vector<Node> diseqs;
  for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
    TNode::iterator j = i;
    while(++j != in.end()) {
      Node eq = NodeManager::currentNM()->mkNode((*i).getType().isBoolean() ?
                                                 kind::IFF : kind::EQUAL,
                                                 *i, *j);
      Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
      diseqs.push_back(neq);
    }
  }
  Node out = NodeManager::currentNM()->mkNode(kind::AND, diseqs);
  return out;
}

RewriteResponse TheoryBuiltin::preRewrite(TNode in, bool topLevel) {
  switch(in.getKind()) {
  case kind::DISTINCT:
    return RewriteComplete(blastDistinct(in));

  case kind::EQUAL:
    // EQUAL is a special case that should never end up here
    Unreachable("TheoryBuiltin can't rewrite EQUAL !");

  default:
    return RewriteComplete(in);
  }
}

Node TheoryBuiltin::getValue(TNode n, TheoryEngine* engine) {
  switch(n.getKind()) {

  case kind::VARIABLE:
    // no variables that the builtin theory is responsible for
    Unreachable();

  case kind::EQUAL: { // 2 args
    // has to be an EQUAL over tuples, since all others should be
    // handled elsewhere
    Assert(n[0].getKind() == kind::TUPLE &&
           n[1].getKind() == kind::TUPLE);
    return NodeManager::currentNM()->
      mkConst( getValue(n[0], engine) == getValue(n[1], engine) );
  }

  case kind::TUPLE: { // 2+ args
    NodeBuilder<> nb(kind::TUPLE);
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      nb << engine->getValue(*i);
    }
    return Node(nb);
  }

  default:
    // all other "builtins" should have been rewritten away or handled
    // by theory engine, or handled elsewhere.
    Unhandled(n.getKind());
  }
}

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory */
}/* CVC4 namespace */

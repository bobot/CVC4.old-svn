/*********************                                                        */
/*! \file theory_uf.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of uninterpreted functions.
 **
 ** Implementation of the theory of uninterpreted functions.
 **/

#include "theory/uf/theory_uf.h"
#include "expr/kind.h"
#include "util/congruence_closure.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

TheoryUF::TheoryUF(int id, Context* c, OutputChannel& out) :
  Theory(id, c, out),
  d_assertions(c),
  d_ccChannel(this),
  d_cc(c, &d_ccChannel),
  d_disequality(c),
  d_registered(c) {
}

TheoryUF::~TheoryUF() {
}

RewriteResponse TheoryUF::postRewrite(TNode n, bool topLevel) {
  if(topLevel) {
    Debug("uf") << "uf: begin rewrite(" << n << ")" << std::endl;
    Node ret(n);
    if(n.getKind() == EQUAL) {
      if(n[0] == n[1]) {
        ret = NodeManager::currentNM()->mkConst(true);
      }
    }
    Debug("uf") << "uf: end rewrite(" << n << ") : " << ret << std::endl;
    return RewriteComplete(ret);
  } else {
    return RewriteComplete(n);
  }
}

void TheoryUF::preRegisterTerm(TNode n) {
  Debug("uf") << "uf: preRegisterTerm(" << n << ")" << std::endl;
}

void TheoryUF::registerTerm(TNode n) {
  Debug("uf") << "uf: registerTerm(" << n << ")" << std::endl;
}

Node TheoryUF::constructConflict(TNode diseq) {
  Debug("uf") << "uf: begin constructConflict()" << std::endl;
  Debug("uf") << "uf:   using diseq == " << diseq << std::endl;

  Node explanation = d_cc.explain(diseq[0], diseq[1]);

  NodeBuilder<> nb(kind::AND);
  if(explanation.getKind() == kind::AND) {
    for(Node::iterator i = explanation.begin();
        i != explanation.end();
        ++i) {
      nb << *i;
    }
  } else {
    Assert(explanation.getKind() == kind::EQUAL);
    nb << explanation;
  }
  nb << diseq.notNode();

  // by construction this should be true
  Assert(nb.getNumChildren() > 1);

  Node conflict = nb;
  Debug("uf") << "conflict constructed : " << conflict << std::endl;

  Debug("uf") << "uf: ending constructConflict()" << std::endl;

  return conflict;
}

void TheoryUF::notifyCongruent(TNode a, TNode b) {
  Debug("uf") << "uf: notified of merge " << a << std::endl
              << "                  and " << b << std::endl;
}

void TheoryUF::check(Effort level) {
  Debug("uf") << "uf: begin check(" << level << ")" << std::endl;

  while(!done()) {
    Node assertion = get();

    Debug("uf") << "uf check(): " << assertion << std::endl;

    switch(assertion.getKind()) {
    case EQUAL:
      d_cc.addEquality(assertion);
      break;
    case NOT:
      d_disequality.push_back(assertion[0]);
      break;
    default:
      Unhandled(assertion.getKind());
    }
  }
  Debug("uf") << "uf check() done = " << (done() ? "true" : "false") << std::endl;

  if(standardEffortOrMore(level)) {
    for(CDList<Node>::const_iterator diseqIter = d_disequality.begin();
        diseqIter != d_disequality.end();
        ++diseqIter) {

      TNode left  = (*diseqIter)[0];
      TNode right = (*diseqIter)[1];
      if(d_cc.areCongruent(left, right)) {
        Debug("uf") << "uf left congruent_to right:\nuf left == " << left << "\nuf right == " << right << "\n";
        Node conflict = constructConflict(*diseqIter);
        Debug("uf") << "uf returning conflict: " << conflict << std::endl;
        d_out->conflict(conflict, false);
        return;
      }
    }
  }

  Debug("uf") << "uf: end check(" << level << ")" << std::endl;
}

void TheoryUF::propagate(Effort level) {
  Debug("uf") << "uf: begin propagate(" << level << ")" << std::endl;
  Debug("uf") << "uf: end propagate(" << level << ")" << std::endl;
}

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

TheoryUF::TheoryUF(int id, Context* ctxt, OutputChannel& out) :
  Theory(id, ctxt, out),
  d_assertions(ctxt),
  d_ccChannel(this),
  d_cc(ctxt, &d_ccChannel),
  d_unionFind(ctxt),
  d_disequalities(ctxt),
  d_disequality(ctxt),
  d_conflict(),
  d_trueNode(),
  d_falseNode() {
  TypeNode boolType = NodeManager::currentNM()->booleanType();
  d_trueNode = NodeManager::currentNM()->mkVar("TRUE_UF", boolType);
  d_falseNode = NodeManager::currentNM()->mkVar("FALSE_UF", boolType);
  d_cc.addTerm(d_trueNode);
  d_cc.addTerm(d_falseNode);
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

TNode TheoryUF::find(TNode a) {
  UnionFind::iterator i = d_unionFind.find(a);
  if(i == d_unionFind.end()) {
    return a;
  } else {
    return d_unionFind[a] = find((*i).second);
  }
}

// no path compression
TNode TheoryUF::debugFind(TNode a) const {
  UnionFind::iterator i = d_unionFind.find(a);
  if(i == d_unionFind.end()) {
    return a;
  } else {
    return debugFind((*i).second);
  }
}

void TheoryUF::unionClasses(TNode a, TNode b) {
  if(a == b) {
    return;
  }
  Assert(d_unionFind.find(a) == d_unionFind.end());
  Assert(d_unionFind.find(b) == d_unionFind.end());
  d_unionFind[a] = b;
}

void TheoryUF::notifyCongruent(TNode a, TNode b) {
  Debug("uf") << "uf: notified of merge " << a << std::endl
              << "                  and " << b << std::endl;
  if(!d_conflict.isNull()) {
    // if already a conflict, we don't care
    return;
  }

  // make "a" the one with shorter diseqList
  DiseqLists::iterator deq_ia = d_disequalities.find(a);
  DiseqLists::iterator deq_ib = d_disequalities.find(b);
  if(deq_ia != d_disequalities.end()) {
    if(deq_ib == d_disequalities.end() ||
       (*deq_ia).second->size() > (*deq_ib).second->size()) {
      TNode tmp = a;
      a = b;
      b = tmp;
      Debug("uf") << "    swapping to make a shorter diseqList" << std::endl;
    }
  }
  a = find(a);
  b = find(b);
  Debug("uf") << "uf: uf reps are " << a << std::endl
              << "            and " << b << std::endl;
  unionClasses(a, b);

  DiseqLists::iterator deq_i = d_disequalities.find(a);
  if(deq_i != d_disequalities.end()) {
    // a set of other trees we are already disequal to
    // (for the optimization below)
    std::set<TNode> alreadyDiseqs;
    DiseqLists::iterator deq_ib = d_disequalities.find(b);
    if(deq_ib != d_disequalities.end()) {
      DiseqList* deq = (*deq_i).second;
      for(DiseqList::const_iterator j = deq->begin(); j != deq->end(); ++j) {
        TNode deqn = *j;
        TNode s = deqn[0];
        TNode t = deqn[1];
        TNode sp = find(s);
        TNode tp = find(t);
        Assert(sp == b || tp == b);
        if(sp == b) {
          alreadyDiseqs.insert(tp);
        } else {
          alreadyDiseqs.insert(sp);
        }
      }
    }

    DiseqList* deq = (*deq_i).second;
    Debug("uf") << "a == " << a << std::endl;
    Debug("uf") << "size of deq(a) is " << deq->size() << std::endl;
    for(DiseqList::const_iterator j = deq->begin(); j != deq->end(); ++j) {
      Debug("uf") << "  deq(a) ==> " << *j << std::endl;
      TNode deqn = *j;
      Assert(deqn.getKind() == kind::EQUAL);
      TNode s = deqn[0];
      TNode t = deqn[1];
      Debug("uf") << "       s  ==> " << s << std::endl
                  << "       t  ==> " << t << std::endl
                  << "  find(s) ==> " << debugFind(s) << std::endl
                  << "  find(t) ==> " << debugFind(t) << std::endl;
      TNode sp = find(s);
      TNode tp = find(t);
      if(sp == tp) {
        d_conflict = deqn;
        return;
      }
      Assert(sp == b || tp == b);
      // optimization: don't put redundant diseq's in the list
      if(sp == b) {
        if(alreadyDiseqs.find(tp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs.insert(tp);
        }
      } else {
        if(alreadyDiseqs.find(sp) == alreadyDiseqs.end()) {
          appendToDiseqList(b, deqn);
          alreadyDiseqs.insert(sp);
        }
      }
    }
    Debug("uf") << "end" << std::endl;
  }
}

void TheoryUF::appendToDiseqList(TNode of, TNode eq) {
  Debug("uf") << "appending " << eq << std::endl
              << "  to diseq list of " << of << std::endl;
  Assert(eq.getKind() == kind::EQUAL);
  Assert(of == debugFind(of));
  DiseqLists::iterator deq_i = d_disequalities.find(of);
  DiseqList* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) DiseqList(true, getContext());
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }
  deq->push_back(eq);
  Debug("uf") << "  size is now " << deq->size() << std::endl;
}

void TheoryUF::addDisequality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL);

  Node a = eq[0];
  Node b = eq[1];

  appendToDiseqList(find(a), eq);
  appendToDiseqList(find(b), eq);
}

void TheoryUF::check(Effort level) {
  Debug("uf") << "uf: begin check(" << level << ")" << std::endl;

  while(!done()) {
    Node assertion = get();

    Debug("uf") << "uf check(): " << assertion << std::endl;

    switch(assertion.getKind()) {
    case EQUAL:
      d_cc.addEquality(assertion);
      if(!d_conflict.isNull()) {
        Node conflict = constructConflict(d_conflict);
        d_conflict = Node::null();
        d_out->conflict(conflict, false);
        return;
      }
      break;
    case APPLY_UF:
      { // predicate
        Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, assertion, d_trueNode);
        d_cc.addTerm(assertion);
        d_cc.addEquality(eq);
        Debug("uf") << "true == false ? " << (find(d_trueNode) == find(d_falseNode)) << std::endl;
        Assert(find(d_trueNode) != find(d_falseNode));
      }
      break;
    case NOT:
      if(assertion[0].getKind() == kind::EQUAL) {
        Node a = assertion[0][0];
        Node b = assertion[0][1];

        addDisequality(assertion[0]);
        d_disequality.push_back(assertion[0]);

        d_cc.addTerm(a);
        d_cc.addTerm(b);

        Debug("uf") << "       a  ==> " << a << std::endl
                    << "       b  ==> " << b << std::endl
                    << "  find(a) ==> " << debugFind(a) << std::endl
                    << "  find(b) ==> " << debugFind(b) << std::endl;

        // There are two ways to get a conflict here.
        if(!d_conflict.isNull()) {
          // We get a conflict this way if we weren't watching a, b
          // before and we were just now notified (via
          // notifyCongruent()) when we called addTerm() above that
          // they are congruent.  We make this a separate case (even
          // though the check in the "else if.." below would also
          // catch it, so that we can clear out d_conflict.
          Node conflict = constructConflict(d_conflict);
          d_conflict = Node::null();
          d_out->conflict(conflict, false);
          return;
        } else if(find(a) == find(b)) {
          // We get a conflict this way if we WERE previously watching
          // a, b and were notified previously (via notifyCongruent())
          // that they were congruent.
          Node conflict = constructConflict(assertion[0]);
          d_out->conflict(conflict, false);
          return;
        }

        // If we get this far, there should be nothing conflicting due
        // to this disequality.
        Assert(!d_cc.areCongruent(a, b));
      } else {
        Assert(assertion[0].getKind() == kind::APPLY_UF);
        Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, assertion[0], d_falseNode);
        d_cc.addTerm(assertion[0]);
        d_cc.addEquality(eq);
        Debug("uf") << "true == false ? " << (find(d_trueNode) == find(d_falseNode)) << std::endl;
        Assert(find(d_trueNode) != find(d_falseNode));
      }
      break;
    default:
      Unhandled(assertion.getKind());
    }
  }
  Debug("uf") << "uf check() done = " << (done() ? "true" : "false") << std::endl;

  for(CDList<Node>::const_iterator diseqIter = d_disequality.begin();
      diseqIter != d_disequality.end();
      ++diseqIter) {

    TNode left  = (*diseqIter)[0];
    TNode right = (*diseqIter)[1];
    Debug("uf") << "testing left: " << left << std::endl
                << "       right: " << right << std::endl
                << "     find(L): " << debugFind(left) << std::endl
                << "     find(R): " << debugFind(right) << std::endl
                << "     areCong: " << d_cc.areCongruent(left, right) << std::endl;
    Assert((debugFind(left) == debugFind(right)) == d_cc.areCongruent(left, right));
  }

  Debug("uf") << "uf: end check(" << level << ")" << std::endl;
}

void TheoryUF::propagate(Effort level) {
  Debug("uf") << "uf: begin propagate(" << level << ")" << std::endl;
  Debug("uf") << "uf: end propagate(" << level << ")" << std::endl;
}

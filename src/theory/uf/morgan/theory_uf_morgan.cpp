/*********************                                                        */
/*! \file theory_uf_morgan.cpp
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
 ** \brief Implementation of the theory of uninterpreted functions.
 **
 ** Implementation of the theory of uninterpreted functions.
 **/

#include "theory/uf/morgan/theory_uf_morgan.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include "util/congruence_closure.h"

#include <map>

using namespace std;

using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::uf::morgan;

TheoryUFMorgan::TheoryUFMorgan(Context* ctxt, OutputChannel& out, Valuation valuation) :
  TheoryUF(ctxt, out, valuation),
  d_assertions(ctxt),
  d_ccChannel(this),
  d_cc(ctxt, &d_ccChannel, kind::APPLY_UF),
  d_trueNode(),
  d_falseNode(),
  d_trueEqFalseNode(),
  d_toPropagate(),
  d_ccExplanationLength("theory::uf::morgan::cc::averageExplanationLength",
                        d_cc.getExplanationLength()) {

  StatisticsRegistry::registerStat(&d_ccExplanationLength);

  NodeManager* nm = NodeManager::currentNM();
  TypeNode boolType = nm->booleanType();
  d_trueNode = nm->mkVar("TRUE_UF", boolType);
  d_falseNode = nm->mkVar("FALSE_UF", boolType);
  d_trueEqFalseNode = nm->mkNode(kind::IFF, d_trueNode, d_falseNode);
  d_cc.registerTerm(d_trueEqFalseNode);
  d_cc.assertDisequality(d_trueEqFalseNode);
  //d_cc.registerTerm(d_trueNode);
  //d_cc.registerTerm(d_falseNode);
}

TheoryUFMorgan::~TheoryUFMorgan() {
  d_trueNode = Node::null();
  d_falseNode = Node::null();
  d_trueEqFalseNode = Node::null();

  StatisticsRegistry::unregisterStat(&d_ccExplanationLength);
}

void TheoryUFMorgan::preRegisterTerm(TNode n) {
  Debug("uf") << "uf: preRegisterTerm(" << n << ")" << endl;
  if(n.getKind() == kind::EQUAL || n.getKind() == kind::IFF) {
    d_cc.registerTerm(n);
  } else if(n.getKind() == kind::APPLY_UF && n.getOperator().getType().isPredicate()) {
    d_cc.registerTerm(NodeManager::currentNM()->mkNode(kind::IFF, n, d_trueNode));
  }
}

Node TheoryUFMorgan::constructConflict(TNode diseq) {
  Debug("uf") << "uf: begin constructConflict()" << endl;
  Debug("uf") << "uf:   using diseq == " << diseq << endl;

  Node explanation = d_cc.explain(diseq[0], diseq[1]);

  Debug("uf") << "uf:   got expl " << explanation << endl;

  NodeBuilder<> nb(kind::AND);
  if(explanation.getKind() == kind::AND) {
    for(TNode::iterator i = TNode(explanation).begin();
        i != TNode(explanation).end();
        ++i) {
      TNode n = *i;
      Assert(n.getKind() == kind::EQUAL ||
             n.getKind() == kind::IFF);
      Assert(n[0] != d_trueNode &&
             n[0] != d_falseNode);
      if(n[1] == d_trueNode) {
        nb << n[0];
      } else if(n[1] == d_falseNode) {
        nb << n[0].notNode();
      } else {
        nb << n;
      }
    }
  } else {
    Assert(explanation.getKind() == kind::EQUAL ||
           explanation.getKind() == kind::IFF);
    Assert(explanation[0] != d_trueNode &&
           explanation[0] != d_falseNode);
    if(explanation[1] == d_trueNode) {
      nb << explanation[0];
    } else if(explanation[1] == d_falseNode) {
      nb << explanation[0].notNode();
    } else {
      nb << explanation;
    }
  }

  if(diseq != d_trueEqFalseNode) {
    nb << diseq.notNode();
  }

  // by construction this should be true
  Assert(nb.getNumChildren() > 1);

  Node conflict = nb;
  Debug("uf") << "conflict constructed : " << conflict << endl;

  Debug("uf") << "uf: ending constructConflict()" << endl;

  return conflict;
}

void TheoryUFMorgan::notifyCongruence(TNode n) {
  Debug("uf") << "uf: notified of congruence " << n << endl;
  d_toPropagate.push_back(n);
}

/*
void TheoryUFMorgan::appendToDiseqList(TNode of, TNode eq) {
  Debug("uf") << "appending " << eq << endl
              << "  to diseq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(of == debugFind(of));
  EqLists::iterator deq_i = d_disequalities.find(of);
  EqList* deq;
  if(deq_i == d_disequalities.end()) {
    deq = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_disequalities.insertDataFromContextMemory(of, deq);
  } else {
    deq = (*deq_i).second;
  }
  deq->push_back(eq);
  if(Debug.isOn("uf")) {
    Debug("uf") << "  size is now " << deq->size() << endl;
  }
}

void TheoryUFMorgan::appendToEqList(TNode of, TNode eq) {
  Debug("uf") << "appending " << eq << endl
              << "  to eq list of " << of << endl;
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(of == debugFind(of));
  EqLists::iterator eq_i = d_equalities.find(of);
  EqList* eql;
  if(eq_i == d_equalities.end()) {
    eql = new(getContext()->getCMM()) EqList(true, getContext(), false,
                                             ContextMemoryAllocator<TNode>(getContext()->getCMM()));
    d_equalities.insertDataFromContextMemory(of, eql);
  } else {
    eql = (*eq_i).second;
  }
  eql->push_back(eq);
  if(Debug.isOn("uf")) {
    Debug("uf") << "  size is now " << eql->size() << endl;
  }
}

void TheoryUFMorgan::addDisequality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);

  TNode a = eq[0];
  TNode b = eq[1];

  appendToDiseqList(find(a), eq);
  appendToDiseqList(find(b), eq);
}
*/

void TheoryUFMorgan::check(Effort level) {
  TimerStat::CodeTimer codeTimer(d_checkTimer);

  Debug("uf") << "uf: begin check(" << level << ")" << endl;

  while(!done()) {
    //Assert(d_conflict.isNull());

    Node assertion = get();

    //d_activeAssertions.push_back(assertion);

    Debug("uf") << "uf check(): " << assertion << endl;

    switch(assertion.getKind()) {
    case kind::EQUAL:
    case kind::IFF:
      d_cc.assertEquality(assertion);
      break;
    case kind::APPLY_UF:
      { // predicate

        // assert it's a predicate
        Assert(assertion.getOperator().getType().getRangeType().isBoolean());

        Node eq = NodeManager::currentNM()->mkNode(kind::IFF,
                                                   assertion, d_trueNode);
        d_cc.assertEquality(eq);
      }
      break;
    case kind::NOT:
      if(assertion[0].getKind() == kind::EQUAL ||
         assertion[0].getKind() == kind::IFF) {
        if(d_cc.areCongruent(assertion[0][0], assertion[0][1])) {
          d_out->conflict(constructConflict(assertion[0]));
        } else {
          d_cc.assertDisequality(assertion[0]);
        }
      } else {
        // negation of a predicate
        Assert(assertion[0].getKind() == kind::APPLY_UF);

        // assert it's a predicate
        Assert(assertion[0].getOperator().getType().getRangeType().isBoolean());

        Node eq = NodeManager::currentNM()->mkNode(kind::IFF,
                                                   assertion[0], d_falseNode);
        d_cc.assertEquality(eq);
      }
      break;
    default:
      Unhandled(assertion.getKind());
    }
  }

  if(level == FULL_EFFORT) {
    // need to do this to ensure we find all conflicts
    propagate(level);
  }

  Debug("uf") << "uf check() done = " << (done() ? "true" : "false") << endl;
  Debug("uf") << "uf: end check(" << level << ")" << endl;
}

void TheoryUFMorgan::propagate(Effort level) {
  TimerStat::CodeTimer codeTimer(d_propagateTimer);

  Debug("uf") << "uf: begin propagate(" << level << ")" << endl;
  vector<Node> list;
  list.swap(d_toPropagate);
  for(vector<Node>::iterator i = list.begin(); i != list.end(); ++i) {
    Node value = d_valuation.getSatValue(*i);
    if(value.isNull()) {
      Debug("uf") << "uf: propagating deferred literal " << *i << endl;
      d_out->propagate(*i);
    } else if(value.getConst<bool>()) {
      Debug("uf") << "uf: deferred literal is TRUE: " << *i << endl;
    } else {
      Debug("uf") << "uf: deferred literal is FALSE: " << *i << endl;
      d_out->conflict(constructConflict(*i));
      return;// for now, just do one explanation
    }
  }
  Debug("uf") << "uf: end propagate(" << level << ")" << endl;
}

void TheoryUFMorgan::explain(TNode n) {
  TimerStat::CodeTimer codeTimer(d_explainTimer);

  Debug("uf") << "uf: begin explain([" << n << "])" << endl;
  d_out->explanation(d_cc.explain(n));
  Debug("uf") << "uf: end explain([" << n << "])" << endl;
}

void TheoryUFMorgan::presolve() {
  TimerStat::CodeTimer codeTimer(d_presolveTimer);

  Debug("uf") << "uf: begin presolve()" << endl;
  Debug("uf") << "uf: end presolve()" << endl;
}

void TheoryUFMorgan::notifyRestart() {
  Debug("uf") << "uf: begin notifyDecisionLevelZero()" << endl;
  Debug("uf") << "uf: end notifyDecisionLevelZero()" << endl;
}

Node TheoryUFMorgan::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
  case kind::APPLY_UF:
    if(n.getType().isBoolean()) {
      if(d_cc.areCongruent(d_trueNode, n)) {
        return nodeManager->mkConst(true);
      } else if(d_cc.areCongruent(d_falseNode, n)) {
        return nodeManager->mkConst(false);
      }
    }
    return d_cc.normalize(n);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryUFMorgan::staticLearning(TNode n, NodeBuilder<>& learned) {
  TimerStat::CodeTimer codeTimer(d_staticLearningTimer);

  vector<TNode> workList;
  workList.push_back(n);
  __gnu_cxx::hash_set<TNode, TNodeHashFunction> processed;

  while(!workList.empty()) {
    n = workList.back();

    bool unprocessedChildren = false;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      if(processed.find(*i) == processed.end()) {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }

    if(unprocessedChildren) {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if(processed.find(n) != processed.end()) {
      continue;
    }
    processed.insert(n);

    // == DIAMONDS ==

    Debug("diamonds") << "===================== looking at" << endl
                      << n << endl;

    // binary OR of binary ANDs of EQUALities
    if(n.getKind() == kind::OR && n.getNumChildren() == 2 &&
       n[0].getKind() == kind::AND && n[0].getNumChildren() == 2 &&
       n[1].getKind() == kind::AND && n[1].getNumChildren() == 2 &&
       (n[0][0].getKind() == kind::EQUAL || n[0][0].getKind() == kind::IFF) &&
       (n[0][1].getKind() == kind::EQUAL || n[0][1].getKind() == kind::IFF) &&
       (n[1][0].getKind() == kind::EQUAL || n[1][0].getKind() == kind::IFF) &&
       (n[1][1].getKind() == kind::EQUAL || n[1][1].getKind() == kind::IFF)) {
      // now we have (a = b && c = d) || (e = f && g = h)

      Debug("diamonds") << "has form of a diamond!" << endl;

      TNode
        a = n[0][0][0], b = n[0][0][1],
        c = n[0][1][0], d = n[0][1][1],
        e = n[1][0][0], f = n[1][0][1],
        g = n[1][1][0], h = n[1][1][1];

      // test that one of {a, b} = one of {c, d}, and make "b" the
      // shared node (i.e. put in the form (a = b && b = d))
      // note we don't actually care about the shared ones, so the
      // "swaps" below are one-sided, ignoring b and c
      if(a == c) {
        a = b;
      } else if(a == d) {
        a = b;
        d = c;
      } else if(b == c) {
        // nothing to do
      } else if(b == d) {
        d = c;
      } else {
        // condition not satisfied
        Debug("diamonds") << "+ A fails" << endl;
        continue;
      }

      Debug("diamonds") << "+ A holds" << endl;

      // same: one of {e, f} = one of {g, h}, and make "f" the
      // shared node (i.e. put in the form (e = f && f = h))
      if(e == g) {
        e = f;
      } else if(e == h) {
        e = f;
        h = g;
      } else if(f == g) {
        // nothing to do
      } else if(f == h) {
        h = g;
      } else {
        // condition not satisfied
        Debug("diamonds") << "+ B fails" << endl;
        continue;
      }

      Debug("diamonds") << "+ B holds" << endl;

      // now we have (a = b && b = d) || (e = f && f = h)
      // test that {a, d} == {e, h}
      if( (a == e && d == h) ||
          (a == h && d == e) ) {
        // learn: n implies a == d
        Debug("diamonds") << "+ C holds" << endl;
        Node newEquality = a.getType().isBoolean() ? a.iffNode(d) : a.eqNode(d);
        Debug("diamonds") << "  ==> " << newEquality << endl;
        learned << n.impNode(newEquality);
      } else {
        Debug("diamonds") << "+ C fails" << endl;
      }
    }
  }
}

/*
void TheoryUFMorgan::dump() {
  if(!Debug.isOn("uf")) {
    return;
  }
  Debug("uf") << "============== THEORY_UF ==============" << endl;
  Debug("uf") << "Active assertions list:" << endl;
  for(context::CDList<Node>::const_iterator i = d_activeAssertions.begin();
      i != d_activeAssertions.end();
      ++i) {
    Debug("uf") << "    " << *i << endl;
  }
  Debug("uf") << "Congruence union-find:" << endl;
  for(UnionFind::const_iterator i = d_unionFind.begin();
      i != d_unionFind.end();
      ++i) {
    Debug("uf") << "    " << (*i).first << "  ==>  " << (*i).second
                << endl;
  }
  Debug("uf") << "Disequality lists:" << endl;
  for(EqLists::const_iterator i = d_disequalities.begin();
      i != d_disequalities.end();
      ++i) {
    Debug("uf") << "    " << (*i).first << ":" << endl;
    EqList* dl = (*i).second;
    for(EqList::const_iterator j = dl->begin();
        j != dl->end();
        ++j) {
      Debug("uf") << "        " << *j << endl;
    }
  }
  Debug("uf") << "=======================================" << endl;
}
*/

/*********************                                                        */
/*! \file congruence_closure.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The congruence closure module implementation
 **
 ** The congruence closure module implementation.
 **/

#include "util/congruence_closure.h"

#include <stack>

#include "theory/uf/morgan/theory_uf_morgan.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/datatypes/theory_datatypes.h"

namespace CVC4 {
  // explicit instantiation of the needed instnatiations of CC template here, for rapid prototyping
  template class CongruenceClosure<CVC4::theory::uf::morgan::TheoryUFMorgan::CongruenceChannel>;
  template class CongruenceClosure<CVC4::theory::arrays::TheoryArrays::CongruenceChannel>;
  template class CongruenceClosure<CVC4::theory::datatypes::TheoryDatatypes::CongruenceChannel>;
}/* CVC4 namespace */

using namespace std;

namespace CVC4 {

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::merge(TNode eq, TNode inputEq) {
  Assert(!eq[0].getType().isFunction() && !eq[1].getType().isFunction(),
         "CongruenceClosure:: equality between function symbols not allowed");

  d_proofRewrite[eq] = inputEq;

  if(Trace.isOn("cc")) {
    Trace("cc") << "CC addEq[" << d_context->getLevel() << "]: " << eq << std::endl;
  }
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(!isCongruenceOperator(eq[1]));
  if(areCongruent(eq[0], eq[1])) {
    Trace("cc") << "CC -- redundant, ignoring...\n";
    return;
  }

  TNode s = eq[0], t = eq[1];

  Assert(s != t);

  Trace("cc:detail") << "CC        " << s << " == " << t << std::endl;

  // change from paper: do this whether or not s, t are applications
  Trace("cc:detail") << "CC        propagating the eq" << std::endl;

  if(!isCongruenceOperator(s)) {
    // s, t are constants
    propagate(eq);
  } else {
    // s is an apply, t is a constant
    Node ap = buildRepresentativesOfApply(s);

    Trace("cc:detail") << "CC rewrLHS " << "op_and_args_a == " << t << std::endl;
    Trace("cc") << "CC ap is   " << ap << std::endl;

    TNode l = lookup(ap);
    Trace("cc:detail") << "CC lookup(ap): " << l << std::endl;
    if(!l.isNull()) {
      // ensure a hard Node link exists to this during the call
      Node pending = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, l);
      Trace("cc:detail") << "pending1 " << pending << std::endl;
      propagate(pending);
    } else {
      Trace("cc") << "CC lookup(ap) setting to " << eq << std::endl;
      setLookup(ap, eq);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        useList(cid(*i)).push_back(eq);
      }
    }
  }
}/* merge() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::buildRepresentativesOfApply(TNode apply,
                                                              Kind kindToBuild)
  throw(AssertionException) {
  Assert(isCongruenceOperator(apply));
  NodeBuilder<> argspb(kindToBuild);
  Assert(node(find(cid(apply.getOperator()))) == apply.getOperator(),
         "CongruenceClosure:: bad state: "
         "function symbol (or other congruence operator) merged with another");
  if(apply.getMetaKind() == kind::metakind::PARAMETERIZED) {
    argspb << apply.getOperator();
  }
  for(TNode::iterator i = apply.begin(); i != apply.end(); ++i) {
    argspb << node(find(cid(*i)));
  }
  return argspb;
}/* buildRepresentativesOfApply() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::propagate(TNode seed) {
  Trace("cc:detail") << "=== doing a round of propagation ===" << std::endl
                     << "the \"seed\" propagation is: " << seed << std::endl;

  std::list<Node> pending;

  Trace("cc") << "seed propagation with: " << seed << std::endl;
  pending.push_back(seed);
  do { // while(!pending.empty())
    bool cancel = false;

    Node e = pending.front();
    pending.pop_front();

    Trace("cc") << "=== top of propagate loop ===" << std::endl
                << "=== e is " << e << " ===" << std::endl;

    TNode a, b;
    if(e.getKind() == kind::EQUAL ||
       e.getKind() == kind::IFF) {
      // e is an equality a = b (a, b are constants)

      a = e[0];
      b = e[1];

      Trace("cc:detail") << "propagate equality: " << a << " == " << b << std::endl;
    } else {
      // e is a tuple ( apply f A... = a , apply f B... = b )

      Trace("cc") << "propagate tuple: " << e << "\n";

      Assert(e.getKind() == kind::TUPLE);

      Assert(e.getNumChildren() == 2);
      Assert(e[0].getKind() == kind::EQUAL ||
             e[0].getKind() == kind::IFF);
      Assert(e[1].getKind() == kind::EQUAL ||
             e[1].getKind() == kind::IFF);

      // tuple is (eq, lookup)
      a = e[0][1];
      b = e[1][1];

      Assert(!isCongruenceOperator(a));
      Assert(!isCongruenceOperator(b));

      Trace("cc") << "                 ( " << a << " , " << b << " )" << std::endl;
    }

    if(Debug.isOn("cc")) {
      Trace("cc:detail") << *this
                         << "=====at start=====" << std::endl
                         << "a          :" << a << std::endl
                         << "NORMALIZE a:" << normalize(a) << std::endl
                         << "b          :" << b << std::endl
                         << "NORMALIZE b:" << normalize(b) << std::endl
                         << "alreadyCongruent?:" << areCongruent(a,b) << std::endl
                         << "==================" << std::endl;
    }

    // change from paper: need to normalize() here since in our
    // implementation, a and b can be applications
    Node ap = node(find(cid(a))), bp = node(find(cid(b)));
    if(ap != bp) {

      Trace("cc:detail") << "EC[a] == " << ap << std::endl
                         << "EC[b] == " << bp << std::endl;

      // prop list

      Trace("cc:detail") << "going through propagation list of " << /*node(*/ap/*)*/ << std::endl;
      ClassList& cl = classList(cid(ap));

      if(cl.empty()) {
        // An empty class list means it's the single-entry class list
        // containing the thing itself.  So we patch it up, here.
        //
        // This can happen since we lazily create the single-entry
        // class listss, but they're context-dependent: once we pop
        // above that level, the list is cleared out.
        cl.push_back(cid(ap));
        Trace("cc:detail") << "ap was nullified, fixed" << std::endl;
      }

      for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
        Trace("cc:detail") << "==> at node " << node(*cli) << " in class list of " << /*node(*/ap/*)*/ << std::endl;
        Assert(node(find(*cli)) == ap);
        std::vector<Node>& plist = propagateList(*cli);
        for(std::vector<Node>::iterator i = plist.begin(); i != plist.end(); ++i) {
          Assert((*i).getKind() == kind::EQUAL || (*i).getKind() == kind::IFF);
          Trace("cc:detail") << "    ==> considering " << *i << std::endl;
          Node l = (*i)[0];
          Node r = (*i)[1];
          if(isCongruenceOperator(l)) {
            Trace("cc:detail") << "    ==> " << l << " ==> ";
            l = replace(flatten(l));
            Trace("cc:detail") << l << std::endl;
          }
          if(isCongruenceOperator(r)) {
            Trace("cc:detail") << "    ==> " << r << " ==> ";
            r = replace(flatten(r));
            Trace("cc:detail") << r << std::endl;
          }
          Cid c = find(cid(l));
          if(c == cid(bp)) {
            if(node(find(cid(r))) == ap) {
              Trace("cc:detail") << "        HIT!! ECs are " << /*node(*/bp/*)*/ << " and " << /*node(*/ap/*)*/ << std::endl;
              if(d_out->notifyEntailedEquality(*i)) {
                Trace("cc:detail") << "        in conflict, will CANCEL further propagation" << std::endl;
                cancel = true;
                d_pending.clear();
                goto fixup;
              }
            }
          } else if(c == cid(ap) && node(find(cid(r))) == bp) {
            Trace("cc:detail") << "        HIT!! ECs are " << /*node(*/ap/*)*/ << " and " << /*node(*/bp/*)*/ << std::endl;
            if(d_out->notifyEntailedEquality(*i)) {
              Trace("cc:detail") << "        in conflict, CANCELING further propagation" << std::endl;
              cancel = true;
              d_pending.clear();
              goto fixup;
            }
          }
        }
      }

    fixup:
      // even if we've been "canceled," we still have to fix up our
      // data structures for this merge so that explain() will work.

      // rep mapping

      Trace("cc:detail") << "going through representatives of " << /*node(*/ap/*)*/ << std::endl;

      for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
        Assert(node(find(*cli)) == ap);
        Trace("cc:detail") << "setting representative of " << node(*cli) << " to " << bp << std::endl;
        d_representative.set(*cli, cid(bp));
      }

      // use lists

      if(Debug.isOn("cc:detail")) {
        Debug("cc:detail") << "ap is " << ap << std::endl;
        Debug("cc:detail") << "find(ap) is " << node(find(cid(ap))) << std::endl;
        Debug("cc:detail") << "CC in prop go through useList of " << ap << std::endl;
      }
      UseList& ul = useList(cid(ap));
      //for( f(c1,c2)=c in UseList(ap) )
      for(UseList::const_iterator i = ul.begin(); i != ul.end(); ++i) {
        TNode eq = *i;
        Trace("cc") << "CC  -- useList: " << eq << std::endl;
        Assert(eq.getKind() == kind::EQUAL ||
               eq.getKind() == kind::IFF);
        // change from paper
        // use list elts can have form (apply c..) = x  OR  x = (apply c..)
        Assert(isCongruenceOperator(eq[0]) ||
               isCongruenceOperator(eq[1]));
        // do for each side that is an application
        for(int side = 0; side <= 1; ++side) {
          if(!isCongruenceOperator(eq[side])) {
            continue;
          }

          Node cp = buildRepresentativesOfApply(eq[side]);

          // if lookup(c1',c2') is some f(d1,d2)=d then
          TNode n = lookup(cp);

          Trace("cc:detail") << "CC     -- c' is " << cp << std::endl;

          if(!n.isNull()) {
            Trace("cc:detail") << "CC     -- lookup(c') is " << n << std::endl;
            // add (f(c1,c2)=c,f(d1,d2)=d) to pending
            Node tuple = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, n);
            Trace("cc") << "CC add tuple to pending: " << tuple << std::endl;
            pending.push_back(tuple);
            // remove f(c1,c2)=c from UseList(ap)
            Trace("cc:detail") << "supposed to remove " << eq << std::endl
                               << "  from UseList of " << ap << std::endl;
            //i = ul.erase(i);// difference from paper: don't need to erase
          } else {
            Trace("cc") << "CC     -- lookup(c') is null" << std::endl;
            Trace("cc") << "CC     -- setlookup(c') to " << eq << std::endl;
            // set lookup(c1',c2') to f(c1,c2)=c
            setLookup(cp, eq);
            // move f(c1,c2)=c from UseList(ap) to UseList(b')
            //i = ul.erase(i);// difference from paper: don't need to erase
            useList(cid(bp)).push_back(eq);
          }
        }
      }
      Trace("cc:detail") << "CC in prop done with useList of " << ap << std::endl;

      if(!cancel) {
        // finally, notify client if ap was cared about, and care about bp
        if(d_careSet.find(ap) != d_careSet.end()) {
          d_out->notifyMerge(/*node(*/ap/*)*/, /*node(*/bp/*)*/);
          d_careSet.insert(bp);
        }
      }

      Assert(&classList(cid(ap)) != &classList(cid(bp)));
      if(Trace.isOn("cc:detail")) {
        {
          Trace("cc:detail") << "class list of " << ap << " is:" << std::endl;
          ClassList& cl = classList(cid(ap));
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }

        {
          Trace("cc:detail") << "class list of " << bp << " is:" << std::endl;
          ClassList& cl = classList(cid(bp));
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }
      }

      Debug("cc:detail") << "concat class lists of " << ap << " and " << bp << std::endl;
      // hack to get around the fact that lists empty themselves on
      // backtrack (but should always contain themselves)
      ClassList& clap = classList(cid(ap));
      ClassList& clbp = classList(cid(bp));
      if(clbp.empty()) {
        clbp.push_back(cid(bp));
        Trace("cc:detail") << "bp was nullified, fixed" << std::endl;
      }
      Assert(!clap.empty()); // should have been fixed above
      clbp.concat(clap);
      mergeProof(cid(a), cid(b), e);

      if(Trace.isOn("cc:detail")) {
        Trace("cc:detail") << "post-concat:::" << std::endl;
        {
          Trace("cc:detail") << "class list of " << bp << " is:" << std::endl;
          ClassList& cl = classList(cid(bp));
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }
      }

    } else {
      Trace("cc:detail") << "CCs the same ( == " << ap << "), do nothing." << std::endl;
    }

    if(Debug.isOn("cc")) {
      Debug("cc") << "=====at end=====" << std::endl
                  << "a          :" << a << std::endl
                  << "NORMALIZE a:" << normalize(a) << std::endl
                  << "b          :" << b << std::endl
                  << "NORMALIZE b:" << normalize(b) << std::endl
                  << "alreadyCongruent?:" << areCongruent(a,b) << std::endl
                  << "================" << std::endl
                  << *this;
    }
    Assert(areCongruent(a, b));
  } while(!pending.empty());
}/* propagate() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::mergeProof(Cid a, Cid b, TNode e) {
  Trace("cc:proof") << "  -- merge-proofing " << node(a) << "\n"
                    << "                and " << node(b) << "\n"
                    << "               with " << e << "\n";

  // proof forest gets a -> b labeled with e

  // first reverse all the edges in proof forest to root of this proof tree
  Trace("cc:proof") << "CC PROOF reversing proof tree\n";
  // c and p are child and parent in (old) proof tree
  Cid c = a, p = d_proof[a];
  Node edgePf = d_proofLabel[a];
  // when we hit null p, we're at the (former) root
  Trace("cc:proof") << "CC PROOF start at c == " << c << std::endl
                    << "                  p == " << p << std::endl
                    << "             edgePf == " << edgePf << std::endl;
  while(p != 0) {
    // in proof forest,
    // we have edge   c --edgePf-> p
    // turn it into   c <-edgePf-- p

    Cid pParSave = d_proof[p];
    Node pLabelSave = d_proofLabel[p];
    d_proof.set(p, c);
    d_proofLabel.set(p, edgePf);
    c = p;
    p = pParSave;
    edgePf = pLabelSave;
    Trace("cc:proof") << "CC PROOF now   at c == " << c << std::endl
                      << "                  p == " << p << std::endl
                      << "             edgePf == " << edgePf << std::endl;
  }

  // add an edge from a to b
  d_proof.set(a, b);
  d_proofLabel.set(a, e);
}/* mergeProof() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::normalize(TNode t) const
  throw(AssertionException) {
  //Trace("cc:detail") << "normalize " << t << std::endl;
  if(!isCongruenceOperator(t)) {// t is a constant
    if(hasCid(t)) {
      t = node(find(cid(t)));
    }
    //Trace("cc:detail") << "  find " << t << std::endl;
    return t;
  } else {// t is an apply
    NodeBuilder<> apb(kind::TUPLE);
    Assert(normalize(t.getOperator()) == t.getOperator(),
           "CongruenceClosure:: bad state: "
           "function symbol merged with another");
    if(t.getMetaKind() == kind::metakind::PARAMETERIZED) {
      apb << t.getOperator();
    }
    Node n;
    bool allConstants = (!isCongruenceOperator(n));
    for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
      TNode c = *i;
      n = normalize(c);
      apb << n;
      allConstants = (allConstants && !isCongruenceOperator(n));
    }

    Node ap = apb;
    //Trace("cc:detail") << "  got ap " << ap << std::endl;

    Node theLookup = lookup(ap);
    if(allConstants && !theLookup.isNull()) {
      Assert(theLookup.getKind() == kind::EQUAL ||
             theLookup.getKind() == kind::IFF);
      Assert(isCongruenceOperator(theLookup[0]));
      Assert(!isCongruenceOperator(theLookup[1]));
      return hasCid(theLookup[1]) ? node(find(cid(theLookup[1]))) : TNode(theLookup[1]);
    } else {
      NodeBuilder<> fa(t.getKind());
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        fa << *i;
      }
      // ensure a hard Node link exists for the return
      Node n = fa;
      return n;
    }
  }
}/* normalize() */


// This is the find() operation for the auxiliary union-find.  This
// union-find is not context-dependent, as it's used only during
// explain().  It does path compression.
template <class OutputChannel>
typename CongruenceClosure<OutputChannel>::Cid
CongruenceClosure<OutputChannel>::highestNode(Cid a, UnionFind_t& unionFind) const
  throw(AssertionException) {
  Cid i = unionFind[a];
  if(i == 0) {
    return a;
  } else {
    return unionFind[a] = highestNode(i, unionFind);
  }
}/* highestNode() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::explainAlongPath(Cid a, Cid c, PendingProofList_t& pending, UnionFind_t& unionFind, std::list<Node>& pf)
  throw(AssertionException) {

  a = highestNode(a, unionFind);
  Assert(c == highestNode(c, unionFind));

  while(a != c) {
    Cid b = d_proof[a];
    Node e = d_proofLabel[a];
    if(e.getKind() == kind::EQUAL ||
       e.getKind() == kind::IFF) {
      pf.push_back(e);
    } else {
      Assert(e.getKind() == kind::TUPLE);
      pf.push_back(e[0]);
      pf.push_back(e[1]);
      Assert(isCongruenceOperator(e[0][0]));
      Assert(!isCongruenceOperator(e[0][1]));
      Assert(isCongruenceOperator(e[1][0]));
      Assert(!isCongruenceOperator(e[1][1]));
      Assert(e[0][0].getNumChildren() == e[1][0].getNumChildren());
      Assert(e[0][0].getOperator() == e[1][0].getOperator(),
             "CongruenceClosure:: bad state: function symbols should be equal");
      // shouldn't have to prove this for operators
      //pending.push_back(std::make_pair(e[0][0].getOperator(), e[1][0].getOperator()));
      for(int i = 0, nc = e[0][0].getNumChildren(); i < nc; ++i) {
        pending.push_back(std::make_pair(e[0][0][i], e[1][0][i]));
      }
    }
    unionFind[a] = b;
    a = highestNode(b, unionFind);
  }
}/* explainAlongPath() */


template <class OutputChannel>
typename CongruenceClosure<OutputChannel>::Cid
CongruenceClosure<OutputChannel>::nearestCommonAncestor(Cid a, Cid b, UnionFind_t& unionFind)
  throw(AssertionException) {
  SeenSet_t seen;

  Assert(find(a) == find(b));

  do {
    a = highestNode(a, unionFind);
    seen[a] = true;
    a = d_proof[a];
  } while(a != 0);

  for(;;) {
    b = highestNode(b, unionFind);
    if(seen[b]) {
      return b;
    }
    b = d_proof[b];

    Assert(b != 0);
  }
}/* nearestCommonAncestor() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::explain(Node a, Node b)
  throw(CongruenceClosureException, AssertionException) {

  Assert(a != b);

  if(!areCongruent(a, b)) {
    Debug("cc") << "EXPLAIN a   " << a << std::endl
                << "EXPLAIN a'' " << normalize(a) << std::endl
                << "EXPLAIN b   " << b << std::endl
                << "EXPLAIN b'' " << normalize(b) << std::endl;
    throw CongruenceClosureException("asked to explain() congruence of nodes "
                                     "that aren't congruent");
  }

  if(isCongruenceOperator(a)) {
    a = replace(flatten(a));
  }
  if(isCongruenceOperator(b)) {
    b = replace(flatten(b));
  }

  PendingProofList_t pending;
  UnionFind_t unionFind;
  std::list<Node> terms;

  pending.push_back(std::make_pair(a, b));

  Trace("cc") << "CC EXPLAINING " << a << " == " << b << std::endl;

  do {// while(!pending.empty())
    std::pair<Node, Node> eq = pending.front();
    pending.pop_front();

    a = eq.first;
    b = eq.second;

    Cid c = nearestCommonAncestor(cid(a), cid(b), unionFind);

    explainAlongPath(cid(a), c, pending, unionFind, terms);
    explainAlongPath(cid(b), c, pending, unionFind, terms);
  } while(!pending.empty());

  if(Trace.isOn("cc")) {
    Trace("cc") << "CC EXPLAIN final proof has size " << terms.size() << std::endl;
  }

  NodeBuilder<> pf(kind::AND);
  while(!terms.empty()) {
    Node p = terms.front();
    terms.pop_front();
    Trace("cc") << "CC EXPLAIN " << p << std::endl;
    p = proofRewrite(p);
    Trace("cc") << "   rewrite " << p << std::endl;
    if(!p.isNull()) {
      pf << p;
    }
  }

  Trace("cc") << "CC EXPLAIN done" << std::endl;

  Assert(pf.getNumChildren() > 0);

  if(pf.getNumChildren() == 1) {
    d_explanationLength.addEntry(1.0);
    return pf[0];
  } else {
    d_explanationLength.addEntry(double(pf.getNumChildren()));
    return pf;
  }
}/* explain() */


template <class OutputChannel>
std::ostream& operator<<(std::ostream& out,
                         const CongruenceClosure<OutputChannel>& cc) {

  typedef typename CongruenceClosure<OutputChannel>::Cid Cid;
  typedef typename CongruenceClosure<OutputChannel>::ClassList ClassList;
  typedef typename CongruenceClosure<OutputChannel>::UseList UseList;
  typedef typename CongruenceClosure<OutputChannel>::LookupMap LookupMap;
  typedef typename CongruenceClosure<OutputChannel>::PropagateList PropagateList;

  out << "==============================================" << std::endl;

  out << "Representatives [that aren't just themselves]:" << std::endl;
  for(Cid i = 1; i < cc.d_representative.size(); ++i) {
    Cid p = cc.d_representative[i];
    if(p != 0) {
      out << "  " << cc.node(i) << " => " << cc.node(p) << std::endl;
    }
  }

  out << "ClassLists [that aren't just themselves]:" << std::endl;
  for(Cid i = 1; i < cc.d_reverseCidMap.size(); ++i) {
    const ClassList& cl = cc.classList(i);
    if(cc.find(i) == i) {
      typename ClassList::const_iterator j = cl.begin();
      if(++j != cl.end()) {// has > 1 element
        out << "  " << cc.node(i) << " =>" << std::endl;
        if(Debug.isOn("cc:detail")) {
          cl.debugCheck();
        }
        for(j = cl.begin(); j != cl.end(); ++j) {
          out << "      " << cc.node(*j) << std::endl;
        }
      }
    }
  }

  out << "UseLists:" << std::endl;
  for(Cid i = 1; i < cc.d_useLists.size(); ++i) {
    if(cc.find(i) == i && cc.d_useLists[i] != NULL && cc.d_useLists[i]->begin() != cc.d_useLists[i]->end()) {
      out << "  " << cc.node(i) << " =>" << std::endl;
      const ClassList& cl = cc.classList(i);
      for(typename ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
        const UseList& ul = cc.useList(*cli);
        for(typename UseList::const_iterator i = ul.begin(); i != ul.end(); ++i) {
          out << "      " << *i << std::endl;
        }
      }
    }
  }

  out << "Lookup:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::LookupMap::const_iterator i = cc.d_lookup.begin(); i != cc.d_lookup.end(); ++i) {
    TNode n = (*i).second;
    out << "  " << (*i).first << " => " << n << std::endl;
  }

  out << "PropagateLists:" << std::endl;
  for(Cid i = 1; i < cc.d_propagate.size(); ++i) {
    if(! cc.d_propagate[i].empty()) {
      out << "  " << cc.node(i) << " =>" << std::endl;
      for(std::vector<Node>::const_iterator j = cc.d_propagate[i].begin(); j != cc.d_propagate[i].end(); ++j) {
        out << "      " << *j << std::endl;
      }
    }
  }

  out << "Care set:" << std::endl;
  for(typename CongruenceClosure<OutputChannel>::CareSet_t::const_iterator i = cc.d_careSet.begin(); i != cc.d_careSet.end(); ++i) {
    out << "  " << *i << std::endl;
  }

  out << "==============================================" << std::endl;

  return out;
}

}/* CVC4 namespace */

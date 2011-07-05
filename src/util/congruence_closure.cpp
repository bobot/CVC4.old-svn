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
bool CongruenceClosure<OutputChannel>::areCongruent(TNode a, TNode b) throw(AssertionException) {
  Assert(hasCid(a));
  Assert(hasCid(b));

  if(Debug.isOn("cc:ac")) {
    Debug("cc:ac") << "CC areCongruent? " << a << "  ==  " << b << std::endl;
    Debug("cc:ac") << "  a   " << a << std::endl;
    Debug("cc:ac") << "  a'  " << node(find(cid(a))) << std::endl;
    Debug("cc:ac") << "  a'' " << normalize(a) << std::endl;
    Debug("cc:ac") << "  b   " << b << std::endl;
    Debug("cc:ac") << "  b'  " << node(find(cid(b))) << std::endl;
    Debug("cc:ac") << "  b'' " << normalize(b) << std::endl;
  }

  return normalize(a) == normalize(b);
}

// FIXME probably this isn't sufficient as a canonizer
template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::normalize(TNode n) const {
  if(!hasCid(n)) {
    return n;
  } else if(!isCongruenceOperator(n)) {
    return node(find(cid(n)));
  } else {
    Node m = rewriteWithRepresentatives(node(find(cid(n))));
    std::vector<Cid> v;
    if(m.getMetaKind() == kind::metakind::PARAMETERIZED) {
      if(!hasCid(m.getOperator())) {
        return m;
      }
      v.push_back(/*find(*/cid(m.getOperator())/*)*/);
    }
    for(Node::iterator i = m.begin(); i != m.end(); ++i) {
      if(!hasCid(*i)) {
        return m;
      }
      v.push_back(find(cid(*i)));
    }
    Cid lv = lookup(v);
    if(lv == 0) {
      return m;
    } else {
      return node(find(lv));
    }
  }
}

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::breakLookupCycle(Cid ind, Cid app, TNode inputEq) {
  Assert(!isApplication(ind));
  Assert(isApplication(app));
  // Look for a lookup cycle.  This happens if we have a chain
  // of equalities of applications, none of which are known to
  // be equal to an individual.
  //
  // E.g., previously f(x) = f(y) , f(y) = f(z) , f(z) = f(w).
  // Now say we get f(w) = w.  We're at this point in the code;
  // equality between an application and an individual, and the
  // application has a lookup.  We follow its chain of lookups
  // until we come to the end (the cycle f(y) <--> f(x) in the
  // lookup map), and break that cycle by setting the lookup of
  // f(x) to w with the conjunction of (transitive) equalities
  // as a reason.
  Debug("cc") << "CC look for lookup cycle: " << node(app) << std::endl;
  Cid lp = app, l = lookup(app);
  NodeBuilder<> conj(kind::AND);
  std::stack< std::pair<Cid, NodeBuilder<> > > stk;
  stk.push(make_pair(app, NodeBuilder<>(kind::AND)));
  stk.top().second << inputEq;
  stk.push(make_pair(l, stk.top().second));
  stk.top().second << lookupReason(l);
  while(isApplication(l) && lp != lookup(l)) {
    Debug("cc") << "CC look for lookup cycle: " << node(l) << std::endl;
    lp = l;
    l = lookup(l);
    stk.push(make_pair(l, stk.top().second));
    stk.top().second << lookupReason(l);
  }
  if(isApplication(l)) {
    Debug("cc") << "CC look for lookup cycle: END with cycle" << std::endl;
    Debug("cc") << "CC cycle: " << node(lp) << " -> " << node(lookup(lp)) << std::endl;
    Debug("cc") << "CC cycle: " << node(l) << " -> " << node(lookup(l)) << std::endl;
    while(!stk.empty()) {
      // set lookup of l to t
      l = stk.top().first;
      Debug("cc") << "CC breaking cycle/chain[" << stk.size() - 1 << "] by setting lookup of " << node(l) << " to: " << node(ind) << "' == " << node(find(ind)) << std::endl;
      NodeBuilder<>& b = stk.top().second;
      Node n;
      if(b.getNumChildren() > 1) {
        n = b;
      } else {
        n = b[0];
        b.clear();
      }
      setLookup(l, n, find(ind));
      concatUseLists(l, find(ind));
      stk.pop();
    }
  } else {
    Debug("cc") << "CC look for lookup cycle: END with individual " << node(lp) << " -> " << node(l) << std::endl;
    Node n = stk.top().second;
    Debug("cc") << "CC lookup chain: pending.push_back " << node(ind) << " , " << node(l) << " , " << n << std::endl;
    d_pending.push_back(make_triple(ind, l, n));

    // TODO break the chain on this path
    Unimplemented();
  }
}

/* From [Nieuwenhuis & Oliveras]
1. Procedure Merge(s=t)
2.   If s and t are constants a and b Then
3.     add a=b to Pending
4.     Propagate()
5.   Else ** s=t is of the form f(a1, a2)=a **
6.     If Lookup(a1', a2') is some f(b1, b2)=b Then
7.       add ( f(a1, a2)=a, f(b1, b2)=b ) to Pending
8.       Propagate()
9.     Else
10.      set Lookup(a1', a2') to f(a1, a2)=a
11.      add f(a1, a2)=a to UseList(a1') and to UseList(a2')
*/

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::merge(Cid s, Cid t, TNode inputEq) {

  Trace("cc") << "CC merge[" << d_context->getLevel() << "]: " << inputEq << std::endl;

  Assert(inputEq.getKind() == kind::EQUAL || inputEq.getKind() == kind::IFF);

  if(find(s) == find(t)) {
    // trivially redundant
    return;
  }

  if(isApplication(s)) {
    if(isApplication(t)) {
      Debug("cc") << "CC lookup: s and t are both applications" << std::endl;
      // s and t are both applications
      TNode ns = node(find(s));
      std::vector<Cid> vs;
      if(ns.getMetaKind() == kind::metakind::PARAMETERIZED) {
        vs.push_back(/*find(*/cid(ns.getOperator())/*)*/);
      }
      for(TNode::iterator i = ns.begin(); i != ns.end(); ++i) {
        vs.push_back(find(cid(*i)));
      }

      TNode nt = node(find(t));
      std::vector<Cid> vt;
      if(nt.getMetaKind() == kind::metakind::PARAMETERIZED) {
        vt.push_back(/*find(*/cid(nt.getOperator())/*)*/);
      }
      for(TNode::iterator i = nt.begin(); i != nt.end(); ++i) {
        vt.push_back(find(cid(*i)));
      }

      if(lookup(vs) == 0) {
        if(lookup(vt) == 0) {
          // neither application has a lookup;
          // schedule the merger of these two's ECs.
          d_pending.push_back(make_triple(s, t, Node(inputEq)));
        } else {
          // s does not have a lookup, but t does; schedule the merger
          // in the other direction.
#warning fixme look for propagations here ?
          d_pending.push_back(make_triple(t, s, Node(inputEq)));
        }
      } else {
        if(lookup(vt) == 0) {
          // s has a lookup, t does not; merge them
#warning fixme look for propagations here ?
          d_pending.push_back(make_triple(s, t, Node(inputEq)));
        } else {
          // both s and t have lookups

          // that means we have f(x) = k1, f(y) = k2, and now
          // f(x) = f(y).
          // treat as if we discovered via congruence that f(x) = f(y).
          d_pending.push_back(make_triple(lookup(vs), lookup(vt),
                                          NodeManager::currentNM()->mkNode(kind::AND, inputEq, lookupReason(vs), lookupReason(vt))));
        }
      }
    } else {
      Debug("cc") << "CC lookup: s is an application, t is not" << std::endl;
      // s is an application, t is not
      TNode n = node(find(s));
      std::vector<Cid> v;
      if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
        v.push_back(/*find(*/cid(n.getOperator())/*)*/);
      }
      for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
        v.push_back(find(cid(*i)));
      }
      Cid lv = lookup(v);
      if(lv == 0) {
        Debug("cc") << "CC lookup for v is nonexistent, setting lookup" << std::endl;
        setLookup(v, inputEq, find(t));
        concatUseLists(s, t);
      } else {
        Assert(!isApplication(lv));
        Node n = NodeManager::currentNM()->mkNode(kind::TUPLE, inputEq, lookupReason(v));
        Debug("cc") << "CC lookup for v exists, pending.push_back " << node(lv) << " , " << node(t) << " , " << n << std::endl;
        d_pending.push_back(make_triple(lv, t, n));
      }
    }
  } else if(isApplication(t)) {
    Debug("cc") << "CC lookup: s is not an application, but t is" << std::endl;
    // s is not an application, but t is
    TNode n = node(find(t));
    std::vector<Cid> v;
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      v.push_back(/*find(*/cid(n.getOperator())/*)*/);
    }
    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      v.push_back(find(cid(*i)));
    }
    Cid lv = lookup(v);
    if(lv == 0) {
      Debug("cc") << "CC lookup for v is nonexistent, setting lookup" << std::endl;
      setLookup(v, inputEq, find(s));
      concatUseLists(t, s);
    } else {
      Assert(!isApplication(lv));
      Node n = NodeManager::currentNM()->mkNode(kind::TUPLE, inputEq, lookupReason(v));
      Debug("cc") << "CC lookup for v exists, pending.push_back " << node(lv) << " , " << node(s) << " , " << n << std::endl;
      d_pending.push_back(make_triple(lv, s, n));
    }
  } else {
    Debug("cc") << "CC lookup: neither s nor t is an application" << std::endl;
    Debug("cc") << "CC lookup: pending.push_back " << node(s) << " , " << node(t) << " , " << inputEq << std::endl;
    // neither s nor t is an application
    d_pending.push_back(make_triple(s, t, Node(inputEq)));
  }

  propagate();

}/* merge() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::propagate() {
  Debug("cc:detail") << *this;

  while(!d_pending.empty()) {
    bool cancel = false;

    triple<Cid, Cid, Node> tr = d_pending.front();
    d_pending.pop_front();

    Cid s = tr.first;
    Cid t = tr.second;
    Node e = tr.third;

    Trace("cc") << "=== top of propagate loop ===" << std::endl
                << "=== e is " << s << " == " << t << " ===" << std::endl
                << "=== e is " << node(s) << " == " << node(t) << " ===" << std::endl
                << "=== eq is " << e << " ===" << std::endl;

    if(Trace.isOn("cc:detail")) {
      Trace("cc:detail") << "=====at start=====" << std::endl
                         << "a          :" << node(s) << std::endl
                         << "b          :" << node(t) << std::endl
                         << "alreadyCongruent?:" << areCongruent(node(s), node(t)) << std::endl;
    }
    /*
    if(Debug.isOn("cc:detail")) {
      debug();
    }
    */

    Cid ap = find(s), bp = find(t);
    if(ap != bp) {

      Trace("cc:detail") << "EC[a] == " << node(ap) << std::endl
                         << "EC[b] == " << node(bp) << std::endl;

      std::vector< std::pair<Cid, std::vector<Cid> > > lookupsToLookAt;

      // prop list

      Trace("cc:detail") << "going through propagation list of " << node(bp) << std::endl;
      ClassList& cl = classList(bp);

      if(cl.empty()) {
        // An empty class list means it's the single-entry class list
        // containing the thing itself.  So we patch it up, here.
        //
        // This can happen since we lazily create the single-entry
        // class listss, but they're context-dependent: once we pop
        // above that level, the list is cleared out.
        cl.push_back(bp);
        Trace("cc:detail") << "bp was nullified, fixed" << std::endl;
      }

      for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
        Trace("cc:detail") << "==> at node " << node(*cli) << " in class list of " << node(bp) << std::endl;
        Assert(find(*cli) == bp);
        std::vector<Node>& plist = propagateList(*cli);
        for(std::vector<Node>::iterator i = plist.begin(); i != plist.end(); ++i) {
          Assert((*i).getKind() == kind::EQUAL || (*i).getKind() == kind::IFF);
          Trace("cc:detail") << "    ==> considering " << *i << std::endl;
          Cid c = find(cid((*i)[0]));
          if(c == ap) {
            // the *i != e is so that we don't notify the user of
            // something they notified US of.
            if(find(cid((*i)[1])) == bp && *i != e) {
              Trace("cc:detail") << "        HIT!! ECs are " << node(ap) << " and " << node(bp) << std::endl;
              if(d_out->notifyEntailedEquality(*i)) {
                Trace("cc:detail") << "        in conflict, will CANCEL further propagation" << std::endl;
                cancel = true;
                d_pending.clear();
                goto reps;
              }
            }
          } else if(c == bp && find(cid((*i)[1])) == ap && *i != e) {
            Trace("cc:detail") << "        HIT!! ECs are " << node(bp) << " and " << node(ap) << std::endl;
            if(d_out->notifyEntailedEquality(*i)) {
              Trace("cc:detail") << "        in conflict, CANCELING further propagation" << std::endl;
              cancel = true;
              d_pending.clear();
              goto reps;
            }
          }
        }
      }

      // lookup maps
      Trace("cc:detail") << "going through lookups of " << node(bp) << std::endl;
      for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
        Assert(find(*cli) == bp);
        UseList& ul = useList(*cli);
        Trace("cc:detail") << "CC  -- useList: [" << node(*cli) << "(" << *cli << ":" << *cli << ")]:" << std::endl;
        for(UseList::const_iterator i = ul.begin(); i != ul.end(); ++i) {
          Trace("cc:detail") << "CC  -- useList: [" << node(*cli) << "(" << *cli << ")] " << node(*i) << "(" << *i << ")" << std::endl;

          Assert(isApplication(*i));
          TNode n = node(*i);
          lookupsToLookAt.push_back(make_pair(*i, std::vector<Cid>()));
          std::vector<Cid>& v = lookupsToLookAt.back().second;
          if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
            v.push_back(/*find(*/cid(n.getOperator())/*)*/);
          }
          bool lookAt = false;
          for(TNode::iterator j = n.begin(); j != n.end(); ++j) {
            Cid f = find(cid(*j));
            v.push_back(f);
            lookAt = lookAt || f == bp;
          }
          if(lookAt) {
            Trace("cc:detail") << "    -- have a lookup for " << node(*i) << " and I care!" << std::endl;
          } else {
            v.pop_back();
            Trace("cc:detail") << "    -- have a lookup for " << node(*i) << " but don't care" << std::endl;
            // FIXME delete this path -- everything in the use list should be cared about right??
            InternalError();
          }
        }
      }
      Trace("cc:detail") << "CC in prop done with lookups of " << node(bp) << std::endl;

    reps:

      // rep mapping

      Trace("cc:detail") << "going through representatives of " << node(bp) << std::endl;

      for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
        Assert(find(*cli) == bp);
        d_representative.set(*cli, ap);
      }

      if(!cancel) {
        // use lists

        size_t lookAtIndex = 0;

        Trace("cc:detail") << "going through use list of " << node(bp) << " -- lookupsToLookAt size == " << lookupsToLookAt.size() << std::endl;
        for(ClassList::iterator cli = cl.begin(); cli != cl.end(); ++cli) {
          Assert(find(*cli) == ap);
          UseList& ul = useList(*cli);
          Trace("cc:detail") << "CC  -- useList: [" << node(*cli) << "(" << *cli << ":" << *cli << ")]:" << std::endl;
          for(UseList::const_iterator i = ul.begin(); i != ul.end(); ++i) {
            Trace("cc:detail") << "CC  -- useList: [" << node(*cli) << "(" << *cli << ")] " << node(*i) << "(" << *i << ")" << std::endl;

            bool fixupLookup = false;
            TNode ni = node(*i);
            if(lookAtIndex < lookupsToLookAt.size() &&
               lookupsToLookAt[lookAtIndex].first == *i) {
              Trace("cc:detail") << "    -- this is a lookup we care about!!" << std::endl;
              ++lookAtIndex;
              fixupLookup = true;
            }

            Node rewritten = rewriteWithRepresentatives(ni);
            if(ni != rewritten) {
              Node eq = NodeManager::currentNM()->mkNode(kind::TUPLE, ni, rewritten);

              Cid c = cid(rewritten);
              Trace("cc:detail") << "    -- rewritten to " << rewritten << "(" << c << ")" << std::endl;
              //d_pending.push_back(make_triple(*i, c, eq));
              Assert(fixupLookup);
              if(lookup(c) != 0) {
                Cid lc = lookup(c);
                Cid clash = lookup(lookupsToLookAt[lookAtIndex - 1].second);
                Trace("cc:detail") << "    -- lookup clash: " << node(lc) << " -and- " << node(clash) << std::endl;
                // if already merged, forget about it
                if(find(lc) == find(clash)) {
                  Trace("cc:detail") << "    -- ignore the second one, eq already represented in UF forest" << std::endl;
                } else {
                  Trace("cc:detail") << "    -- new eq here, will merge " << node(find(lc)) << " -and- " << node(find(clash)) << std::endl;
                  Node theTwoLookups = NodeManager::currentNM()->mkNode(kind::AND, lookupReason(c), lookupReason(lookupsToLookAt[lookAtIndex - 1].second));
                  d_pending.push_back(make_triple(find(lc), find(clash), theTwoLookups));
                }
              } else {
                setLookup(c, lookupReason(lookupsToLookAt[lookAtIndex - 1].second), lookup(lookupsToLookAt[lookAtIndex - 1].second));
              }
            } else {
              Trace("cc:detail") << "    -- rewritten to self" << std::endl;
            }
          }
        }
        // make sure we got 'em all
        Assert(lookAtIndex == lookupsToLookAt.size());
        Trace("cc:detail") << "CC in prop done with useList of " << node(bp) << std::endl;

        // finally, notify client if bp was cared about, and care about ap
        if(d_careTerms.find(bp) != d_careTerms.end()) {
          d_out->notifyMerge(node(bp), node(ap));
          d_careTerms.insert(ap);
        }
      }

      Assert(&classList(ap) != &classList(bp));
      if(Trace.isOn("cc:detail")) {
        {
          Trace("cc:detail") << "class list of " << node(ap) << " is:" << std::endl;
          ClassList& cl = classList(ap);
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }

        {
          Trace("cc:detail") << "class list of " << node(bp) << " is:" << std::endl;
          ClassList& cl = classList(bp);
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }
      }

      Debug("cc:detail") << "concat class lists of " << node(ap) << " and " << node(bp) << std::endl;
      // hack to get around the fact that lists empty themselves on
      // backtrack (but should always contain themselves)
      ClassList& clap = classList(ap);
      ClassList& clbp = classList(bp);
      if(clap.empty()) {
        clap.push_back(ap);
        Trace("cc:detail") << "ap was nullified, fixed" << std::endl;
      }
      Assert(!clbp.empty()); // should have been fixed above
      clap.concat(clbp);
      mergeProof(s, t, e);

      if(Trace.isOn("cc:detail")) {
        Trace("cc:detail") << "post-concat:::" << std::endl;
        {
          Trace("cc:detail") << "class list of " << node(ap) << " is:" << std::endl;
          ClassList& cl = classList(ap);
          for(ClassList::iterator i = cl.begin(); i != cl.end(); ++i) {
            Trace("cc:detail") << " : " << node(*i) << std::endl;
          }
        }
      }

    } else {
      Trace("cc:detail") << "CCs the same ( == " << ap << "), do nothing." << std::endl;
    }

    if(Trace.isOn("cc:detail")) {
      Trace("cc:detail") << "=====at end=====" << std::endl
                         << "a          :" << node(s) << std::endl
                         << "a'         :" << node(find(s)) << std::endl
                         << "b          :" << node(t) << std::endl
                         << "b'         :" << node(find(t)) << std::endl
                         << "alreadyCongruent?:" << areCongruent(node(s), node(t)) << std::endl;
    }
    Assert(areCongruent(node(s), node(t)));
    /*
    if(Debug.isOn("cc:detail")) {
      debug();
    }
    */
  }
}/* propagate() */


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::setLookup(const std::vector<Cid>& a, TNode b, Cid c) {
  Assert(b.getKind() == kind::EQUAL ||
         b.getKind() == kind::IFF ||
         b.getKind() == kind::AND);
#   warning FIXME -- add kind identity to Cid vector??
  if(Debug.isOn("cc")) {
    Debug("cc") << "setting lookup of [";
    for(std::vector<Cid>::const_iterator i = a.begin(); i != a.end();) {
      Debug("cc") << node(*i);
      Assert(d_reverseCidMap.size() > *i);
      if(++i != a.end()) {
        Debug("cc") << ",";
      }
    }
    Debug("cc") << "] to " << b << " , " << node(c) << std::endl;
  }

  d_lookup[a] = std::make_pair(b, c);
}


template <class OutputChannel>
void CongruenceClosure<OutputChannel>::mergeProof(Cid a, Cid b, TNode e) {
  Trace("cc") << "  -- merge-proofing " << node(a) << "\n"
              << "                and " << node(b) << "\n"
              << "               with " << e << "\n";

  // proof forest gets a -> b labeled with e

  // first reverse all the edges in proof forest to root of this proof tree
  Trace("cc") << "CC PROOF reversing proof tree\n";
  // c and p are child and parent in (old) proof tree
  Cid c = a, p = d_proof[a];
  Node edgePf = d_proofLabel[a];
  // when we hit null p, we're at the (former) root
  Trace("cc") << "CC PROOF start at c == " << c << std::endl
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
    Trace("cc") << "CC PROOF now   at c == " << c << std::endl
                << "                  p == " << p << std::endl
                << "             edgePf == " << edgePf << std::endl;
  }

  // add an edge from a to b
  d_proof.set(a, b);
  d_proofLabel.set(a, e);
}/* mergeProof() */


// This is the find() operation for the auxiliary union-find.  This
// union-find is not context-dependent, as it's used only during
// explain().  It does path compression.
template <class OutputChannel>
typename CongruenceClosure<OutputChannel>::Cid
CongruenceClosure<OutputChannel>::highestNode(Cid a, UnionFind_t& unionFind) const
  throw(AssertionException) {
  UnionFind_t::iterator i = unionFind.find(a);
  if(i == unionFind.end()) {
    return a;
  } else {
    return unionFind[a] = highestNode((*i).second, unionFind);
  }
}/* highestNode() */

static void addToProof(TNode n, std::list<Node>& pf) {
  if(n.getKind() == kind::AND) {
    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      addToProof(*i, pf);
    }
  } else {
    Assert(n.getKind() == kind::IFF || n.getKind() == kind::EQUAL);
    pf.push_back(n);
  }
}

template <class OutputChannel>
void CongruenceClosure<OutputChannel>::debugProof(const std::list<Node>& pf, TNode a, TNode b) const throw(AssertionException) {
#ifdef CVC4_DEBUG
  if(Debug.isOn("cc")) {
    Debug("cc") << "checking proof of " << a << " == " << b << std::endl;
    Assert(a != b);
    std::hash_map<TNode, TNode, TNodeHashFunction> uf;
    for(std::list<Node>::const_iterator i = pf.begin(); i != pf.end(); ++i) {
      Assert((*i).getKind() == kind::IFF || (*i).getKind() == kind::EQUAL);
      Assert((*i)[0] != (*i)[1]);
      TNode x = (*i)[0];
      TNode y = (*i)[1];
      while(!uf[x].isNull()) {
        x = uf[x];
      }
      while(!uf[y].isNull()) {
        y = uf[y];
      }
      uf.insert(std::make_pair(x, y));
    }
    while(!uf[a].isNull()) {
      a = uf[a];
    }
    while(!uf[b].isNull()) {
      b = uf[b];
    }
    Assert(a == b && !a.isNull(),
           "Proof was supposed to prove %s == %s\n...but it didn't!",
           a.toString().c_str(), b.toString().c_str());
  }
#endif /* CVC4_DEBUG */
}

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
      Debug("cc") << "explainAlongPath[" << node(a) << " == " << node(c) << "]: why does " << node(a) << " == " << node(b) << " ??" << std::endl;
      Debug("cc") << "  :: e is " << e << std::endl;
      Assert(e.getKind() == kind::TUPLE);
      Assert(e.getNumChildren() == 2);
      if(isCongruenceOperator(e[0])) {
        // traditional congruence between e[0] and e[1]; simply have
        // to explain why arguments to each are equal
        Debug("cc") << "     :: congruence rule ( " << e[0] << " , " << e[1] << " )" << std::endl;
        Assert(isCongruenceOperator(e[1]));
        Assert(e[0].getNumChildren() == e[1].getNumChildren());
        Assert(e[0].getOperator() == e[1].getOperator(),
               "CongruenceClosure:: bad state: function symbols should be equal");
        for(int i = 0, nc = e[0].getNumChildren(); i < nc; ++i) {
          pending.push_back(std::make_pair(cid(e[0][i]), cid(e[1][i])));
        }
      } else {
        // complicated case: we have an input equality (or conjunction
        // of them) on the left, and an input equality (or conjunction
        // of them) on the right.
        Debug("cc") << "     :: transitivity of equalities rule ( " << e[0] << " , " << e[1] << " )" << std::endl;
        Assert(e[0].getKind() == kind::IFF || e[0].getKind() == kind::EQUAL || e[0].getKind() == kind::AND);
        Assert(e[1].getKind() == kind::IFF || e[1].getKind() == kind::EQUAL || e[1].getKind() == kind::AND);
        std::pair<TNode, TNode> pr0 = whatIsProvenWithTransitivity(e[0]);
        Debug("cc") << "     :: " << e[0] << std::endl
                    << "            proves that " << pr0.first << " == " << pr0.second << std::endl;
        std::pair<TNode, TNode> pr1 = whatIsProvenWithTransitivity(e[1]);
        Debug("cc") << "     :: " << e[1] << std::endl
                    << "            proves that " << pr1.first << " == " << pr1.second << std::endl;
        // at this point, we know the two terms in pr0 are equal, and
        // that the two in pr1 are equal.
        if(pr0.first == pr1.first || pr0.first == pr1.second ||
           pr0.second == pr1.first || pr0.second == pr1.second) {
          // just output both (chains of) equalities, and we're done
          addToProof(e[0], pf);
          addToProof(e[1], pf);
        } else {
          // other complicated cases..
          Unimplemented();
        }
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
    seen.insert(a);
    a = d_proof[a];
  } while(a != 0);

  for(;;) {
    b = highestNode(b, unionFind);
    if(seen.find(b) != seen.end()) {
      return b;
    }
    b = d_proof[b];

    Assert(b != 0);
  }
}/* nearestCommonAncestor() */


template <class OutputChannel>
Node CongruenceClosure<OutputChannel>::explain(Node an, Node bn)
  throw(CongruenceClosureException, AssertionException) {

  Assert(an != bn);

  if(!areCongruent(an, bn)) {
    Debug("cc") << "explain: " << an << std::endl << " and   : " << bn << std::endl;
    throw CongruenceClosureException("asked to explain() congruence of nodes "
                                     "that aren't congruent");
  }

  Cid a = cid(an), b = cid(bn);

  PendingProofList_t pending;
  UnionFind_t unionFind;
  std::list<Node> terms;

  pending.push_back(std::make_pair(a, b));

  Trace("cc") << "CC EXPLAINING " << node(a) << " == " << node(b) << std::endl;

  do {// while(!pending.empty())
    std::pair<Cid, Cid> eq = pending.front();
    pending.pop_front();

    a = eq.first;
    b = eq.second;

    Cid c = nearestCommonAncestor(a, b, unionFind);

    explainAlongPath(a, c, pending, unionFind, terms);
    explainAlongPath(b, c, pending, unionFind, terms);
  } while(!pending.empty());

  Trace("cc") << "CC EXPLAIN final proof has size " << terms.size() << std::endl;

  NodeBuilder<> pf(kind::AND);
  while(!terms.empty()) {
    Node p = terms.front();
    terms.pop_front();
    Trace("cc") << "CC EXPLAIN " << p << std::endl;
    pf << p;
  }

  Trace("cc") << "CC EXPLAIN done" << std::endl;

  if(Debug.isOn("cc")) {
    //debugProof(terms, an, bn);
  }

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

  /*
  if(Debug.isOn("cc:detail")) {
    cc.debug();
  }
  */

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
          out << "      " << cc.node(*i) << std::endl;
        }
      }
    }
  }

  out << "Lookup map:" << std::endl;
  for(typename LookupMap::const_iterator i = cc.d_lookup.begin(); i != cc.d_lookup.end(); ++i) {
    out << "  [";
    const std::pair<std::vector<Cid>, std::pair<Node, Cid> >& pr = *i;
    for(typename std::vector<Cid>::const_iterator j = pr.first.begin(); j != pr.first.end();) {
      out << cc.node(*j);
      if(++j != pr.first.end()) {
        out << ",";
      }
    }
    out << "] => " << cc.node((*i).second.second) << "  (" << (*i).second.first << ")" << std::endl;
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
  for(Cid i = 1; i < cc.d_reverseCidMap.size(); ++i) {
    if(cc.d_careTerms.find(i) != cc.d_careTerms.end()) {
      out << "  " << cc.node(i) << std::endl;
    }
  }

  out << "==============================================" << std::endl;

  return out;
}

}/* CVC4 namespace */

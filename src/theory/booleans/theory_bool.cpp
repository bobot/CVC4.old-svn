/*********************                                                        */
/*! \file theory_bool.cpp
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
 ** \brief The theory of booleans.
 **
 ** The theory of booleans.
 **/

#include "theory/theory.h"
#include "theory/booleans/theory_bool.h"
#include "theory/valuation.h"
#include "util/boolean_simplification.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace booleans {

Node TheoryBool::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::VARIABLE:
    // case for Boolean vars is implemented in TheoryEngine (since it
    // appeals to the PropEngine to get the value)
    Unreachable();

  case kind::EQUAL: // 2 args
    // should be handled by IFF
    Unreachable();

  case kind::NOT: // 1 arg
    return nodeManager->mkConst(! d_valuation.getValue(n[0]).getConst<bool>());

  case kind::AND: { // 2+ args
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      if(! d_valuation.getValue(*i).getConst<bool>()) {
        return nodeManager->mkConst(false);
      }
    }
    return nodeManager->mkConst(true);
  }

  case kind::IFF: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() ==
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::IMPLIES: // 2 args
    return nodeManager->mkConst( (! d_valuation.getValue(n[0]).getConst<bool>()) ||
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::OR: { // 2+ args
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      if(d_valuation.getValue(*i).getConst<bool>()) {
        return nodeManager->mkConst(true);
      }
    }
    return nodeManager->mkConst(false);
  }

  case kind::XOR: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() !=
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::ITE: // 3 args
    // all ITEs should be gone except (bool,bool,bool) ones
    Assert( n[1].getType() == nodeManager->booleanType() &&
            n[2].getType() == nodeManager->booleanType() );
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() ?
                                 d_valuation.getValue(n[1]).getConst<bool>() :
                                 d_valuation.getValue(n[2]).getConst<bool>() );

  default:
    Unhandled(n.getKind());
  }
}

/**
 * Takes an already-simplified node n and add it to a builder of type
 * AND or OR, adding to substitutions and replacements as necessary.
 * This function does not call simplifyRecursive(), so everything
 * should already be simplified!  It is a convenience function to
 * simplifyRecursive().  It itself is recursive, in order to flatten
 * AND and OR.
 */
// returns true if it has short-circuited the AND/OR
bool TheoryBool::addToBuilder(TNode n, NodeBuilder<>& b, Substitutions& outSubstitutions) {

  Assert(!n.isNull());
  Kind bk = b.getKind(), nk = n.getKind();
  Assert(bk == kind::AND || bk == kind::OR);

  if( (n == d_true && bk == kind::AND) || (n == d_false && bk == kind::OR) ) {
    Debug("simplify:bool") << "skipping " << n << endl;
    // do nothing
  } else if( (n == d_false && bk == kind::AND) || (n == d_true && bk == kind::OR) ) {
    Debug("simplify:bool") << "short-circuiting " << n << endl;
    b.clear(bk);
    b << n;
    return false;
  } else if(bk == nk) {
    Debug("simplify:bool") << "flattening " << nk << endl;
    // flatten AND/OR
    for(TNode::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
      if(!addToBuilder(*i, b, outSubstitutions)) {
        return false;
      }
    }
  } else {
    Debug("simplify:bool") << "pushing " << n << endl;
    b << n;
    // Look for substitutions throughout the resulting AND/OR.
    // E.g. if you have "x = 5 AND x * y = 25", you can replace x with
    // 5 in the second conjunct.  If you have "~(x /= 5 OR x * y /= 25)"
    // it's the same thing (the builder will be AND-kinded).
    if(bk == kind::AND) {
      if(nk == kind::EQUAL || nk == kind::IFF) {
        if( n[0].getMetaKind() == kind::metakind::VARIABLE &&
            n[1].getMetaKind() == kind::metakind::CONSTANT ) {
          Debug("simplify:bool") << "found new substitution! "
                                << n[0] << " => " << n[1] << endl;
          outSubstitutions.push_back(make_pair(n[0], n[1]));
        } else if( n[1].getMetaKind() == kind::metakind::VARIABLE &&
                   n[0].getMetaKind() == kind::metakind::CONSTANT ) {
          Debug("simplify:bool") << "found new substitution! "
                                << n[1] << " => " << n[0] << endl;
          outSubstitutions.push_back(make_pair(n[1], n[0]));
        }
      } else if(n.getMetaKind() == kind::metakind::VARIABLE) {
        Debug("simplify:bool") << "found new substitution! "
                              << n << " => " << d_true << endl;
        outSubstitutions.push_back(make_pair(n, d_true));
      } else if(nk == kind::NOT &&
                n[0].getMetaKind() == kind::metakind::VARIABLE) {
        Debug("simplify:bool") << "found new substitution! "
                              << n << " => " << d_false << endl;
        outSubstitutions.push_back(make_pair(n[0], d_false));
      }
    }
  }

  return true;
}

Node TheoryBool::simplify(TNode in, Substitutions& outSubstitutions) {
  return simplifyRecursive(in, outSubstitutions, true, false);
}

// polarity == false means there's an enclosing NOT that we might be
// able to incorporate into this node
Node TheoryBool::simplifyRecursive(TNode in, Substitutions& outSubstitutions,
                                   bool polarity, bool inAnd) {

  if(kindToTheoryId(in.getKind()) != THEORY_BOOL) {
    if(in.getMetaKind() == kind::metakind::VARIABLE) {
      return polarity ? Node(in) : in.notNode();
    }
    Node n = polarity ? Node(in) : in.notNode();
    return d_valuation.simplify(n, outSubstitutions);
  }

  Node n;

  IndentedScope scope(Debug("simplify:bool"));

  Debug("simplify:bool") << "handling " << (polarity ? "" : "NOT ") << in << endl;

  switch(Kind k = in.getKind()) {
  case kind::NOT:
    n = simplifyRecursive(in[0], outSubstitutions, !polarity, inAnd);
    polarity = true;
    break;

  case kind::AND:
  case kind::OR: {
    size_t oldSize = outSubstitutions.size();
    NodeBuilder<> b(polarity ? k : (k == kind::AND ? kind::OR : kind::AND));
    Debug("simplify:bool") << "building an " << b.getKind() << endl;
    for(Node::iterator i = in.begin(), i_end = in.end(); i != i_end; ++i) {
      Debug("simplify:bool") << "performing substitutions" << endl;
      Debug("simplify:bool") << "+  on: " << *i << endl;
      Node n = (*i).substitute(outSubstitutions.begin(), outSubstitutions.end());
      Debug("simplify:bool") << "+ got: " << n << endl;
      Debug("simplify:bool") << "now simplifying subterm " << n << endl;
      n = simplifyRecursive(n, outSubstitutions, polarity, b.getKind() == kind::AND);
      if(b.getKind() != kind::AND) {
        outSubstitutions.resize(oldSize);
      }
      Debug("simplify:bool") << "+ got: " << n << endl;

      addToBuilder(n, b, outSubstitutions);

      Assert(b.getKind() == kind::AND || outSubstitutions.size() == oldSize);
    }
    polarity = true;// it's been handled
    if(outSubstitutions.size() > oldSize) {
      if(Debug.isOn("simplify:bool")) {
        Debug("simplify:bool") << "** outSubsts GREW !!";
        for(unsigned i = oldSize; i < outSubstitutions.size(); ++i) {
          Debug("simplify:bool") << ", " << outSubstitutions[i];
        }
        Debug("simplify:bool") << endl;
      }
      Assert(b.getKind() == kind::AND);
      NodeBuilder<> b2(b.getKind());
      for(NodeBuilder<>::iterator i = b.begin(),
            i_end = b.end();
          i != i_end;
          ++i) {
        Debug("simplify:bool") << "performing substitutions" << endl;
        Debug("simplify:bool") << "+  on: " << (*i) << endl;
        b2 << simplifyRecursive((*i).substitute(outSubstitutions.begin(), outSubstitutions.end()), outSubstitutions, true, b.getKind() == kind::AND);
        Debug("simplify:bool") << "+ got: " << b2[b2.getNumChildren() - 1] << endl;
      }
      Node n2;
      if(b2.getNumChildren() == 1) {
        n = b2[0];
      } else if(b2.getNumChildren() == 0) {
        n = b2.getKind() == kind::AND ? d_true : d_false;
      } else {
        n = b2;
        n = BooleanSimplification::simplify(n);
      }
      // re-add the substitutions we performed (they've been simplified away!)
      b2.clear(b.getKind());
      if(n.getKind() == b2.getKind()) {
        for(Node::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
          b2 << *i;
        }
      } else {
        b2 << n;
      }
      b.clear();
      if(!inAnd) {
        for(Substitutions::const_iterator
              i = outSubstitutions.begin(),
              i_end = outSubstitutions.end();
            i != i_end;
            ++i) {
          b2 << NodeManager::currentNM()->mkNode( (*i).first.getType().isBoolean() ?
                                                  kind::IFF :
                                                  kind::EQUAL,
                                                  (*i).first, (*i).second );
        }
      }
      if(b2.getNumChildren() == 1) {
        n = b2[0];
        b2.clear();
      } else {
        if(b2.getNumChildren() == 0) {
          n = b2.getKind() == kind::AND ? d_true : d_false;
          b2.clear();
        } else {
          n = b2;
          n = BooleanSimplification::simplify(n);
        }
      }
    } else {
      Debug("simplify:bool") << "** outSubsts didn't grow" << endl;
      if(b.getNumChildren() == 1) {
        n = b[0];
        b.clear();
      } else {
        if(b.getNumChildren() == 0) {
          n = b.getKind() == kind::AND ? d_true : d_false;
          b.clear();
        } else {
          n = b;
          n = BooleanSimplification::simplify(n);
        }
      }
    }
  }
    break;

  case kind::IMPLIES:
    if(polarity) {
      Debug("simplify:bool") << "converting to ~A OR B" << endl;
      n = simplifyRecursive(in[0].notNode().orNode(in[1]), outSubstitutions, true, inAnd);
    } else {
      Debug("simplify:bool") << "converting to A AND ~B" << endl;
      n = simplifyRecursive(in[0].andNode(in[1].notNode()), outSubstitutions, true, inAnd);
      polarity = true;// already handled the "NOT"
    }
    break;

  case kind::ITE: {
    size_t oldSize = outSubstitutions.size();
    Node cond = simplifyRecursive(in[0], outSubstitutions, true, false);
    outSubstitutions.resize(oldSize);
    Node then = simplifyRecursive(in[1], outSubstitutions, polarity, false);
    outSubstitutions.resize(oldSize);
    Node els = simplifyRecursive(in[2], outSubstitutions, polarity, false);
    outSubstitutions.resize(oldSize);
    if(cond == d_true) {
      n = then;
      polarity = true;// NOT is already handled
    } else if(cond == d_false) {
      n = els;
      polarity = true;// NOT is already handled
    } else {
      n = cond.iteNode(then, els);
      polarity = true;
    }
  }
    break;

  case kind::IFF: {
    NodeBuilder<> b(k);
    size_t oldSize = outSubstitutions.size();
    b << simplifyRecursive(in[0], outSubstitutions, true, false);
    outSubstitutions.resize(oldSize);
    b << simplifyRecursive(in[1], outSubstitutions, true, false);
    outSubstitutions.resize(oldSize);
    if(b[0] == b[1]) {
      b.clear();
      n = d_true;
    } else {
      n = Node(b);
    }
  }
    break;

  case kind::EQUAL: {
    Debug("simplify:bool") << "in EQUALity" << endl;
    NodeBuilder<> b(k);
    Debug("simplify:bool") << "+simplify " << in[0] << endl;
    size_t oldSize = outSubstitutions.size();
    b << d_valuation.simplify(in[0], outSubstitutions);
    outSubstitutions.resize(oldSize);
    Debug("simplify:bool") << "+simplify " << in[1] << endl;
    b << d_valuation.simplify(in[1], outSubstitutions);
    outSubstitutions.resize(oldSize);
    Debug("simplify:bool") << "+check " << b[0] << " == " << b[1] << endl;
    if(b[0] == b[1]) {
      n = d_true;
    } else {
      n = Node(b);
    }
    Debug("simplify:bool") << "+n is " << n << endl;
  }
    break;

  default:
    Debug("simplify:bool") << "NOT DOING ANYTHING FOR " << k << " with polarity " << polarity << endl;
    n = in;

  }/* switch(in.kind) */

  Assert(!n.isNull());
  // if the enclosing NOT wasn't incorporated, wrap it around
  Debug("simplify:bool") << "negate? " << (polarity ? "no" : "yes") << endl;
  n = polarity ? n : BooleanSimplification::negate(n);
  Debug("simplify:bool") << "+n is " << n << endl;
  return n;
}

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

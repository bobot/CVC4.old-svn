/*********************                                                        */
/*! \file union_find.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Path-compressing, backtrackable union-find using an undo
 ** stack. Refactored from the UF union-find.
 **
 ** Path-compressing, backtrackable union-find using an undo stack
 ** rather than storing items in a CDMap<>.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__UNION_FIND_H
#define __CVC4__THEORY__DATATYPES__UNION_FIND_H

#include <utility>
#include <vector>
#include <ext/hash_map>

#include "expr/node.h"
#include "context/cdo.h"

namespace CVC4 {

namespace context {
  class Context;
}/* CVC4::context namespace */

namespace theory {
namespace datatypes {

// NodeType \in { Node, TNode }
template <class NodeType, class NodeHash>
class UnionFind : context::ContextNotifyObj {
  /** Our underlying map type. */
  typedef __gnu_cxx::hash_map<NodeType, NodeType, NodeHash> MapType;

  /**
   * Our map of Nodes to their canonical representatives.
   * If a Node is not present in the map, it is its own
   * representative.
   */
  MapType d_map;

  /** Our undo stack for changes made to d_map. */
  std::vector<std::pair<TNode, TNode> > d_trace;

  /** Our current offset in the d_trace stack (context-dependent). */
  context::CDO<size_t> d_offset;

public:
  UnionFind(context::Context* ctxt) :
    context::ContextNotifyObj(ctxt),
    d_offset(ctxt, 0) {
  }

  ~UnionFind() throw() { }

  /**
   * Return a Node's union-find representative, doing path compression.
   */
  inline TNode find(TNode n);

  /**
   * Return a Node's union-find representative, NOT doing path compression.
   * This is useful for Assert() statements, debug checking, and similar
   * things that you do NOT want to mutate the structure.
   */
  inline TNode debugFind(TNode n) const;

  /**
   * Set the canonical representative of n to newParent.  They should BOTH
   * be their own canonical representatives on entry to this funciton.
   */
  inline void setCanon(TNode n, TNode newParent);

private:
  /**
   */
  inline bool isClashConstructor( TNode n1, TNode n2 );
  inline bool isCycleConstructor( TNode n1, TNode n2 );

public:
  /**
   */
  inline bool isInconsistentConstructor( TNode n1, TNode n2 );
  inline NodeType checkInconsistent(TNode n, TNode newParent);

  /**
   * Called by the Context when a pop occurs.  Cancels everything to the
   * current context level.  Overrides ContextNotifyObj::notify().
   */
  void notify();

};/* class UnionFind<> */

template <class NodeType, class NodeHash>
inline TNode UnionFind<NodeType, NodeHash>::debugFind(TNode n) const {
  typename MapType::const_iterator i = d_map.find(n);
  if(i == d_map.end()) {
    return n;
  } else {
    return debugFind((*i).second);
  }
}

template <class NodeType, class NodeHash>
inline TNode UnionFind<NodeType, NodeHash>::find(TNode n) {
  Trace("datatypesuf") << "datatypesUF find of " << n << endl;
  typename MapType::iterator i = d_map.find(n);
  if(i == d_map.end()) {
    Trace("datatypesuf") << "datatypesUF   it is rep" << endl;
    return n;
  } else {
    Trace("datatypesuf") << "datatypesUF   not rep: par is " << (*i).second << endl;
    pair<TNode, TNode> pr = *i;
    // our iterator is invalidated by the recursive call to find(),
    // since it mutates the map
    TNode p = find(pr.second);
    if(p == pr.second) {
      return p;
    }
    d_trace.push_back(make_pair(n, pr.second));
    d_offset = d_trace.size();
    Trace("datatypesuf") << "datatypesUF   setting canon of " << n << " : " << p << " @ " << d_trace.size() << endl;
    pr.second = p;
    d_map.insert(pr);
    return p;
  }
}

template <class NodeType, class NodeHash>
inline void UnionFind<NodeType, NodeHash>::setCanon(TNode n, TNode newParent) {
  Assert(d_map.find(n) == d_map.end());
  Assert(d_map.find(newParent) == d_map.end());
  if(n != newParent) {
    Trace("datatypesuf") << "datatypesUF setting canon of " << n << " : " << newParent << " @ " << d_trace.size() << endl;
    d_map[n] = newParent;
    d_trace.push_back(make_pair(n, TNode::null()));
    d_offset = d_trace.size();
  }
}

template <class NodeType, class NodeHash>
inline bool UnionFind<NodeType, NodeHash>::isClashConstructor(TNode n1, TNode n2) {
  if( n1.getKind()==kind::APPLY_CONSTRUCTOR && n2.getKind()==kind::APPLY_CONSTRUCTOR ){
    if( n1.getOperator()!=n2.getOperator() ){
      return true;
    }else{
      Assert( n1.getNumChildren()==n2.getNumChildren() );
      for( int i=0; i<(int)n1.getNumChildren(); i++ ){
        if( isClashConstructor( n1[i], n2[i] ) ){
          return true;
        }
      }
    }
  }
  return false;
}

template <class NodeType, class NodeHash>
inline bool UnionFind<NodeType, NodeHash>::isCycleConstructor(TNode n1, TNode n2) {
  if( n1==n2 ){
    return true;
  }else if( n2.getKind()==kind::APPLY_CONSTRUCTOR ){
    for( int i=0; i<(int)n2.getNumChildren(); i++ ){
      if( isCycleConstructor( n1, n2[i] ) ){
        return true;
      }
    }
  }
  return false;
}

template <class NodeType, class NodeHash>
inline bool UnionFind<NodeType, NodeHash>::isInconsistentConstructor(TNode n1, TNode n2) {
  return isClashConstructor( n1, n2 ) || ( n1!=n2 && ( isCycleConstructor( n1, n2 ) || isCycleConstructor( n2, n1 ) ) );
}

template <class NodeType, class NodeHash>
inline NodeType UnionFind<NodeType, NodeHash>::checkInconsistent(TNode n, TNode newParent) {
  //check for conflicts
  if( n.getKind()==kind::APPLY_CONSTRUCTOR ){
    if( isInconsistentConstructor( n, newParent ) ){
      return newParent;
    }
    typename MapType::iterator it;
    for( it = d_map.begin(); it != d_map.end(); ++it ){
      if( it->second==newParent && isInconsistentConstructor( n, it->first ) ){
        return it->first;
      }
    }
  }
  return Node::null();
}

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /*__CVC4__THEORY__DATATYPES__UNION_FIND_H */

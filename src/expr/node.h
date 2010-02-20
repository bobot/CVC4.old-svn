/*********************                                                        */
/** node.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "expr/node_value.h"

#ifndef __CVC4__NODE_H
#define __CVC4__NODE_H

#include <vector>
#include <string>
#include <iostream>
#include <stdint.h>

#include "cvc4_config.h"
#include "expr/kind.h"
#include "util/Assert.h"

namespace CVC4 {

template <bool count_ref> class NodeTemplate;
typedef NodeTemplate<true> Node;
typedef NodeTemplate<false> NoteT;

inline std::ostream& operator<<(std::ostream&, const Node&);

class NodeManager;

namespace expr {
  class NodeValue;
}/* CVC4::expr namespace */

using CVC4::expr::NodeValue;

/**
 * Encapsulation of an NodeValue pointer.  The reference count is
 * maintained in the NodeValue.
 */
template <bool count_ref> class NodeTemplate {

  friend class NodeValue;
  friend class SoftNode;

  /** A convenient null-valued encapsulated pointer */
  static NodeTemplate s_null;

  /** The referenced NodeValue */
  NodeValue* d_ev;

  bool d_count_ref;

  /** This constructor is reserved for use by the NodeTemplate package; one
   *  must construct an NodeTemplate using one of the build mechanisms of the
   *  NodeTemplate package.
   *
   *  Increments the reference count.
   *
   *  FIXME: there's a type-system escape here to cast away the const,
   *  since the refcount needs to be updated.  But conceptually Nodes
   *  don't change their arguments, and it's nice to have
   *  const_iterators over them.  See notes in .cpp file for
   *  details. */
  // this really does needs to be explicit to avoid hard to track
  // errors with Nodes implicitly wrapping NodeValues
  explicit NodeTemplate(const NodeValue*);

  template <unsigned> friend class NodeBuilder;
  friend class NodeManager;

  /**
   * Assigns the expression value and does reference counting. No assumptions
   * are made on the expression, and should only be used if we know what we are
   * doing.
   *
   * @param ev the expression value to assign
   */
  void assignNodeValue(NodeValue* ev);

  typedef NodeValue::ev_iterator ev_iterator;
  typedef NodeValue::const_ev_iterator const_ev_iterator;

  inline ev_iterator ev_begin();
  inline ev_iterator ev_end();
  inline const_ev_iterator ev_begin() const;
  inline const_ev_iterator ev_end() const;

public:

  /** Default constructor, makes a null expression. */
  NodeTemplate();

  NodeTemplate(const NodeTemplate&);

  /** Destructor.  Decrements the reference count and, if zero,
   *  collects the NodeValue. */
  ~NodeTemplate();

  bool operator==(const NodeTemplate& e) const { return d_ev == e.d_ev; }
  bool operator!=(const NodeTemplate& e) const { return d_ev != e.d_ev; }

  NodeTemplate operator[](int i) const {
    Assert(i >= 0 && i < d_ev->d_nchildren);
    return NodeTemplate(d_ev->d_children[i]);
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   */
  inline bool operator<(const NodeTemplate& e) const;

  NodeTemplate& operator=(const NodeTemplate&);

  size_t hash() const { return d_ev->getId(); }
  uint64_t getId() const { return d_ev->getId(); }

  NodeTemplate eqExpr(const NodeTemplate& right) const;
  NodeTemplate notExpr() const;
  NodeTemplate andExpr(const NodeTemplate& right) const;
  NodeTemplate orExpr(const NodeTemplate& right) const;
  NodeTemplate iteExpr(const NodeTemplate& thenpart, const NodeTemplate& elsepart) const;
  NodeTemplate iffExpr(const NodeTemplate& right) const;
  NodeTemplate impExpr(const NodeTemplate& right) const;
  NodeTemplate xorExpr(const NodeTemplate& right) const;

  NodeTemplate plusExpr(const NodeTemplate& right) const;
  NodeTemplate uMinusExpr() const;
  NodeTemplate multExpr(const NodeTemplate& right) const;

  inline Kind getKind() const;

  inline size_t getNumChildren() const;

  static NodeTemplate null();

  typedef NodeValue::node_iterator iterator;
  typedef NodeValue::node_iterator const_iterator;

  inline iterator begin();
  inline iterator end();
  inline const_iterator begin() const;
  inline const_iterator end() const;

  inline std::string toString() const;
  inline void toStream(std::ostream&) const;

  bool isNull() const;
  bool isAtomic() const;

  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(const AttrKind&);

  template <class AttrKind>
  inline bool hasAttribute(const AttrKind&,
                           typename AttrKind::value_type* = NULL);

  template <class AttrKind>
  inline void setAttribute(const AttrKind&,
                           const typename AttrKind::value_type& value);

  /**
   * Very basic pretty printer for NodeTemplate.
   * @param o output stream to print to.
   * @param indent number of spaces to indent the formula by.
   */
  void printAst(std::ostream & o, int indent = 0) const;
  
private:
  
  /**
   * Pretty printer for use within gdb
   * This is not intended to be used outside of gdb.
   * This writes to the ostream Warning() and immediately flushes
   * the ostream.
   */
  void debugPrint();

};/* class NodeTemplate */

}/* CVC4 namespace */

#include <ext/hash_map>

// for hashtables
namespace __gnu_cxx {
  template <>
  struct hash<CVC4::Node> {
    size_t operator()(const CVC4::Node& node) const {
      return (size_t)node.hash();
    }
  };
}/* __gnu_cxx namespace */

#include "expr/attribute.h"
#include "expr/node_manager.h"

namespace CVC4 {

template <bool count_ref> inline bool NodeTemplate<count_ref>::operator<(const NodeTemplate& e) const {
  return d_ev->d_id < e.d_ev->d_id;
}

inline std::ostream& operator<<(std::ostream& out, const Node& e) {
  e.toStream(out);
  return out;
}

template <bool count_ref> inline Kind NodeTemplate<count_ref>::getKind() const {
  return Kind(d_ev->d_kind);
}

template <bool count_ref> inline std::string NodeTemplate<count_ref>::toString() const {
  return d_ev->toString();
}

template <bool count_ref>
inline void NodeTemplate<count_ref>::toStream(std::ostream& out) const {
  d_ev->toStream(out);
}

template <bool count_ref>
inline typename NodeTemplate<count_ref>::ev_iterator NodeTemplate<count_ref>::ev_begin() {
  return d_ev->ev_begin();
}

template <bool count_ref>
inline typename NodeTemplate<count_ref>::ev_iterator NodeTemplate<count_ref>::ev_end() {
  return d_ev->ev_end();
}

template <bool count_ref>
inline typename NodeTemplate<count_ref>::const_ev_iterator NodeTemplate<count_ref>::ev_begin() const {
  return d_ev->ev_begin();
}

template <bool count_ref>
inline typename NodeTemplate<count_ref>::const_ev_iterator NodeTemplate<count_ref>::ev_end() const {
  return d_ev->ev_end();
}

template <bool count_ref>
inline typename NodeTemplate<count_ref>::iterator NodeTemplate<count_ref>::begin() {
  return d_ev->begin();
}

template <bool count_ref>
inline typename NodeTemplate<count_ref>::iterator NodeTemplate<count_ref>::end() {
  return d_ev->end();
}

template <bool count_ref>
inline typename NodeTemplate<count_ref>::const_iterator NodeTemplate<count_ref>::begin() const {
  return d_ev->begin();
}

template <bool count_ref>
inline typename NodeTemplate<count_ref>::const_iterator NodeTemplate<count_ref>::end() const {
  return d_ev->end();
}

template <bool count_ref>
inline size_t NodeTemplate<count_ref>::getNumChildren() const {
  return d_ev->d_nchildren;
}

template <bool count_ref>
template <class AttrKind>
inline typename AttrKind::value_type NodeTemplate<count_ref>::getAttribute(const AttrKind&) {
  return NodeManager::currentNM()->getAttribute(*this, AttrKind());
}

template <bool count_ref>
template <class AttrKind>
inline bool NodeTemplate<count_ref>::hasAttribute(const AttrKind&,
                               typename AttrKind::value_type* ret) {
  return NodeManager::currentNM()->hasAttribute(*this, AttrKind(), ret);
}

template <bool count_ref>
template <class AttrKind>
inline void NodeTemplate<count_ref>::setAttribute(const AttrKind&,
                               const typename AttrKind::value_type& value) {
  NodeManager::currentNM()->setAttribute(*this, AttrKind(), value);
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::s_null(&NodeValue::s_null);

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::null() {
  return s_null;
}

template <bool count_ref>
bool NodeTemplate<count_ref>::isNull() const {
  return d_ev == &NodeValue::s_null;
}

////FIXME: This function is a major hack! Should be changed ASAP
////TODO: Should use positive definition, i.e. what kinds are atomic.
template <bool count_ref>
bool NodeTemplate<count_ref>::isAtomic() const {
  switch(getKind()) {
  case NOT:
  case XOR:
  case ITE:
  case IFF:
  case IMPLIES:
  case OR:
  case AND:
    return false;
  default:
    return true;
  }
}

template <bool count_ref>
NodeTemplate<count_ref>::NodeTemplate() :
  d_ev(&NodeValue::s_null) {
  // No refcount needed
}

// FIXME: escape from type system convenient but is there a better
// way?  Nodes conceptually don't change their expr values but of
// course they do modify the refcount.  But it's nice to be able to
// support node_iterators over const NodeValue*.  So.... hm.
template <bool count_ref>
NodeTemplate<count_ref>::NodeTemplate(const NodeValue* ev)
  : d_ev(const_cast<NodeValue*>(ev)) {
  Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
  d_ev->inc();
}

template <bool count_ref>
NodeTemplate<count_ref>::NodeTemplate(const NodeTemplate<count_ref>& e) {
  Assert(e.d_ev != NULL, "Expecting a non-NULL expression value!");
  d_ev = e.d_ev;
  d_ev->inc();
}

template <bool count_ref>
NodeTemplate<count_ref>::~NodeTemplate() {
  Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
  d_ev->dec();
}

template <bool count_ref>
void NodeTemplate<count_ref>::assignNodeValue(NodeValue* ev) {
  d_ev = ev;
  d_ev->inc();
}

template <bool count_ref>
NodeTemplate<count_ref>& NodeTemplate<count_ref>::operator=(const NodeTemplate<count_ref>& e) {
  Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
  Assert(e.d_ev != NULL, "Expecting a non-NULL expression value on RHS!");
  if(EXPECT_TRUE( d_ev != e.d_ev )) {
    d_ev->dec();
    d_ev = e.d_ev;
    d_ev->inc();
  }
  return *this;
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::eqExpr(const NodeTemplate<count_ref>& right) const {
  return NodeManager::currentNM()->mkNode(EQUAL, *this, right);
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::notExpr() const {
  return NodeManager::currentNM()->mkNode(NOT, *this);
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::andExpr(const NodeTemplate<count_ref>& right) const {
  return NodeManager::currentNM()->mkNode(AND, *this, right);
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::orExpr(const NodeTemplate<count_ref>& right) const {
  return NodeManager::currentNM()->mkNode(OR, *this, right);
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::iteExpr(const NodeTemplate<count_ref>& thenpart, const NodeTemplate<count_ref>& elsepart) const {
  return NodeManager::currentNM()->mkNode(ITE, *this, thenpart, elsepart);
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::iffExpr(const NodeTemplate<count_ref>& right) const {
  return NodeManager::currentNM()->mkNode(IFF, *this, right);
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::impExpr(const NodeTemplate<count_ref>& right) const {
  return NodeManager::currentNM()->mkNode(IMPLIES, *this, right);
}

template <bool count_ref>
NodeTemplate<count_ref> NodeTemplate<count_ref>::xorExpr(const NodeTemplate<count_ref>& right) const {
  return NodeManager::currentNM()->mkNode(XOR, *this, right);
}

static void indent(std::ostream & o, int indent){
  for(int i=0; i < indent; i++)
    o << ' ';
}

template <bool count_ref>
void NodeTemplate<count_ref>::printAst(std::ostream & o, int ind) const{
  indent(o, ind);
  o << '(';
  o << getKind();
  if(getKind() == VARIABLE){
    o << ' ' << getId();

  }else if(getNumChildren() >= 1){
    for(NodeTemplate<count_ref>::iterator child = begin(); child != end(); ++child){
      o << std::endl;
      (*child).printAst(o, ind+1);
    }
    o << std::endl;
    indent(o, ind);
  }
  o << ')';
}

template <bool count_ref>
void NodeTemplate<count_ref>::debugPrint(){
  printAst(Warning(), 0);
  Warning().flush();
}


}/* CVC4 namespace */

#endif /* __CVC4__NODE_H */

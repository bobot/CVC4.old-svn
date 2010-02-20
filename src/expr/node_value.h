/*********************                                                        */
/** node_value.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** An expression node.
 **
 ** Instances of this class are generally referenced through
 ** cvc4::Node rather than by pointer; cvc4::Node maintains the
 ** reference count on NodeValue instances and
 **/

/* this must be above the check for __CVC4__EXPR__NODE_VALUE_H */
/* to resolve a circular dependency */
//#include "expr/node.h"

#ifndef __CVC4__EXPR__NODE_VALUE_H
#define __CVC4__EXPR__NODE_VALUE_H

#include "cvc4_config.h"
#include <stdint.h>
#include "kind.h"

#include <string>
#include <iterator>

namespace CVC4 {

template <bool ref_count> class NodeTemplate;
template <unsigned> class NodeBuilder;
class NodeManager;

namespace expr {

/**
 * This is an NodeValue.
 */
class NodeValue {

  /** A convenient null-valued expression value */
  static NodeValue s_null;

  /** Maximum reference count possible.  Used for sticky
   *  reference-counting.  Should be (1 << num_bits(d_rc)) - 1 */
  static const unsigned MAX_RC = 255;

  /** Number of bits assigned to the kind in the NodeValue header */
  static const unsigned KINDBITS = 8;

  /** A mask for d_kind */
  static const unsigned kindMask = (1u << KINDBITS) - 1;

  // this header fits into one 64-bit word

  /** The ID (0 is reserved for the null value) */
  unsigned d_id        : 32;

  /** The expression's reference count.  @see cvc4::Node. */
  unsigned d_rc        :  8;

  /** Kind of the expression */
  unsigned d_kind      : KINDBITS;

  /** Number of children */
  unsigned d_nchildren : 16;

  /** Variable number of child nodes */
  NodeValue *d_children[0];

  // todo add exprMgr ref in debug case

  template <bool> friend class CVC4::NodeTemplate;
  template <unsigned> friend class CVC4::NodeBuilder;
  friend class CVC4::NodeManager;

  void inc();
  void dec();

  static size_t next_id;

  /** Private default constructor for the null value. */
  NodeValue();

  /** Private default constructor for the NodeBuilder. */
  NodeValue(int);

  /** Destructor decrements the ref counts of its children */
  ~NodeValue();

  typedef NodeValue** ev_iterator;
  typedef NodeValue const* const* const_ev_iterator;

  ev_iterator ev_begin();
  ev_iterator ev_end();

  const_ev_iterator ev_begin() const;
  const_ev_iterator ev_end() const;

  class node_iterator {
    const_ev_iterator d_i;
  public:
    explicit node_iterator(const_ev_iterator i) : d_i(i) {}

    template <bool ref_count>
    inline NodeTemplate<ref_count> operator*();

    bool operator==(const node_iterator& i) {
      return d_i == i.d_i;
    }

    bool operator!=(const node_iterator& i) {
      return d_i != i.d_i;
    }

    node_iterator operator++() {
      ++d_i;
      return *this;
    }

    node_iterator operator++(int) {
      return node_iterator(d_i++);
    }

    typedef std::input_iterator_tag iterator_category;
  };
  typedef node_iterator const_node_iterator;

public:

  // Iterator support
  typedef node_iterator iterator;
  typedef node_iterator const_iterator;

  iterator begin();
  iterator end();

  const_iterator begin() const;
  const_iterator end() const;

  /**
   * Hash this expression.
   * @return the hash value of this expression.
   */
  size_t hash() const {
    size_t hash = d_kind;
    const_ev_iterator i = ev_begin();
    const_ev_iterator i_end = ev_end();
    while (i != i_end) {
      hash ^= (*i)->d_id + 0x9e3779b9 + (hash << 6) + (hash >> 2);
      ++ i;
    }
    return hash;
  }

  inline bool compareTo(const NodeValue* nv) const {
    if(d_kind != nv->d_kind)
      return false;
    if(d_nchildren != nv->d_nchildren)
      return false;
    const_ev_iterator i = ev_begin();
    const_ev_iterator j = nv->ev_begin();
    const_ev_iterator i_end = ev_end();
    while(i != i_end) {
      if ((*i) != (*j)) return false;
      ++i; ++j;
    }
    return true;
  }

  // Comparison predicate
  struct NodeValueEq {
    bool operator()(const NodeValue* nv1, const NodeValue* nv2) const {
      return nv1->compareTo(nv2);
    }
  };

  unsigned getId() const { return d_id; }
  Kind getKind() const { return dKindToKind(d_kind); }
  unsigned getNumChildren() const { return d_nchildren; }

  std::string toString() const;
  void toStream(std::ostream& out) const;

  static inline unsigned kindToDKind(Kind k) {
    return ((unsigned) k) & kindMask;
  }
  static inline Kind dKindToKind(unsigned d) {
    return (d == kindMask) ? UNDEFINED_KIND : Kind(d);
  }
};

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#include "expr/node.h"

namespace CVC4 {
namespace expr {

template <bool ref_count>
inline NodeTemplate<ref_count> NodeValue::node_iterator::operator*() {
  return NodeTemplate<ref_count>(*d_i);
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__NODE_VALUE_H */

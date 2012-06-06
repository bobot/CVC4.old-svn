/*********************                                                        */
/*! \file metakind_template.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Template for the metakind header.
 **
 ** Template for the metakind header.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__KIND__METAKIND_H
#define __CVC4__KIND__METAKIND_H

#include <iostream>

#include "expr/kind.h"
#include "util/Assert.h"

namespace CVC4 {

namespace expr {
  class NodeValue;
}/* CVC4::expr namespace */

namespace kind {
namespace metakind {

/**
 * Static, compile-time information about types T representing CVC4
 * constants:
 *
 *   typename ConstantMap<T>::OwningTheory
 *
 *     The theory in charge of constructing T when constructing Nodes
 *     with NodeManager::mkConst(T).
 *
 *   typename ConstantMap<T>::kind
 *
 *     The kind to use when constructing Nodes with
 *     NodeManager::mkConst(T).
 */
template <class T>
struct ConstantMap;

/**
 * Static, compile-time information about kinds k and what type their
 * corresponding CVC4 constants are:
 *
 *   typename ConstantMapReverse<k>::T
 *
 *     Constant type for kind k.
 */
template <Kind k>
struct ConstantMapReverse;

/**
 * Static, compile-time mapping from CONSTANT kinds to comparison
 * functors on NodeValue*.  The single element of this structure is:
 *
 *   static bool NodeValueCompare<K, pool>::compare(NodeValue* x, NodeValue* y)
 *
 *     Compares x and y, given that they are both K-kinded (and the
 *     meta-kind of K is CONSTANT).  If pool == true, one of x and y
 *     (but not both) may be a "non-inlined" NodeValue.  If pool ==
 *     false, neither x nor y may be a "non-inlined" NodeValue.
 */
template <Kind k, bool pool>
struct NodeValueConstCompare {
  inline static bool compare(const ::CVC4::expr::NodeValue* x,
                             const ::CVC4::expr::NodeValue* y);
  inline static size_t constHash(const ::CVC4::expr::NodeValue* nv);
};/* NodeValueConstCompare<k, pool> */

struct NodeValueCompare {
  template <bool pool>
  inline static bool compare(const ::CVC4::expr::NodeValue* nv1,
                             const ::CVC4::expr::NodeValue* nv2);
  inline static size_t constHash(const ::CVC4::expr::NodeValue* nv);
};/* struct NodeValueCompare */

/**
 * "metakinds" represent the "kinds" of kinds at the meta-level.
 * "metakind" is an ugly name but it's not used by client code, just
 * by the expr package, and the intent here is to keep it from
 * polluting the kind namespace.  For more documentation on what these
 * mean, see src/theory/builtin/kinds.
 */
enum MetaKind_t {
  INVALID = -1, /**< special node non-kinds like NULL_EXPR or LAST_KIND */
  VARIABLE, /**< special node kinds: no operator */
  OPERATOR, /**< operators that get "inlined" */
  PARAMETERIZED, /**< parameterized ops (like APPLYs) that carry extra data */
  CONSTANT /**< constants */
};/* enum MetaKind_t */

}/* CVC4::kind::metakind namespace */

// import MetaKind into the "CVC4::kind" namespace but keep the
// individual MetaKind constants under kind::metakind::
typedef ::CVC4::kind::metakind::MetaKind_t MetaKind;

/**
 * Get the metakind for a particular kind.
 */
static inline MetaKind metaKindOf(Kind k) {
  static const MetaKind metaKinds[] = {
    metakind::INVALID, /* UNDEFINED_KIND */
    metakind::INVALID, /* NULL_EXPR */
${metakind_kinds}
    metakind::INVALID /* LAST_KIND */
  };/* metaKinds[] */

  Assert(k >= kind::NULL_EXPR && k < kind::LAST_KIND);

  // We've asserted that k >= NULL_EXPR (which is 0), but we still
  // handle the UNDEFINED_KIND (-1) case.  If we don't, the compiler
  // emits warnings for non-assertion builds, since the check isn't done.
  return metaKinds[k + 1];
}/* metaKindOf(k) */

/**
 * Map a kind of the operator to the kind of the enclosing expression. For
 * example, since the kind of functions is just VARIABLE, it should map
 * VARIABLE to APPLY_UF.
 */
static inline Kind operatorKindToKind(Kind k) {
  switch (k) {
${metakind_operatorKinds}
  default:
    return kind::UNDEFINED_KIND;  /* LAST_KIND */
  };
}
}/* CVC4::kind namespace */

namespace expr {
  class NodeValue;
}/* CVC4::expr namespace */

namespace kind {
namespace metakind {

/* these are #defines so their sum can be #if-checked in node_value.h */
#define __CVC4__EXPR__NODE_VALUE__NBITS__REFCOUNT 8
#define __CVC4__EXPR__NODE_VALUE__NBITS__KIND 8
#define __CVC4__EXPR__NODE_VALUE__NBITS__ID 32
#define __CVC4__EXPR__NODE_VALUE__NBITS__NCHILDREN 16

static const unsigned MAX_CHILDREN =
  (1u << __CVC4__EXPR__NODE_VALUE__NBITS__NCHILDREN) - 1;

}/* CVC4::kind::metakind namespace */
}/* CVC4::kind namespace */

namespace expr {

// Comparison predicate
struct NodeValueEq {
  inline bool operator()(const NodeValue* nv1, const NodeValue* nv2) const {
    return ::CVC4::kind::metakind::NodeValueCompare::compare<false>(nv1, nv2);
  }
};

// Comparison predicate
struct NodeValuePoolEq {
  inline bool operator()(const NodeValue* nv1, const NodeValue* nv2) const {
    return ::CVC4::kind::metakind::NodeValueCompare::compare<true>(nv1, nv2);
  }
};

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#include "expr/node_value.h"

#endif /* __CVC4__KIND__METAKIND_H */

${metakind_includes}

#ifdef __CVC4__NODE_MANAGER_NEEDS_CONSTANT_MAP

namespace CVC4 {
namespace kind {
namespace metakind {

template <Kind k, bool pool>
inline bool NodeValueConstCompare<k, pool>::compare(const ::CVC4::expr::NodeValue* x,
                                                    const ::CVC4::expr::NodeValue* y) {
  typedef typename ConstantMapReverse<k>::T T;
  if(pool) {
    if(x->d_nchildren == 1) {
      Assert(y->d_nchildren == 0);
      return compare(y, x);
    } else if(y->d_nchildren == 1) {
      Assert(x->d_nchildren == 0);
      return x->getConst<T>() == *reinterpret_cast<T*>(y->d_children[0]);
    }
  }

  Assert(x->d_nchildren == 0);
  Assert(y->d_nchildren == 0);
  return x->getConst<T>() == y->getConst<T>();
}

template <Kind k, bool pool>
inline size_t NodeValueConstCompare<k, pool>::constHash(const ::CVC4::expr::NodeValue* nv) {
  typedef typename ConstantMapReverse<k>::T T;
  return nv->getConst<T>().hash();
}

${metakind_constantMaps}

template <bool pool>
inline bool NodeValueCompare::compare(const ::CVC4::expr::NodeValue* nv1,
                                      const ::CVC4::expr::NodeValue* nv2) {
  if(nv1->d_kind != nv2->d_kind) {
    return false;
  }

  if(nv1->getMetaKind() == kind::metakind::CONSTANT) {
    switch(nv1->d_kind) {
${metakind_compares}
    default:
      Unhandled(::CVC4::expr::NodeValue::dKindToKind(nv1->d_kind));
    }
  }

  if(nv1->d_nchildren != nv2->d_nchildren) {
    return false;
  }

  ::CVC4::expr::NodeValue::const_nv_iterator i = nv1->nv_begin();
  ::CVC4::expr::NodeValue::const_nv_iterator j = nv2->nv_begin();
  ::CVC4::expr::NodeValue::const_nv_iterator i_end = nv1->nv_end();

  while(i != i_end) {
    if((*i) != (*j)) {
      return false;
    }
    ++i;
    ++j;
  }

  return true;
}

inline size_t NodeValueCompare::constHash(const ::CVC4::expr::NodeValue* nv) {
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch(nv->d_kind) {
${metakind_constHashes}
  default:
    Unhandled(::CVC4::expr::NodeValue::dKindToKind(nv->d_kind));
  }
}

struct NodeValueConstPrinter {
  inline static void toStream(std::ostream& out,
                              const ::CVC4::expr::NodeValue* nv);
  inline static void toStream(std::ostream& out, TNode n);
};

inline void NodeValueConstPrinter::toStream(std::ostream& out,
                                            const ::CVC4::expr::NodeValue* nv) {
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch(nv->d_kind) {
${metakind_constPrinters}
  default:
    Unhandled(::CVC4::expr::NodeValue::dKindToKind(nv->d_kind));
  }
}

inline void NodeValueConstPrinter::toStream(std::ostream& out, TNode n) {
  toStream(out, n.d_nv);
}

/**
 * Cleanup to be performed when a NodeValue zombie is collected, and
 * it has CONSTANT metakind.  This calls the destructor for the underlying
 * C++ type representing the constant value.  See
 * NodeManager::reclaimZombies() for more information.
 *
 * This doesn't support "non-inlined" NodeValues, which shouldn't need this
 * kind of cleanup.
 */
inline void deleteNodeValueConstant(::CVC4::expr::NodeValue* nv) {
  Assert(nv->getMetaKind() == kind::metakind::CONSTANT);

  switch(nv->d_kind) {
${metakind_constDeleters}
  default:
    Unhandled(::CVC4::expr::NodeValue::dKindToKind(nv->d_kind));
  }
}

inline unsigned getLowerBoundForKind(::CVC4::Kind k) {
  static const unsigned lbs[] = {
    0, /* NULL_EXPR */
${metakind_lbchildren}

    0 /* LAST_KIND */
  };

  return lbs[k];
}

inline unsigned getUpperBoundForKind(::CVC4::Kind k) {
  static const unsigned ubs[] = {
    0, /* NULL_EXPR */
${metakind_ubchildren}

    0, /* LAST_KIND */
  };

  return ubs[k];
}

}/* CVC4::kind::metakind namespace */
}/* CVC4::kind namespace */
}/* CVC4 namespace */

#endif /* __CVC4__NODE_MANAGER_NEEDS_CONSTANT_MAP */

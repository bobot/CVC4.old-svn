/*********************                                                        */
/** node_builder.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A builder interface for Nodes.
 **
 ** The idea is to permit a flexible and efficient (in the common
 ** case) interface for building Nodes.  The general pattern of use is
 ** to create a NodeBuilder, set its kind, append children to it, then
 ** "extract" the resulting Node.  This resulting Node may be one that
 ** already exists (the NodeManager keeps a table of all Nodes in the
 ** system), or may be entirely new.
 **
 ** This implementation gets a bit hairy for a handful of reasons.  We
 ** want a user-supplied "in-line" buffer (probably on the stack, see
 ** below) to hold the children, but then the number of children must
 ** be known ahead of time.  Therefore, if this buffer is overrun, we
 ** need to heap-allocate a new buffer to hold the children.
 **
 ** Note that as children are added to a NodeBuilder, they are stored
 ** as raw pointers-to-NodeValue.  However, their reference counts are
 ** carefully maintained.
 **
 ** When the "in-line" buffer "d_inlineNv" is superceded by a
 ** heap-allocated buffer, we allocate the new buffer (a NodeValue
 ** large enough to hold more children), copy the elements to it, and
 ** mark d_inlineNv as having zero children.  We do this last bit so
 ** that we don't have to modify any child reference counts.  The new
 ** heap-allocated buffer "takes over" the reference counts of the old
 ** "in-line" buffer.  (If we didn't mark it as having zero children,
 ** the destructor may improperly decrement the children's reference
 ** counts.)
 **
 ** There are then four normal cases at the end of a NodeBuilder's
 ** life cycle:
 **
 **   0. We have a VARIABLE-kinded Node.  These are special (they have
 **      no children and are all distinct by definition).  They are
 **      really a subcase of 1(b), below.
 **   1. d_nv points to d_inlineNv: it is the backing store supplied
 **      by the user (or derived class).
 **      (a) The Node under construction already exists in the
 **          NodeManager's pool.
 **      (b) The Node under construction is NOT already in the
 **          NodeManager's pool.
 **   2. d_nv does NOT point to d_inlineNv: it is a new, larger buffer
 **      that was heap-allocated by this NodeBuilder.
 **      (a) The Node under construction already exists in the
 **          NodeManager's pool.
 **      (b) The Node under construction is NOT already in the
 **          NodeManager's pool.
 **
 ** When a Node is extracted (see the non-const version of
 ** NodeBuilderBase<>::operator Node()), we convert the NodeBuilder to
 ** a Node and make sure the reference counts are properly maintained.
 ** That means we must ensure there are no reference-counting errors
 ** among the node's children, that the children aren't re-decremented
 ** on clear() or NodeBuilder destruction, and that the returned Node
 ** wraps a NodeValue with a reference count of 1.
 **
 **   0.    If a VARIABLE, treat similarly to 1(b), except that we
 **         know there are no children (no reference counts to reason
 **         about) and we don't keep VARIABLE-kinded Nodes in the
 **         NodeManager pool.
 **
 **   1(a). Reference-counts for all children in d_inlineNv must be
 **         decremented, and the NodeBuilder must be marked as "used"
 **         and the number of children set to zero so that we don't
 **         decrement them again on destruction.  The existing
 **         NodeManager pool entry is returned.
 **
 **   1(b). A new heap-allocated NodeValue must be constructed and all
 **         settings and children from d_inlineNv copied into it.
 **         This new NodeValue is put into the NodeManager's pool.
 **         The NodeBuilder is marked as "used" and the number of
 **         children in d_inlineNv set to zero so that we don't
 **         decrement child reference counts on destruction (the child
 **         reference counts have been "taken over" by the new
 **         NodeValue).  We return a Node wrapper for this new
 **         NodeValue, which increments its reference count.
 **
 **   2(a). Reference counts for all children in d_nv must be
 **         decremented.  The NodeBuilder is marked as "used" and the
 **         heap-allocated d_nv deleted.  d_nv is repointed to
 **         d_inlineNv so that destruction of the NodeBuilder doesn't
 **         cause any problems.  The existing NodeManager pool entry
 **         is returned.
 **
 **   2(b). The heap-allocated d_nv is "cropped" to the correct size
 **         (based on the number of children it _actually_ has).  d_nv
 **         is repointed to d_inlineNv so that destruction of the
 **         NodeBuilder doesn't cause any problems, and the (old)
 **         value it had is placed into the NodeManager's pool and
 **         returned in a Node wrapper.
 **
 ** NOTE IN 1(b) AND 2(b) THAT we can NOT create Node wrapper
 ** temporary for the NodeValue in the NodeBuilderBase<>::operator
 ** Node() member function.  If we create a temporary (for example by
 ** writing Debug("builder") << Node(nv) << endl), the NodeValue will
 ** have its reference count incremented from zero to one, then
 ** decremented, which makes it eligible for collection before the
 ** builder has even returned it!  So this is a no-no.
 **
 ** For the _const_ version of NodeBuilderBase<>::operator Node(), no
 ** reference-count modifications or anything else can take place!
 ** Therefore, we have a slightly more expensive version:
 **
 **   0.    If a VARIABLE, treat similarly to 1(b), except that we
 **         know there are no children, and we don't keep
 **         VARIABLE-kinded Nodes in the NodeManager pool.
 **
 **   1(a). The existing NodeManager pool entry is returned; we leave
 **         child reference counts alone and get them at NodeBuilder
 **         destruction time.
 **
 **   1(b). A new heap-allocated NodeValue must be constructed and all
 **         settings and children from d_inlineNv copied into it.
 **         This new NodeValue is put into the NodeManager's pool.
 **         The NodeBuilder cannot be marked as "used", so we
 **         increment all child reference counts (which will be
 **         decremented to match on destruction of the NodeBuilder).
 **         We return a Node wrapper for this new NodeValue, which
 **         increments its reference count.
 **
 **   2(a). The existing NodeManager pool entry is returned; we leave
 **         child reference counts alone and get them at NodeBuilder
 **         destruction time.
 **
 **   2(b). The heap-allocated d_nv cannot be "cropped" to the correct
 **         size; we create a copy, increment child reference counts,
 **         place this copy into the NodeManager pool, and return a
 **         Node wrapper around it.  The child reference counts will
 **         be decremented to match at NodeBuilder destruction time.
 **
 ** There are also two cases when the NodeBuilder is clear()'ed:
 **
 **   1. d_nv == &d_inlineNv (NodeBuilder using the user-supplied
 **      backing store): all d_inlineNv children have their reference
 **      counts decremented, d_inlineNv.d_nchildren is set to zero,
 **      and its kind is set to UNDEFINED_KIND.
 **
 **   2. d_nv != &d_inlineNv (d_nv heap-allocated by NodeBuilder): all
 **      d_nv children have their reference counts decremented, d_nv
 **      is deallocated, and d_nv is set to &d_inlineNv.  d_inlineNv's
 **      kind is set to UNDEFINED_KIND.
 **
 ** ... destruction is similar:
 **
 **   1. d_nv == &d_inlineNv (NodeBuilder using the user-supplied
 **      backing store): all d_inlineNv children have their reference
 **      counts decremented.
 **
 **   2. d_nv != &d_inlineNv (d_nv heap-allocated by NodeBuilder): all
 **      d_nv children have their reference counts decremented, and
 **      d_nv is deallocated.
 **
 ** Regarding the backing store (typically on the stack): the file
 ** below provides three classes (two of them are templates):
 **
 **   template <class Builder> class NodeBuilderBase;
 **
 **     This is the base class for node builders.  It can not be used
 **     directly.  It contains a shared implementation but is intended
 **     to be subclassed.  Derived classes supply its "in-line" buffer.
 **
 **   class BackedNodeBuilder;
 **
 **     This is the usable form for a user-supplied-backing-store node
 **     builder.  A user can allocate a buffer large enough for a
 **     NodeValue with N children (say, on the stack), then pass a
 **     pointer to this buffer, and the parameter N, to a
 **     BackedNodeBuilder.  It will use this buffer to build its
 **     NodeValue until the number of children exceeds N; then it will
 **     allocate d_nv on the heap.
 **
 **     To ensure that the buffer is properly-sized, it is recommended
 **     to use the makeStackNodeBuilder(b, N) macro to make a
 **     BackedNodeBuilder "b" with a stack-allocated buffer large
 **     enough to hold N children.
 **
 **   template <unsigned nchild_thresh> class NodeBuilder;
 **
 **     This is the conceptually easiest form of NodeBuilder to use.
 **     The default:
 **
 **       NodeBuilder<> b;
 **
 **     gives you a backing buffer with capacity for 10 children in
 **     the same place as the NodeBuilder<> itself is allocated.  You
 **     can specify another size as a template parameter, but it must
 **     be a compile-time constant (which is why the BackedNodeBuilder
 **     creator-macro "makeStackNodeBuilder(b, N)" is sometimes
 **     preferred).
 **/

#include "cvc4_private.h"

/* strong dependency; make sure node is included first */
#include "node.h"

#ifndef __CVC4__NODE_BUILDER_H
#define __CVC4__NODE_BUILDER_H

#include <vector>
#include <cstdlib>
#include <stdint.h>

namespace CVC4 {
  static const unsigned default_nchild_thresh = 10;

  template <class Builder>
  class NodeBuilderBase;

  class NodeManager;
}/* CVC4 namespace */

#include "expr/kind.h"
#include "util/Assert.h"
#include "expr/node_value.h"
#include "util/output.h"

namespace CVC4 {

template <class Builder>
inline std::ostream& operator<<(std::ostream&, const NodeBuilderBase<Builder>&);

class AndNodeBuilder;
class OrNodeBuilder;
class PlusNodeBuilder;
class MultNodeBuilder;

/**
 * A base class for NodeBuilders.  When extending this class, use:
 *
 *   class MyExtendedNodeBuilder : public NodeBuilderBase<MyExtendedNodeBuilder> { ... };
 *
 * This ensures that certain member functions return the right
 * (derived) class type.
 *
 * There are no virtual functions here, and that should remain the
 * case!  This class is just used for sharing of implementation.  Two
 * types derive from it: BackedNodeBuilder (which allows for an
 * external buffer), and the NodeBuilder<> template, which requires
 * that you give it a compile-time constant backing-store size.
 */
template <class Builder>
class NodeBuilderBase {
protected:

  /**
   * A reference to an "in-line" stack-allocated buffer for use by the
   * NodeBuilder.
   */
  expr::NodeValue& d_inlineNv;

  /**
   * A pointer to the "current" NodeValue buffer; either &d_inlineNv
   * or a heap-allocated one if d_inlineNv wasn't big enough.
   */
  expr::NodeValue* d_nv;

  /** The NodeManager at play */
  NodeManager* d_nm;

  /**
   * The maximum number of children that can be held in this "in-line"
   * buffer.
   */
  const uint16_t d_inlineNvMaxChildren;

  /**
   * The number of children allocated in d_nv.
   */
  uint16_t d_nvMaxChildren;

  /**
   * Returns whether or not this NodeBuilder has been "used"---i.e.,
   * whether a Node has been extracted with [the non-const version of]
   * operator Node().  Internally, this state is represented by d_nv
   * pointing to NULL.
   */
  inline bool isUsed() const {
    return EXPECT_FALSE( d_nv == NULL );
  }

  /**
   * Set this NodeBuilder to the `used' state.
   */
  inline void setUsed() {
    Assert(!isUsed(), "Internal error: bad `used' state in NodeBuilder!");
    Assert(d_inlineNv.d_nchildren == 0 &&
           d_nvMaxChildren == d_inlineNvMaxChildren,
           "Internal error: bad `inline' state in NodeBuilder!");
    d_nv = NULL;
  }

  /**
   * Set this NodeBuilder to the `unused' state.  Should only be done
   * from clear().
   */
  inline void setUnused() {
    Assert(isUsed(), "Internal error: bad `used' state in NodeBuilder!");
    Assert(d_inlineNv.d_nchildren == 0 &&
           d_nvMaxChildren == d_inlineNvMaxChildren,
           "Internal error: bad `inline' state in NodeBuilder!");
    d_nv = &d_inlineNv;
  }

  /**
   * Returns true if d_nv is *not* the "in-line" one (it was
   * heap-allocated by this class).
   */
  inline bool nvIsAllocated() const {
    return EXPECT_FALSE( d_nv != &d_inlineNv ) && EXPECT_TRUE( d_nv != NULL );
  }

  /**
   * Returns true if adding a child requires (re)allocation of d_nv
   * first.
   */
  inline bool nvNeedsToBeAllocated() const {
    return EXPECT_FALSE( d_nv->d_nchildren == d_nvMaxChildren );
  }

  /**
   * (Re)allocate d_nv using a default grow factor.  Ensure that child
   * pointers are copied into the new buffer, and if the "inline"
   * NodeValue is evacuated, make sure its children won't be
   * double-decremented later (on destruction/clear).
   */
  inline void realloc() {
    realloc(d_nvMaxChildren * 2);
  }

  /**
   * (Re)allocate d_nv to a specific size.  Specify "copy" if the
   * children should be copied; if they are, and if the "inline"
   * NodeValue is evacuated, make sure its children won't be
   * double-decremented later (on destruction/clear).
   */
  void realloc(size_t toSize);

  /**
   * If d_nv needs to be (re)allocated to add an additional child, do
   * so using realloc(), which ensures child pointers are copied and
   * that the reference counts of the "inline" NodeValue won't be
   * double-decremented on destruction/clear.  Otherwise, do nothing.
   */
  inline void allocateNvIfNecessaryForAppend() {
    if(EXPECT_FALSE( nvNeedsToBeAllocated() )) {
      realloc();
    }
  }

  /**
   * Deallocate a d_nv that was heap-allocated by this class during
   * grow operations.  (Marks this NodeValue no longer allocated so
   * that double-deallocations don't occur.)
   *
   * PRECONDITION: only call this when nvIsAllocated() == true.
   * POSTCONDITION: !nvIsAllocated()
   */
  void dealloc();

  /**
   * "Purge" the "inline" children.  Decrement all their reference
   * counts and set the number of children to zero.
   *
   * PRECONDITION: only call this when nvIsAllocated() == false.
   * POSTCONDITION: d_inlineNv.d_nchildren == 0.
   */
  void decrRefCounts();

  /**
   * Trim d_nv down to the size it needs to be for the number of
   * children it has.  Used when a Node is extracted from a
   * NodeBuilder and we want the returned memory not to suffer from
   * internal fragmentation.  If d_nv was not heap-allocated by this
   * class, or is already the right size, this function does nothing.
   *
   * @throws bad_alloc if the reallocation fails
   */
  void crop() {
    if(EXPECT_FALSE( nvIsAllocated() ) &&
       EXPECT_TRUE( d_nvMaxChildren > d_nv->d_nchildren )) {
      // Ensure d_nv is not modified on allocation failure
      expr::NodeValue* newBlock = (expr::NodeValue*)
        std::realloc(d_nv,
                     sizeof(expr::NodeValue) +
                     ( sizeof(expr::NodeValue*) * (d_nvMaxChildren = d_nv->d_nchildren) ));
      if(newBlock == NULL) {
        // In this case, d_nv was NOT freed.  If we throw, the
        // deallocation should occur on destruction of the
        // NodeBuilder.
        throw std::bad_alloc();
      }
      d_nv = newBlock;
    }
  }

  Builder& collapseTo(Kind k) {
    AssertArgument(k != kind::UNDEFINED_KIND && k != kind::NULL_EXPR,
                   k, "illegal collapsing kind");

    if(getKind() != k) {
      Node n = operator Node();
      clear();
      d_nv->d_kind = expr::NodeValue::kindToDKind(k);
      return append(n);
    }
    return static_cast<Builder&>(*this);
  }

protected:

  inline NodeBuilderBase(expr::NodeValue* buf, unsigned maxChildren,
                         Kind k = kind::UNDEFINED_KIND);
  inline NodeBuilderBase(expr::NodeValue* buf, unsigned maxChildren,
                         NodeManager* nm, Kind k = kind::UNDEFINED_KIND);

private:
  // disallow copy or assignment of these base classes directly (there
  // would be no backing store!)
  NodeBuilderBase(const NodeBuilderBase& nb);
  NodeBuilderBase& operator=(const NodeBuilderBase& nb);

public:

  // Intentionally not virtual; we don't want a vtable.  Don't
  // override this in a derived class.
  inline ~NodeBuilderBase();

  typedef expr::NodeValue::iterator<true> iterator;
  typedef expr::NodeValue::iterator<true> const_iterator;

  /** Get the begin-const-iterator of this Node-under-construction. */
  inline const_iterator begin() const {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    return d_nv->begin<true>();
  }

  /** Get the end-const-iterator of this Node-under-construction. */
  inline const_iterator end() const {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    return d_nv->end<true>();
  }

  /** Get the kind of this Node-under-construction. */
  inline Kind getKind() const {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    return d_nv->getKind();
  }

  /** Get the current number of children of this Node-under-construction. */
  inline unsigned getNumChildren() const {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    return d_nv->getNumChildren();
  }

  /** Access to children of this Node-under-construction. */
  inline Node operator[](int i) const {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    Assert(i >= 0 && i < d_nv->getNumChildren(), "index out of range for NodeBuilder[]");
    return Node(d_nv->d_children[i]);
  }

  /**
   * "Reset" this node builder (optionally setting a new kind for it),
   * using the same "inline" memory as at construction time.  This
   * deallocates NodeBuilder-allocated heap memory, if it was
   * allocated, and decrements the reference counts of any currently
   * children in the NodeBuilder.
   *
   * This should leave the BackedNodeBuilder in the state it was after
   * initial construction, except for Kind, which is set to the
   * argument (if provided), or UNDEFINED_KIND.  In particular, the
   * associated NodeManager is not affected by clear().
   */
  void clear(Kind k = kind::UNDEFINED_KIND);

  // "Stream" expression constructor syntax

  /** Set the Kind of this Node-under-construction. */
  inline Builder& operator<<(const Kind& k) {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    Assert(getKind() == kind::UNDEFINED_KIND,
           "can't redefine the Kind of a NodeBuilder");
    Assert(k != kind::UNDEFINED_KIND,
           "can't define the Kind of a NodeBuilder to be UNDEFINED_KIND");
    d_nv->d_kind = expr::NodeValue::kindToDKind(k);
    return static_cast<Builder&>(*this);
  }

  /**
   * If this Node-under-construction has a Kind set, collapse it and
   * append the given Node as a child.  Otherwise, simply append.
   * FIXME: do we really want that collapse behavior?  We had agreed
   * on it but then never wrote code like that.
   */
  Builder& operator<<(TNode n) {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    /* FIXME: disable this "collapsing" for now..
    if(EXPECT_FALSE( getKind() != kind::UNDEFINED_KIND )) {
      Node n2 = operator Node();
      clear();
      append(n2);
    }*/
    return append(n);
  }

  /** Append a sequence of children to this Node-under-construction. */
  inline Builder& append(const std::vector<Node>& children) {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    return append(children.begin(), children.end());
  }

  /** Append a sequence of children to this Node-under-construction. */
  template <class Iterator>
  Builder& append(const Iterator& begin, const Iterator& end) {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    for(Iterator i = begin; i != end; ++i) {
      append(*i);
    }
    return static_cast<Builder&>(*this);
  }

  /** Append a child to this Node-under-construction. */
  Builder& append(TNode n) {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    allocateNvIfNecessaryForAppend();
    expr::NodeValue* nv = n.d_nv;
    nv->inc();
    d_nv->d_children[d_nv->d_nchildren++] = nv;
    return static_cast<Builder&>(*this);
  }

  // two versions, so we can support extraction from (const)
  // NodeBuilders which are temporaries appearing as rvalues
  operator Node();
  operator Node() const;

  inline void toStream(std::ostream& out) const {
    Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
    d_nv->toStream(out);
  }

  Builder& operator&=(TNode);
  Builder& operator|=(TNode);
  Builder& operator+=(TNode);
  Builder& operator-=(TNode);
  Builder& operator*=(TNode);

  friend class AndNodeBuilder;
  friend class OrNodeBuilder;
  friend class PlusNodeBuilder;
  friend class MultNodeBuilder;

};/* class NodeBuilderBase */

/**
 * Backing-store interface version for NodeBuilders.  To construct one
 * of these, you need to create a backing store (preferably on the
 * stack) for it to hold its "inline" NodeValue.  There's a
 * convenience macro defined below, makeStackNodeBuilder(b, N),
 * defined below to define a stack-allocated BackedNodeBuilder "b"
 * with room for N children on the stack.
 */
class BackedNodeBuilder : public NodeBuilderBase<BackedNodeBuilder> {
public:
  inline BackedNodeBuilder(expr::NodeValue* buf, unsigned maxChildren) :
    NodeBuilderBase<BackedNodeBuilder>(buf, maxChildren) {
  }

  inline BackedNodeBuilder(expr::NodeValue* buf, unsigned maxChildren, Kind k) :
    NodeBuilderBase<BackedNodeBuilder>(buf, maxChildren) {
  }

  inline BackedNodeBuilder(expr::NodeValue* buf, unsigned maxChildren, NodeManager* nm) :
    NodeBuilderBase<BackedNodeBuilder>(buf, maxChildren) {
  }

  inline BackedNodeBuilder(expr::NodeValue* buf, unsigned maxChildren, NodeManager* nm, Kind k) :
    NodeBuilderBase<BackedNodeBuilder>(buf, maxChildren) {
  }

  // we don't want a vtable, so do not declare a dtor!
  //inline ~BackedNodeBuilder();

private:
  // disallow copy or assignment (there would be no backing store!)
  BackedNodeBuilder(const BackedNodeBuilder& nb);
  BackedNodeBuilder& operator=(const BackedNodeBuilder& nb);

};/* class BackedNodeBuilder */

/**
 * Stack-allocate a BackedNodeBuilder with a stack-allocated backing
 * store of size __n.  The BackedNodeBuilder will be named __v.
 *
 * __v must be a simple name.  __n must be convertible to size_t, and
 * will be evaluated only once.  This macro may only be used where
 * declarations are permitted.
 */
#define makeStackNodeBuilder(__v, __n)                                  \
  const size_t __cvc4_backednodebuilder_nchildren__ ## __v = (__n);     \
  ::CVC4::expr::NodeValue __cvc4_backednodebuilder_buf__ ## __v[1 + (((sizeof(::CVC4::expr::NodeValue) + sizeof(::CVC4::expr::NodeValue*) + 1) / sizeof(::CVC4::expr::NodeValue*)) * __cvc4_backednodebuilder_nchildren__ ## __v)]; \
  ::CVC4::BackedNodeBuilder __v(__cvc4_backednodebuilder_buf__ ## __v, \
                                __cvc4_backednodebuilder_nchildren__ ## __v)
// IF THE ABOVE ASSERTION FAILS, write another compiler-specific
// version of makeStackNodeBuilder() that works for your compiler
// (even if it's suboptimal, ignoring its __n argument, and just
// creates a NodeBuilder<10>).


/**
 * Simple NodeBuilder interface.  This is a template that requires
 * that the number of children of the "inline"-allocated NodeValue be
 * specified as a template parameter (which means it must be a
 * compile-time constant).
 */
template <unsigned nchild_thresh = default_nchild_thresh>
class NodeBuilder : public NodeBuilderBase<NodeBuilder<nchild_thresh> > {
  // This is messy:
  // 1. This (anonymous) struct here must be a POD to avoid the
  //    compiler laying out things in a different way.
  // 2. The layout is engineered carefully.  We can't just
  //    stack-allocate enough bytes as a char[] because we break
  //    strict-aliasing rules.  The first thing in the struct is a
  //    "NodeValue" so a pointer to this struct should be safely
  //    castable to a pointer to a NodeValue (same alignment).
  struct BackingStore {
    expr::NodeValue n;
    expr::NodeValue* c[nchild_thresh];
  } d_backingStore;

  typedef NodeBuilderBase<NodeBuilder<nchild_thresh> > super;

  template <unsigned N>
  void internalCopy(const NodeBuilder<N>& nb);

public:
  inline NodeBuilder() :
    NodeBuilderBase<NodeBuilder<nchild_thresh> >
      (reinterpret_cast<expr::NodeValue*>(&d_backingStore),
       nchild_thresh) {
  }

  inline NodeBuilder(Kind k) :
    NodeBuilderBase<NodeBuilder<nchild_thresh> >
      (reinterpret_cast<expr::NodeValue*>(&d_backingStore),
       nchild_thresh,
       k) {
  }

  inline NodeBuilder(NodeManager* nm) :
    NodeBuilderBase<NodeBuilder<nchild_thresh> >
      (reinterpret_cast<expr::NodeValue*>(&d_backingStore),
       nchild_thresh,
       nm) {
  }

  inline NodeBuilder(NodeManager* nm, Kind k) :
    NodeBuilderBase<NodeBuilder<nchild_thresh> >
      (reinterpret_cast<expr::NodeValue*>(&d_backingStore),
       nchild_thresh,
       nm,
       k) {
  }

  // These implementations are identical, but we need to have both of
  // these because the templatized version isn't recognized as a
  // generalization of a copy constructor (and a default copy
  // constructor will be generated [?])
  inline NodeBuilder(const NodeBuilder& nb) :
    NodeBuilderBase<NodeBuilder<nchild_thresh> >
      (reinterpret_cast<expr::NodeValue*>(&d_backingStore),
       nchild_thresh,
       nb.d_nm,
       nb.getKind()) {
    internalCopy(nb);
  }

  // technically this is a conversion, not a copy
  template <unsigned N>
  inline NodeBuilder(const NodeBuilder<N>& nb) :
    NodeBuilderBase<NodeBuilder<nchild_thresh> >
      (reinterpret_cast<expr::NodeValue*>(&d_backingStore),
       nchild_thresh,
       nb.d_nm,
       nb.getKind()) {
    internalCopy(nb);
  }

  // we don't want a vtable, so do not declare a dtor!
  //inline ~NodeBuilder();

  // This is needed for copy constructors of different sizes to access private fields
  template <unsigned N>
  friend class NodeBuilder;

};/* class NodeBuilder<> */

// TODO: add templatized NodeTemplate<ref_count> to all above and
// below inlines for 'const [T]Node&' arguments?  Technically a lot of
// time is spent in the TNode conversion and copy constructor, but
// this should be optimized into a simple pointer copy (?)
// TODO: double-check this.

class AndNodeBuilder {
public:
  NodeBuilder<> d_eb;

  inline AndNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    d_eb.collapseTo(kind::AND);
  }

  inline AndNodeBuilder(TNode a, TNode b) : d_eb(kind::AND) {
    d_eb << a << b;
  }

  template <bool rc>
  inline AndNodeBuilder& operator&&(const NodeTemplate<rc>&);

  template <bool rc>
  inline OrNodeBuilder operator||(const NodeTemplate<rc>&);

  inline operator NodeBuilder<>() { return d_eb; }
  inline operator Node() { return d_eb; }

};/* class AndNodeBuilder */

class OrNodeBuilder {
public:
  NodeBuilder<> d_eb;

  inline OrNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    d_eb.collapseTo(kind::OR);
  }

  inline OrNodeBuilder(TNode a, TNode b) : d_eb(kind::OR) {
    d_eb << a << b;
  }

  template <bool rc>
  inline AndNodeBuilder operator&&(const NodeTemplate<rc>&);

  template <bool rc>
  inline OrNodeBuilder& operator||(const NodeTemplate<rc>&);

  inline operator NodeBuilder<>() { return d_eb; }
  inline operator Node() { return d_eb; }

};/* class OrNodeBuilder */

class PlusNodeBuilder {
public:
  NodeBuilder<> d_eb;

  inline PlusNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    d_eb.collapseTo(kind::PLUS);
  }

  inline PlusNodeBuilder(TNode a, TNode b) : d_eb(kind::PLUS) {
    d_eb << a << b;
  }

  template <bool rc>
  inline PlusNodeBuilder& operator+(const NodeTemplate<rc>&);

  template <bool rc>
  inline PlusNodeBuilder& operator-(const NodeTemplate<rc>&);

  template <bool rc>
  inline MultNodeBuilder operator*(const NodeTemplate<rc>&);

  inline operator NodeBuilder<>() { return d_eb; }
  inline operator Node() { return d_eb; }

};/* class PlusNodeBuilder */

class MultNodeBuilder {
public:
  NodeBuilder<> d_eb;

  inline MultNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    d_eb.collapseTo(kind::MULT);
  }

  inline MultNodeBuilder(TNode a, TNode b) : d_eb(kind::MULT) {
    d_eb << a << b;
  }

  template <bool rc>
  inline PlusNodeBuilder operator+(const NodeTemplate<rc>&);

  template <bool rc>
  inline PlusNodeBuilder operator-(const NodeTemplate<rc>&);

  template <bool rc>
  inline MultNodeBuilder& operator*(const NodeTemplate<rc>&);

  inline operator NodeBuilder<>() { return d_eb; }
  inline operator Node() { return d_eb; }

};/* class MultNodeBuilder */

template <class Builder>
inline Builder& NodeBuilderBase<Builder>::operator&=(TNode e) {
  return collapseTo(kind::AND).append(e);
}

template <class Builder>
inline Builder& NodeBuilderBase<Builder>::operator|=(TNode e) {
  return collapseTo(kind::OR).append(e);
}

template <class Builder>
inline Builder& NodeBuilderBase<Builder>::operator+=(TNode e) {
  return collapseTo(kind::PLUS).append(e);
}

template <class Builder>
inline Builder& NodeBuilderBase<Builder>::operator-=(TNode e) {
  return collapseTo(kind::PLUS).append(NodeManager::currentNM()->mkNode(kind::UMINUS, e));
}

template <class Builder>
inline Builder& NodeBuilderBase<Builder>::operator*=(TNode e) {
  return collapseTo(kind::MULT).append(e);
}

template <bool rc>
inline AndNodeBuilder& AndNodeBuilder::operator&&(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

template <bool rc>
inline OrNodeBuilder AndNodeBuilder::operator||(const NodeTemplate<rc>& n) {
  return OrNodeBuilder(Node(d_eb), n);
}

inline AndNodeBuilder& operator&&(AndNodeBuilder& a, const AndNodeBuilder& b) {
  return a && Node(b.d_eb);
}
inline AndNodeBuilder& operator&&(AndNodeBuilder& a, const OrNodeBuilder& b) {
  return a && Node(b.d_eb);
}
inline OrNodeBuilder operator||(AndNodeBuilder& a, const AndNodeBuilder& b) {
  return a || Node(b.d_eb);
}
inline OrNodeBuilder operator||(AndNodeBuilder& a, const OrNodeBuilder& b) {
  return a || Node(b.d_eb);
}

template <bool rc>
inline AndNodeBuilder OrNodeBuilder::operator&&(const NodeTemplate<rc>& n) {
  return AndNodeBuilder(Node(d_eb), n);
}

template <bool rc>
inline OrNodeBuilder& OrNodeBuilder::operator||(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

inline AndNodeBuilder operator&&(OrNodeBuilder& a, const AndNodeBuilder& b) {
  return a && Node(b.d_eb);
}
inline AndNodeBuilder operator&&(OrNodeBuilder& a, const OrNodeBuilder& b) {
  return a && Node(b.d_eb);
}
inline OrNodeBuilder& operator||(OrNodeBuilder& a, const AndNodeBuilder& b) {
  return a || Node(b.d_eb);
}
inline OrNodeBuilder& operator||(OrNodeBuilder& a, const OrNodeBuilder& b) {
  return a || Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder& PlusNodeBuilder::operator+(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

template <bool rc>
inline PlusNodeBuilder& PlusNodeBuilder::operator-(const NodeTemplate<rc>& n) {
  d_eb.append(NodeManager::currentNM()->mkNode(kind::UMINUS, n));
  return *this;
}

template <bool rc>
inline MultNodeBuilder PlusNodeBuilder::operator*(const NodeTemplate<rc>& n) {
  return MultNodeBuilder(Node(d_eb), n);
}

inline PlusNodeBuilder& operator+(PlusNodeBuilder& a, const PlusNodeBuilder& b) {
  return a + Node(b.d_eb);
}
inline PlusNodeBuilder& operator+(PlusNodeBuilder& a, const MultNodeBuilder& b) {
  return a + Node(b.d_eb);
}
inline PlusNodeBuilder& operator-(PlusNodeBuilder&a, const PlusNodeBuilder& b) {
  return a - Node(b.d_eb);
}
inline PlusNodeBuilder& operator-(PlusNodeBuilder& a, const MultNodeBuilder& b) {
  return a - Node(b.d_eb);
}
inline MultNodeBuilder operator*(PlusNodeBuilder& a, const PlusNodeBuilder& b) {
  return a * Node(b.d_eb);
}
inline MultNodeBuilder operator*(PlusNodeBuilder& a, const MultNodeBuilder& b) {
  return a * Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder MultNodeBuilder::operator+(const NodeTemplate<rc>& n) {
  return PlusNodeBuilder(Node(d_eb), n);
}

template <bool rc>
inline PlusNodeBuilder MultNodeBuilder::operator-(const NodeTemplate<rc>& n) {
  return PlusNodeBuilder(Node(d_eb), NodeManager::currentNM()->mkNode(kind::UMINUS, n));
}

template <bool rc>
inline MultNodeBuilder& MultNodeBuilder::operator*(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

inline PlusNodeBuilder operator+(MultNodeBuilder& a, const PlusNodeBuilder& b) {
  return a + Node(b.d_eb);
}
inline PlusNodeBuilder operator+(MultNodeBuilder& a, const MultNodeBuilder& b) {
  return a + Node(b.d_eb);
}
inline PlusNodeBuilder operator-(MultNodeBuilder& a, const PlusNodeBuilder& b) {
  return a - Node(b.d_eb);
}
inline PlusNodeBuilder operator-(MultNodeBuilder& a, const MultNodeBuilder& b) {
  return a - Node(b.d_eb);
}
inline MultNodeBuilder& operator*(MultNodeBuilder& a, const PlusNodeBuilder& b) {
  return a * Node(b.d_eb);
}
inline MultNodeBuilder& operator*(MultNodeBuilder& a, const MultNodeBuilder& b) {
  return a * Node(b.d_eb);
}

template <bool rc1, bool rc2>
inline AndNodeBuilder operator&&(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return AndNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline OrNodeBuilder operator||(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return OrNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline PlusNodeBuilder operator+(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return PlusNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline PlusNodeBuilder operator-(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return PlusNodeBuilder(a, NodeManager::currentNM()->mkNode(kind::UMINUS, b));
}

template <bool rc1, bool rc2>
inline MultNodeBuilder operator*(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return MultNodeBuilder(a, b);
}

template <bool rc>
inline AndNodeBuilder operator&&(const NodeTemplate<rc>& a, const AndNodeBuilder& b) {
  return a && Node(b.d_eb);
}

template <bool rc>
inline AndNodeBuilder operator&&(const NodeTemplate<rc>& a, const OrNodeBuilder& b) {
  return a && Node(b.d_eb);
}

template <bool rc>
inline OrNodeBuilder operator||(const NodeTemplate<rc>& a, const AndNodeBuilder& b) {
  return a || Node(b.d_eb);
}

template <bool rc>
inline OrNodeBuilder operator||(const NodeTemplate<rc>& a, const OrNodeBuilder& b) {
  return a || Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder operator+(const NodeTemplate<rc>& a, const PlusNodeBuilder& b) {
  return a + Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder operator+(const NodeTemplate<rc>& a, const MultNodeBuilder& b) {
  return a + Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder operator-(const NodeTemplate<rc>& a, const PlusNodeBuilder& b) {
  return a - Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder operator-(const NodeTemplate<rc>& a, const MultNodeBuilder& b) {
  return a - Node(b.d_eb);
}

template <bool rc>
inline MultNodeBuilder operator*(const NodeTemplate<rc>& a, const PlusNodeBuilder& b) {
  return a * Node(b.d_eb);
}

template <bool rc>
inline MultNodeBuilder operator*(const NodeTemplate<rc>& a, const MultNodeBuilder& b) {
  return a * Node(b.d_eb);
}

template <bool rc>
inline NodeTemplate<true> operator-(const NodeTemplate<rc>& a) {
  return NodeManager::currentNM()->mkNode(kind::UMINUS, a);
}

}/* CVC4 namespace */

#include "expr/node.h"
#include "expr/node_manager.h"

namespace CVC4 {

template <class Builder>
inline NodeBuilderBase<Builder>::NodeBuilderBase(expr::NodeValue* buf, unsigned maxChildren, Kind k) :
  d_inlineNv(*buf),
  d_nv(&d_inlineNv),
  d_nm(NodeManager::currentNM()),
  d_inlineNvMaxChildren(maxChildren),
  d_nvMaxChildren(maxChildren) {

  d_inlineNv.d_id = 0;
  d_inlineNv.d_rc = 0;
  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
  d_inlineNv.d_nchildren = 0;
}

template <class Builder>
inline NodeBuilderBase<Builder>::NodeBuilderBase(expr::NodeValue* buf, unsigned maxChildren, NodeManager* nm, Kind k) :
  d_inlineNv(*buf),
  d_nv(&d_inlineNv),
  d_nm(nm),
  d_inlineNvMaxChildren(maxChildren),
  d_nvMaxChildren(maxChildren) {

  d_inlineNv.d_id = 0;
  d_inlineNv.d_rc = 0;
  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
  d_inlineNv.d_nchildren = 0;
}

template <class Builder>
inline NodeBuilderBase<Builder>::~NodeBuilderBase() {
  if(EXPECT_FALSE( nvIsAllocated() )) {
    dealloc();
  } else if(EXPECT_FALSE( !isUsed() )) {
    decrRefCounts();
  }
}

template <class Builder>
void NodeBuilderBase<Builder>::clear(Kind k) {
  if(EXPECT_FALSE( nvIsAllocated() )) {
    dealloc();
  } else if(EXPECT_FALSE( !isUsed() )) {
    decrRefCounts();
  } else {
    setUnused();
  }

  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
  for(expr::NodeValue::nv_iterator i = d_inlineNv.nv_begin();
      i != d_inlineNv.nv_end();
      ++i) {
    (*i)->dec();
  }
  d_inlineNv.d_nchildren = 0;
}

template <class Builder>
void NodeBuilderBase<Builder>::realloc(size_t toSize) {
  Assert( toSize > d_nvMaxChildren,
          "attempt to realloc() a NodeBuilder to a smaller/equal size!" );

  if(EXPECT_FALSE( nvIsAllocated() )) {
    // Ensure d_nv is not modified on allocation failure
    expr::NodeValue* newBlock = (expr::NodeValue*)
      std::realloc(d_nv, sizeof(expr::NodeValue) +
                   ( sizeof(expr::NodeValue*) * (d_nvMaxChildren = toSize) ));
    if(newBlock == NULL) {
      // In this case, d_nv was NOT freed.  If we throw, the
      // deallocation should occur on destruction of the NodeBuilder.
      throw std::bad_alloc();
    }
    // Here, the copy (between two heap-allocated buffers) has already
    // been done for us by the std::realloc().
    d_nv = newBlock;
  } else {
    // Ensure d_nv is not modified on allocation failure
    expr::NodeValue* newBlock = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue) +
                  ( sizeof(expr::NodeValue*) * (d_nvMaxChildren = toSize) ));
    if(newBlock == NULL) {
      throw std::bad_alloc();
    }

    d_nv = newBlock;
    d_nv->d_id = 0;
    d_nv->d_rc = 0;
    d_nv->d_kind = d_inlineNv.d_kind;
    d_nv->d_nchildren = d_inlineNv.d_nchildren;

    std::copy(d_inlineNv.d_children,
              d_inlineNv.d_children + d_inlineNv.d_nchildren,
              d_nv->d_children);

    // ensure "inline" children don't get decremented in dtor
    d_inlineNv.d_nchildren = 0;
  }
}

template <class Builder>
void NodeBuilderBase<Builder>::dealloc() {
  Assert( nvIsAllocated(),
          "Internal error: NodeBuilder: dealloc() called without a "
          "private NodeBuilder-allocated buffer" );

  for(expr::NodeValue::nv_iterator i = d_nv->nv_begin();
      i != d_nv->nv_end();
      ++i) {
    (*i)->dec();
  }

  free(d_nv);
  d_nv = &d_inlineNv;
  d_nvMaxChildren = d_inlineNvMaxChildren;
}

template <class Builder>
void NodeBuilderBase<Builder>::decrRefCounts() {
  Assert( !nvIsAllocated(),
          "Internal error: NodeBuilder: decrRefCounts() called with a "
          "private NodeBuilder-allocated buffer" );

  for(expr::NodeValue::nv_iterator i = d_inlineNv.nv_begin();
      i != d_inlineNv.nv_end();
      ++i) {
    (*i)->dec();
  }

  d_inlineNv.d_nchildren = 0;
}

// NON-CONST VERSION OF NODE EXTRACTOR
template <class Builder>
NodeBuilderBase<Builder>::operator Node() {
  Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
  Assert(getKind() != kind::UNDEFINED_KIND,
         "Can't make an expression of an undefined kind!");

  // NOTE: The comments in this function refer to the cases in the
  // file comments at the top of this file.

  // Case 0: If a VARIABLE
  if(getKind() == kind::VARIABLE) {
    /* 0. If a VARIABLE, treat similarly to 1(b), except that we know
     * there are no children (no reference counts to reason about)
     * and we don't keep VARIABLE-kinded Nodes in the NodeManager
     * pool. */

    Assert( ! nvIsAllocated(),
            "internal NodeBuilder error: "
            "VARIABLE-kinded NodeBuilder is heap-allocated !?" );
    Assert( d_inlineNv.d_nchildren == 0,
            "improperly-formed VARIABLE-kinded NodeBuilder: "
            "no children permitted" );

    // we have to copy the inline NodeValue out
    expr::NodeValue* nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue));
    if(nv == NULL) {
      throw std::bad_alloc();
    }
    // there are no children, so we don't have to worry about
    // reference counts in this case.
    nv->d_nchildren = 0;
    nv->d_kind = expr::NodeValue::kindToDKind(kind::VARIABLE);
    nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
    nv->d_rc = 0;
    setUsed();
    Debug("gc") << "creating node value " << nv
                << " [" << nv->d_id << "]: " << nv->toString() << "\n";
    return Node(nv);
  }

  // Implementation differs depending on whether the NodeValue was
  // malloc'ed or not and whether or not it's in the already-been-seen
  // NodeManager pool of Nodes.  See implementation notes at the top
  // of this file.

  if(EXPECT_TRUE( ! nvIsAllocated() )) {
    /** Case 1.  d_nv points to d_inlineNv: it is the backing store
     ** supplied by the user (or derived class) **/

    // Lookup the expression value in the pool we already have
    expr::NodeValue* nv = d_nm->poolLookup(&d_inlineNv);
    if(nv != NULL) {
      /* Subcase (a): The Node under construction already exists in
       * the NodeManager's pool. */

      /* 1(a). Reference-counts for all children in d_inlineNv must be
       * decremented, and the NodeBuilder must be marked as "used" and
       * the number of children set to zero so that we don't decrement
       * them again on destruction.  The existing NodeManager pool
       * entry is returned.
       */
      decrRefCounts();
      d_inlineNv.d_nchildren = 0;
      setUsed();
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      return Node(nv);
    } else {
      /* Subcase (b): The Node under construction is NOT already in
       * the NodeManager's pool. */

      /* 1(b). A new heap-allocated NodeValue must be constructed and
       * all settings and children from d_inlineNv copied into it.
       * This new NodeValue is put into the NodeManager's pool.  The
       * NodeBuilder is marked as "used" and the number of children in
       * d_inlineNv set to zero so that we don't decrement child
       * reference counts on destruction (the child reference counts
       * have been "taken over" by the new NodeValue).  We return a
       * Node wrapper for this new NodeValue, which increments its
       * reference count. */

      // create the canonical expression value for this node
      nv = (expr::NodeValue*)
        std::malloc(sizeof(expr::NodeValue) +
                    ( sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren ));
      if(nv == NULL) {
        throw std::bad_alloc();
      }
      nv->d_nchildren = d_inlineNv.d_nchildren;
      nv->d_kind = d_inlineNv.d_kind;
      nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
      nv->d_rc = 0;

      std::copy(d_inlineNv.d_children,
                d_inlineNv.d_children + d_inlineNv.d_nchildren,
                nv->d_children);

      d_inlineNv.d_nchildren = 0;
      setUsed();

      d_nm->poolInsert(nv);
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      return Node(nv);
    }
  } else {
    /** Case 2. d_nv does NOT point to d_inlineNv: it is a new, larger
     ** buffer that was heap-allocated by this NodeBuilder. **/

    // Lookup the expression value in the pool we already have (with insert)
    expr::NodeValue* nv = d_nm->poolLookup(d_nv);
    // If something else is there, we reuse it
    if(nv != NULL) {
      /* Subcase (a) The Node under construction already exists in the
       * NodeManager's pool. */

      /* 2(a). Reference counts for all children in d_nv must be
       * decremented.  The NodeBuilder is marked as "used" and the
       * heap-allocated d_nv deleted.  d_nv is repointed to d_inlineNv
       * so that destruction of the NodeBuilder doesn't cause any
       * problems.  The existing NodeManager pool entry is
       * returned. */

      dealloc();
      setUsed();
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      return Node(nv);
    } else {
      /* Subcase (b) The Node under construction is NOT already in the
       * NodeManager's pool. */

      /* 2(b). The heap-allocated d_nv is "cropped" to the correct
       * size (based on the number of children it _actually_ has).
       * d_nv is repointed to d_inlineNv so that destruction of the
       * NodeBuilder doesn't cause any problems, and the (old) value
       * it had is placed into the NodeManager's pool and returned in
       * a Node wrapper. */

      crop();
      nv = d_nv;
      nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
      d_nv = &d_inlineNv;
      d_nvMaxChildren = d_inlineNvMaxChildren;
      setUsed();
      d_nm->poolInsert(nv);
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      return Node(nv);
    }
  }
}

// CONST VERSION OF NODE EXTRACTOR
template <class Builder>
NodeBuilderBase<Builder>::operator Node() const {
  Assert(!isUsed(), "NodeBuilder is one-shot only; attempt to access it after conversion");
  Assert(getKind() != kind::UNDEFINED_KIND,
         "Can't make an expression of an undefined kind!");

  // NOTE: The comments in this function refer to the cases in the
  // file comments at the top of this file.

  // Case 0: If a VARIABLE
  if(getKind() == kind::VARIABLE) {
    /* 0. If a VARIABLE, treat similarly to 1(b), except that we know
     * there are no children, and we don't keep VARIABLE-kinded Nodes
     * in the NodeManager pool. */

    Assert( ! nvIsAllocated(),
            "internal NodeBuilder error: "
            "VARIABLE-kinded NodeBuilder is heap-allocated !?" );
    Assert( d_inlineNv.d_nchildren == 0,
            "improperly-formed VARIABLE-kinded NodeBuilder: "
            "no children permitted" );

    // we have to copy the inline NodeValue out
    expr::NodeValue* nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue));
    if(nv == NULL) {
      throw std::bad_alloc();
    }
    // there are no children, so we don't have to worry about
    // reference counts in this case.
    nv->d_nchildren = 0;
    nv->d_kind = expr::NodeValue::kindToDKind(kind::VARIABLE);
    nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
    nv->d_rc = 0;
    Debug("gc") << "creating node value " << nv
                << " [" << nv->d_id << "]: " << nv->toString() << "\n";
    return Node(nv);
  }

  // Implementation differs depending on whether the NodeValue was
  // malloc'ed or not and whether or not it's in the already-been-seen
  // NodeManager pool of Nodes.  See implementation notes at the top
  // of this file.

  if(EXPECT_TRUE( ! nvIsAllocated() )) {
    /** Case 1.  d_nv points to d_inlineNv: it is the backing store
     ** supplied by the user (or derived class) **/

    // Lookup the expression value in the pool we already have
    expr::NodeValue* nv = d_nm->poolLookup(&d_inlineNv);
    if(nv != NULL) {
      /* Subcase (a): The Node under construction already exists in
       * the NodeManager's pool. */

      /* 1(a). The existing NodeManager pool entry is returned; we
       * leave child reference counts alone and get them at
       * NodeBuilder destruction time. */

      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      return Node(nv);
    } else {
      /* Subcase (b): The Node under construction is NOT already in
       * the NodeManager's pool. */

      /* 1(b). A new heap-allocated NodeValue must be constructed and
       * all settings and children from d_inlineNv copied into it.
       * This new NodeValue is put into the NodeManager's pool.  The
       * NodeBuilder cannot be marked as "used", so we increment all
       * child reference counts (which will be decremented to match on
       * destruction of the NodeBuilder).  We return a Node wrapper
       * for this new NodeValue, which increments its reference
       * count. */

      // create the canonical expression value for this node
      nv = (expr::NodeValue*)
        std::malloc(sizeof(expr::NodeValue) +
                    ( sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren ));
      if(nv == NULL) {
        throw std::bad_alloc();
      }
      nv->d_nchildren = d_inlineNv.d_nchildren;
      nv->d_kind = d_inlineNv.d_kind;
      nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
      nv->d_rc = 0;

      std::copy(d_inlineNv.d_children,
                d_inlineNv.d_children + d_inlineNv.d_nchildren,
                nv->d_children);

      for(expr::NodeValue::nv_iterator i = nv->nv_begin();
          i != nv->nv_end();
          ++i) {
        (*i)->inc();
      }

      d_nm->poolInsert(nv);
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      return Node(nv);
    }
  } else {
    /** Case 2. d_nv does NOT point to d_inlineNv: it is a new, larger
     ** buffer that was heap-allocated by this NodeBuilder. **/

    // Lookup the expression value in the pool we already have (with insert)
    expr::NodeValue* nv = d_nm->poolLookup(d_nv);
    // If something else is there, we reuse it
    if(nv != NULL) {
      /* Subcase (a) The Node under construction already exists in the
       * NodeManager's pool. */

      /* 2(a). The existing NodeManager pool entry is returned; we
       * leave child reference counts alone and get them at
       * NodeBuilder destruction time. */

      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      return Node(nv);
    } else {
      /* Subcase (b) The Node under construction is NOT already in the
       * NodeManager's pool. */

      /* 2(b). The heap-allocated d_nv cannot be "cropped" to the
       * correct size; we create a copy, increment child reference
       * counts, place this copy into the NodeManager pool, and return
       * a Node wrapper around it.  The child reference counts will be
       * decremented to match at NodeBuilder destruction time. */

      // create the canonical expression value for this node
      nv = (expr::NodeValue*)
        std::malloc(sizeof(expr::NodeValue) +
                    ( sizeof(expr::NodeValue*) * d_nv->d_nchildren ));
      if(nv == NULL) {
        throw std::bad_alloc();
      }
      nv->d_nchildren = d_nv->d_nchildren;
      nv->d_kind = d_nv->d_kind;
      nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
      nv->d_rc = 0;

      std::copy(d_nv->d_children,
                d_nv->d_children + d_nv->d_nchildren,
                nv->d_children);

      for(expr::NodeValue::nv_iterator i = nv->nv_begin();
          i != nv->nv_end();
          ++i) {
        (*i)->inc();
      }

      d_nm->poolInsert(nv);
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      return Node(nv);
    }
  }
}

template <unsigned nchild_thresh>
template <unsigned N>
void NodeBuilder<nchild_thresh>::internalCopy(const NodeBuilder<N>& nb) {
  if(nb.isUsed()) {
    super::setUsed();
    return;
  }

  if(nb.d_nvMaxChildren > super::d_nvMaxChildren) {
    super::realloc(nb.d_nvMaxChildren);
  }

  std::copy(nb.d_nv->nv_begin(),
            nb.d_nv->nv_end(),
            super::d_nv->nv_begin());

  super::d_nv->d_nchildren = nb.d_nv->d_nchildren;

  for(expr::NodeValue::nv_iterator i = super::d_nv->nv_begin();
      i != super::d_nv->nv_end();
      ++i) {
    (*i)->inc();
  }
}

template <class Builder>
inline std::ostream& operator<<(std::ostream& out,
                                const NodeBuilderBase<Builder>& b) {
  b.toStream(out);
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__NODE_BUILDER_H */

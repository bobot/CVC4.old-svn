/*********************                                                        */
/*! \file cdcirclist.h
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
 ** \brief Context-dependent circular list class
 **
 ** Context-dependent circular list class.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDCIRCLIST_H
#define __CVC4__CONTEXT__CDCIRCLIST_H

#include <iterator>
#include <memory>
#include <string>
#include <sstream>

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdcirclist_forward.h"
#include "context/cdo.h"
#include "util/Assert.h"

namespace CVC4 {
namespace context {

/**
 * Class representing a single link in a CDCircList<>.
 *
 * The underlying T object is immutable, only the structure of the
 * list is mutable, so only that's backtracked.
 */
template <class T, class AllocatorT>
class CDCircElement {
  typedef CDCircElement<T, AllocatorT> elt_t;
  CDO<elt_t*> d_next;
  CDO<elt_t*> d_prev;
  const T d_t;
  friend class CDCircList<T, AllocatorT>;
public:
  CDCircElement(Context* context, const T& t,
                elt_t* next = NULL, elt_t* prev = NULL) :
    d_t(t),
    d_next(context, next),
    d_prev(context, prev) {
  }

  CDO<elt_t*>& next() { return d_next; }
  CDO<elt_t*>& prev() { return d_prev; }
  elt_t* next() const { return d_next; }
  elt_t* prev() const { return d_prev; }
  T element() const { return d_t; }
};/* class CDCircElement<> */


/**
 * Generic context-dependent circular list.  Items themselves are not
 * context dependent, only the forward and backward links.  This
 * allows two lists to be spliced together in constant time (see
 * concat()).  The list *structure* is mutable (things can be spliced
 * in, removed, added, the list can be cleared, etc.) in a
 * context-dependent manner, but the list items are immutable.  To
 * replace an item A in the list with B, A must be removed and
 * B added in the same location.
 */
template <class T, class AllocatorT>
class CDCircList : public ContextObj {
public:

  /** List carrier element type */
  typedef CDCircElement<T, AllocatorT> elt_t;
  /** The value type with which this CDCircList<> was instantiated. */
  typedef T value_type;
  /** The allocator type with which this CDCircList<> was instantiated. */
  typedef AllocatorT Allocator;

private:

  /** Head element of the circular list */
  CDO<elt_t*> d_head;
  /** The context with which we're associated */
  Context* d_context;
  /** Our allocator */
  Allocator d_allocator;

public:

  CDCircList(Context* context, const Allocator& alloc = Allocator()) :
    ContextObj(context),
    d_head(context, NULL),
    d_context(context),
    d_allocator(alloc) {
  }

  ~CDCircList() throw(AssertionException) {
    // by context contract, call destroy() here
    destroy();
  }

  void clear() {
    d_head = NULL;
  }

  bool empty() const {
    return d_head == NULL;
  }

  CDO<elt_t*>& head() {
    return d_head;
  }

  CDO<elt_t*>& tail() {
    return empty() ? d_head : d_head->d_prev;
  }

  T front() const {
    Assert(! empty());
    return head()->element();
  }

  T back() const {
    Assert(! empty());
    return tail()->element();
  }

  void append(const T& t) {
    // FIXME LEAK! (should alloc in CMM, no?)
    elt_t* x = d_allocator.allocate(1);
    if(empty()) {
      new(x) elt_t(d_context, x, x, t);
      d_head = x;
    } else {
      new(x) elt_t(d_context, d_head->d_prev, d_head, t);
      d_head->d_prev = x;
    }
  }

  /**
   * Concatenate two lists.  This modifies both: afterward, the two
   * lists might have different heads, but they will have the same
   * elements in the same (circular) order.
   */
  void concat(CDCircList<T, AllocatorT>& l) {
    // splice together the two circular lists
    tail()->next() = l.head();
    l.head()->prev() = tail();
    l.tail()->next() = head();
    head()->prev() = l.tail();
  }

private:

  // do not permit copy/assignment
  CDCircList(const CDCircList<T, AllocatorT>&) CVC4_UNUSED;
  CDCircList<T, AllocatorT>& operator=(const CDCircList<T, AllocatorT>&) CVC4_UNUSED;

  /** Check internal structure and invariants of the list */
  void debugCheck() const {
    elt_t* p = d_head;
    if(p == NULL) {
      // empty list
      return;
    }
    do {
      elt_t* p_last = p;
      p = p.d_next;
      Assert(p.d_prev == p_last);
      Assert(p != NULL);
    } while(p != d_head);
  }

  // Nothing to save; the elements take care of themselves
  virtual ContextObj* save(ContextMemoryManager* pCMM) {
    Unreachable();
  }

  // Similarly, nothing to restore
  virtual void restore(ContextObj* data) {
    Unreachable();
  }

};/* class CDCircList<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDCIRCLIST_H */

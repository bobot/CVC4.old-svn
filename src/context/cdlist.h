/*********************                                                        */
/*! \file cdlist.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): barrett, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Context-dependent list class.
 **
 ** Context-dependent list class.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDLIST_H
#define __CVC4__CONTEXT__CDLIST_H

#include "context/context.h"
#include "util/Assert.h"

#include <memory>
#include <string>

namespace CVC4 {
namespace context {

/**
 * Generic context-dependent dynamic array.  Note that for efficiency, this
 * implementation makes the following assumptions:
 * 1. Over time, objects are only added to the list.  Objects are only
 *    removed when a pop restores the list to a previous state.
 * 2. T objects can safely be copied using their copy constructor,
 *    operator=, and memcpy.
 */
template <class T, class Allocator = std::allocator<T>, class ListHead = T*>
class CDList : public ContextObj {
  /**
   * d_list is a dynamic array of objects of type T.
   */
  ListHead d_list;

  /**
   * Whether to call the destructor when items are popped from the
   * list.  True by default, but can be set to false by setting the
   * second argument in the constructor to false.
   */
  bool d_callDestructor;

  /**
   * Number of objects in d_list
   */
  unsigned d_size;

  /**
   * Allocated size of d_list.
   */
  size_t d_sizeAlloc;

  /**
   * Our allocator.
   */
  Allocator d_allocator;

protected:

  /**
   * Implementation of mandatory ContextObj method save: simply copies the
   * current size to a copy using the copy constructor (the pointer and the
   * allocated size are *not* copied as they are not restored on a pop).
   * The saved information is allocated using the ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    return new(pCMM) CDList<T, Allocator, ListHead>(*this);
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply restores the
   * previous size.  Note that the list pointer and the allocated size are not
   * changed.
   */
  void restore(ContextObj* data) {
    if(d_callDestructor) {
      unsigned size = ((CDList<T, Allocator, ListHead>*)data)->d_size;
      while(d_size != size) {
        --d_size;
        d_list[d_size].~T();
      }
    } else {
      d_size = ((CDList<T, Allocator, ListHead>*)data)->d_size;
    }
  }

private:

  /**
   * Private copy constructor used only by save above.  d_list and d_sizeAlloc
   * are not copied: only the base class information and d_size are needed in
   * restore.
   */
  CDList(const CDList<T, Allocator, ListHead>& l) :
    ContextObj(l),
    d_list(NULL),
    d_callDestructor(l.d_callDestructor),
    d_size(l.d_size),
    d_sizeAlloc(0),
    d_allocator(l.d_allocator) {
  }

  /**
   * Reallocate the array with more space.
   * Throws bad_alloc if memory allocation fails.
   */
  void grow() {
    if(d_list == NULL) {
      // Allocate an initial list if one does not yet exist
      d_sizeAlloc = 10;
      Debug("cdlist") << "initial grow of cdlist " << this << " to " << d_sizeAlloc << std::endl;
      d_list = (T*) d_allocator.allocate(d_sizeAlloc);
      if(d_list == NULL) {
        throw std::bad_alloc();
      }
    } else {
      // Allocate a new array with double the size
      size_t newSize = d_sizeAlloc * 2;
      Debug("cdlist") << "2x grow of cdlist " << this << " to " << newSize << std::endl;
      T* newList = d_allocator.allocate(newSize);
      if(newList == NULL) {
        throw std::bad_alloc();
      }
      std::memcpy(newList, d_list, sizeof(T) * d_sizeAlloc);
      d_allocator.deallocate(d_list, d_sizeAlloc);
      d_list = newList;
      d_sizeAlloc = newSize;
    }
  }

public:

  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDList(Context* context, bool callDestructor = true, const Allocator& alloc = Allocator()) :
    ContextObj(context),
    d_list(NULL),
    d_callDestructor(callDestructor),
    d_size(0),
    d_sizeAlloc(0),
    d_allocator(alloc) {
  }

  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDList(bool allocatedInCMM, Context* context, bool callDestructor = true, const Allocator& alloc = Allocator()) :
    ContextObj(allocatedInCMM, context),
    d_list(NULL),
    d_callDestructor(callDestructor),
    d_size(0),
    d_sizeAlloc(0),
    d_allocator(alloc) {
  }

  /**
   * Destructor: delete the list
   */
  ~CDList() throw(AssertionException) {
    destroy();

    if(d_callDestructor) {
      for(unsigned i = 0; i < d_size; ++i) {
        d_list[i].~T();
      }
    }

    d_allocator.deallocate(d_list, d_sizeAlloc);
  }

  /**
   * Return the current size of (i.e. valid number of objects in) the list
   */
  unsigned size() const {
    return d_size;
  }

  /**
   * Return true iff there are no valid objects in the list.
   */
  bool empty() const {
    return d_size == 0;
  }

  /**
   * Add an item to the end of the list.
   */
  void push_back(const T& data) {
    makeCurrent();

    if(d_size == d_sizeAlloc) {
      grow();
    }

    ::new((void*)(d_list + d_size)) T(data);
    ++d_size;
  }

  /**
   * Access to the ith item in the list.
   */
  const T& operator[](unsigned i) const {
    Assert(i < d_size, "index out of bounds in CDList::operator[]");
    return d_list[i];
  }

  /**
   * Returns the most recent item added to the list.
   */
  const T& back() const {
    Assert(d_size > 0, "CDList::back() called on empty list");
    return d_list[d_size - 1];
  }

  /**
   * Iterator for CDList class.  It has to be const because we don't allow
   * items in the list to be changed.  It's a straightforward wrapper around a
   * pointer.  Note that for efficiency, we implement only prefix increment and
   * decrement.  Also note that it's OK to create an iterator from an empty,
   * uninitialized list, as begin() and end() will have the same value (NULL).
   */
  class const_iterator {
    T const* d_it;

    const_iterator(T const* it) : d_it(it) {}

    friend class CDList<T, Allocator, ListHead>;

  public:

    const_iterator() : d_it(NULL) {}

    inline bool operator==(const const_iterator& i) const {
      return d_it == i.d_it;
    }

    inline bool operator!=(const const_iterator& i) const {
      return d_it != i.d_it;
    }

    inline const T& operator*() const {
      return *d_it;
    }

    /** Prefix increment */
    const_iterator& operator++() {
      ++d_it;
      return *this;
    }

    /** Prefix decrement */
    const_iterator& operator--() { --d_it; return *this; }

    // Postfix operations on iterators: requires a Proxy object to
    // hold the intermediate value for dereferencing
    class Proxy {
      const T* d_t;

    public:

      Proxy(const T& p): d_t(&p) {}

      T& operator*() {
        return *d_t;
      }
    };/* class CDList<>::const_iterator::Proxy */

    /** Postfix increment: returns Proxy with the old value. */
    Proxy operator++(int) {
      Proxy e(*(*this));
      ++(*this);
      return e;
    }

    /** Postfix decrement: returns Proxy with the old value. */
    Proxy operator--(int) {
      Proxy e(*(*this));
      --(*this);
      return e;
    }

  };/* class CDList<>::const_iterator */

  /**
   * Returns an iterator pointing to the first item in the list.
   */
  const_iterator begin() const {
    return const_iterator(static_cast<T const*>(d_list));
  }

  /**
   * Returns an iterator pointing one past the last item in the list.
   */
  const_iterator end() const {
    return const_iterator(static_cast<T const*>(d_list) + d_size);
  }

};/* class CDList */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDLIST_H */

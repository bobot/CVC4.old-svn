/*********************                                                        */
/*! \file cdlist_context_memory.h
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
 ** \brief Context-dependent list class specialized for use in .
 **
 ** Context-dependent list class.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDLIST_CONTEXT_MEMORY_H
#define __CVC4__CONTEXT__CDLIST_CONTEXT_MEMORY_H

#ifndef __CVC4__CONTEXT__CDLIST_H_INCLUDING_CDLIST_CONTEX_MEMORY_H
#  error cdlist_context_memory.h should only be included from cdlist.h
#endif /* __CVC4__CONTEXT__CDLIST_H_INCLUDING_CDLIST_CONTEX_MEMORY_H */

namespace CVC4 {
namespace context {

/**
 * Generic context-dependent dynamic array.  Like the usual CDList<>,
 * but allocates all memory from context memory.  Elements are kept in
 * cascading "list segments."  Access to elements is not O(1) but
 * O(log n).  As with CDList<>, update is not permitted, only
 * appending to the end of the list.
 */
template <class T>
class CDList<T, ContextMemoryAllocator<T> > : public ContextObj {
protected:

  typedef ContextMemoryAllocator<T> Allocator;

  /**
   * ListSegment is itself allocated in Context memory, but it is
   * never updated; it serves as information about the d_list segment
   * pointer it contains only.
   */
  class ListSegment {
    ListSegment* d_nextSegment;
    size_t d_segmentSize;
    T* d_list;
    ListSegment(const ListSegment&);
  public:
    ListSegment() :
      d_nextSegment(NULL),
      d_segmentSize(0),
      d_list(NULL) {
    }
    ~ListSegment() {
      destroy();
    }
    void initialize(T* list) {
      Assert( d_nextSegment == NULL &&
              d_segmentSize == 0 &&
              d_list == NULL,
              "Double-initialization of ListSegment not permitted" );
      d_list = list;
    }
    void linkTo(ListSegment* nextSegment) {
      Assert( d_nextSegment == NULL,
              "Double-linking of ListSegment not permitted" );
      d_nextSegment = nextSegment;
    }
    ListSegment* getNextSegment() const { return d_nextSegment; }
    size_t& size() { return d_segmentSize; }
    size_t size() const { return d_segmentSize; }
    T& operator[](size_t i) { return d_list[i]; }
    const T& operator[](size_t i) const { return d_list[i]; }
  };/* struct CDList<T, ContextMemoryAllocator<T> >::ListSegment */

  /**
   * The first segment of list memory.
   */
  ListSegment d_headSegment;

  /**
   * A pointer to the final segment of list memory.
   */
  ListSegment* d_tailSegment;

  /**
   * Whether to call the destructor when items are popped from the
   * list.  True by default, but can be set to false by setting the
   * second argument in the constructor to false.
   */
  bool d_callDestructor;

  /**
   * Number of objects in list across all segments.
   */
  size_t d_size;

  /**
   * Total allocated size across all segments.
   */
  size_t d_totalSizeAlloc;

  /**
   * Our allocator.
   */
  Allocator d_allocator;

  /**
   * Lightweight save object for CDList<T, ContextMemoryAllocator<T> >.
   */
  struct CDListSave : public ContextObj {
    ListSegment* d_tail;
    size_t d_tailSize, d_size, d_sizeAlloc;
    CDListSave(ListSegment* tail, size_t size, size_t sizeAlloc) :
      d_tail(tail),
      d_tailSize(tail->size()),
      d_size(size),
      d_sizeAlloc(sizeAlloc) {
    }
  };/* struct CDList<T, ContextMemoryAllocator<T> >::CDListSave */

  /**
   * Private copy constructor undefined (no copy permitted).
   */
  CDList(const CDList<T, Allocator>& l);

  /**
   * Reallocate the array with more space.
   * Throws bad_alloc if memory allocation fails.
   */
  void grow() {
    if(d_headSegment.d_list == NULL) {
      // Allocate an initial list if one does not yet exist
      d_headSegment.d_sizeAlloc = 10;
      Debug("cdlist:cmm") << "initial grow of cdlist " << this
                          << " level " << getContext()->getLevel()
                          << " to " << d_headSegment.d_sizeAlloc << std::endl;
      Assert(d_headSegment.d_sizeAlloc <= d_allocator.max_size(),
             "cannot request %u elements due to allocator limits");
      d_headSegment.d_list = d_allocator.allocate(d_headSegment.d_sizeAlloc);
      if(d_headSegment.d_list == NULL) {
        throw std::bad_alloc();
      }
    } else {
      // Allocate a new array with double the size
      typedef typename Allocator::template rebind<ListSegment>::other
        SegmentAllocator;
      ContextMemoryManager* cmm = d_allocator.getCMM();
      SegmentAllocator segAllocator = SegmentAllocator(cmm);
      ListSegment* newSegment = segAllocator.allocate(1);
      if(newSegment == NULL) {
        throw std::bad_alloc();
      }
      segAllocator.construct(newSegment,
                             ListSegment(getContext(), NULL, 0, NULL));
      size_t newSize = d_tailSegment->d_sizeAlloc * 2;
      Assert(newSize <= d_allocator.max_size(),
             "cannot request %u elements due to allocator limits");
      T* newList = d_allocator.allocate(newSize);
      Debug("cdlist:cmm") << "new segment of cdlistcontext " << this
                          << " level " << getContext()->getLevel()
                          << " to " << newSize
                          << " (from " << d_tailSegment->d_list
                          << " to " << newList << ")" << std::endl;
      if(newList == NULL) {
        throw std::bad_alloc();
      }
      d_tailSegment->linkTo(newSegment);
      d_tailSegment = newSegment;
      d_tailSegment->initialize(newList);
      d_totalSizeAlloc += newSize;
    }
  }

  /**
   * Implementation of mandatory ContextObj method save: simply copies the
   * current size to a copy using the copy constructor (the pointer and the
   * allocated size are *not* copied as they are not restored on a pop).
   * The saved information is allocated using the ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    ContextObj* data =
      new(pCMM) CDListSave(d_tailSegment, d_size, d_totalSizeAlloc);
    Debug("cdlist:cmm") << "save " << this
                        << " at level " << this->getContext()->getLevel()
                        << " size at " << this->d_size
                        << " sizeAlloc at " << this->d_sizeAlloc
                        << " d_list is " << this->d_list
                        << " data:" << data << std::endl;
    return data;
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply restores the
   * previous size.  Note that the list pointer and the allocated size are not
   * changed.
   */
  void restore(ContextObj* data) {
    CDListSave* save = static_cast<CDListSave*>(data);
    Debug("cdlist:cmm") << "restore " << this
                        << " level " << this->getContext()->getLevel()
                        << " data == " << data
                        << " call dtor == " << this->d_callDestructor
                        << " d_tail == " << this->d_tailSegment << std::endl;
    if(this->d_callDestructor) {
      const size_t size = save->d_size;
      while(this->d_size != size) {
        --this->d_size;
        this->d_allocator.destroy((*this)[this->d_size]);
      }
    } else {
      this->d_size = save->d_size;
    }
    this->d_tailSegment = save->d_tail;
    this->d_tailSegment->size() = save->d_tailSize;
    Debug("cdlist:cmm") << "restore " << this
                        << " level " << this->getContext()->getLevel()
                        << " size back to " << this->d_size
                        << " sizeAlloc at " << this->d_sizeAlloc << std::endl;
  }

public:

  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDList(Context* context, bool callDestructor, const Allocator& alloc) :
    ContextObj(context),
    d_headSegment(),
    d_tailSegment(&d_headSegment),
    d_callDestructor(callDestructor),
    d_size(0),
    d_allocator(alloc) {
  }

  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDList(bool allocatedInCMM, Context* context, bool callDestructor,
         const Allocator& alloc) :
    ContextObj(allocatedInCMM, context),
    d_headSegment(),
    d_tailSegment(&d_headSegment),
    d_callDestructor(callDestructor),
    d_size(0),
    d_allocator(alloc) {
  }

  /**
   * Destructor: delete the list
   */
  ~CDList() throw(AssertionException) {
    this->destroy();

    if(this->d_callDestructor) {
      for(size_t i = 0; i < this->d_size; ++i) {
        this->d_allocator.destroy((*this)[i]);
      }
    }
  }

  /**
   * Return the current size of (i.e. valid number of objects in) the
   * list.
   */
  size_t size() const {
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
    Debug("cdlist:cmm") << "push_back " << this
                        << " level " << getContext()->getLevel()
                        << ": make-current, "
                        << "d_list == " << &(*d_tailSegment)[0] << std::endl;
    makeCurrent();

    Debug("cdlist:cmm") << "push_back " << this
                        << " level " << getContext()->getLevel()
                        << ": grow? " << d_size
                        << " size_alloc " << d_totalSizeAlloc
                        << std::endl;

    if(d_size == d_totalSizeAlloc) {
      Debug("cdlist:cmm") << "push_back " << this
                          << " " << getContext()->getLevel()
                          << ": grow!\n";
      grow();
    }
    Assert(d_size < d_totalSizeAlloc);

    Debug("cdlist:cmm") << "push_back " << this
                        << " " << getContext()->getLevel()
                        << ": construct! at [" << d_size << "] == "
                        << &(*d_tailSegment)[d_tailSegment->size()]
                        << std::endl;
    d_allocator.construct(&(*d_tailSegment)[d_tailSegment->size()], data);
    Debug("cdlist:cmm") << "push_back " << this
                        << " " << getContext()->getLevel()
                        << ": done..." << std::endl;
    ++d_tailSegment->size();
    ++d_size;
    Debug("cdlist:cmm") << "push_back " << this
                        << " " << getContext()->getLevel()
                        << ": size now " << d_size << std::endl;
  }

  /**
   * Access to the ith item in the list.
   */
  const T& operator[](size_t i) const {
    Assert(i < d_size, "index out of bounds in CDList::operator[]");
    ListSegment* seg = &d_headSegment;
    while(i >= seg->size()) {
      i -= seg->size();
      seg = seg->getNextSegment();
    }
    return (*seg)[i];
  }

  /**
   * Returns the most recent item added to the list.
   */
  const T& back() const {
    Assert(d_size > 0, "CDList::back() called on empty list");
    return (*d_tailSegment)[d_tailSegment->size() - 1];
  }

  /**
   * Iterator for CDList class.  It has to be const because we don't
   * allow items in the list to be changed.  It's a straightforward
   * wrapper around a pointer.  Note that for efficiency, we implement
   * only prefix increment and decrement.  Also note that it's OK to
   * create an iterator from an empty, uninitialized list, as begin()
   * and end() will have the same value (NULL).
   */
  class const_iterator {
    const ListSegment* d_segment;
    size_t d_index;

    const_iterator(const ListSegment* segment, size_t i) :
      d_segment(segment),
      d_index(i) {
    }

    friend class CDList<T, Allocator>;

  public:

    typedef std::input_iterator_tag iterator_category;
    typedef T value_type;
    typedef ptrdiff_t difference_type;
    typedef const T* pointer;
    typedef const T& reference;

    const_iterator() : d_segment(NULL), d_index(0) {}

    inline bool operator==(const const_iterator& i) const {
      return d_segment == i.d_segment && d_index == i.d_index;
    }

    inline bool operator!=(const const_iterator& i) const {
      return !(*this == i);
    }

    inline const T& operator*() const {
      return (*d_segment)[d_index];
    }

    /** Prefix increment */
    const_iterator& operator++() {
      if(++d_index >= d_segment->size()) {
        d_segment = d_segment->getNextSegment();
        d_index = 0;
      }
      return *this;
    }

    /** Postfix increment: returns new iterator with the old value. */
    const_iterator operator++(int) {
      const_iterator i = *this;
      ++(*this);
      return i;
    }
  };/* class CDList<>::const_iterator */

  /**
   * Returns an iterator pointing to the first item in the list.
   */
  const_iterator begin() const {
    return const_iterator(&d_headSegment, 0);
  }

  /**
   * Returns an iterator pointing one past the last item in the list.
   */
  const_iterator end() const {
    return const_iterator(d_tailSegment, d_tailSegment->size());
  }
};/* class CDList<T, ContextMemoryAllocator<T> > */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDLIST_CONTEXT_MEMORY_H */

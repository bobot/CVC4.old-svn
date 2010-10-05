/**
 * Generic context-dependent dynamic array.  Note that for efficiency, this
 * implementation makes the following assumptions:
 * 1. Over time, objects are only added to the list.  Objects are only
 *    removed when a pop restores the list to a previous state.
 * 2. T objects can safely be copied using their copy constructor,
 *    operator=, and memcpy.
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
  class ListSegment : public ContextObj {
    ListSegment* d_nextSegment;
    size_t d_segmentSizeAlloc;
    T* d_list;
    // private ctor for saving
    ListSegment(ListSegment* nextSegment, size_t segmentSizeAlloc, T* list) :
      d_nextSegment(nextSegment),
      d_segmentSizeAlloc(segmentSizeAlloc),
      d_list(list) {
    }
  protected:
    ContextObj* save(ContextMemoryManager* pCMM) {
      new(pCMM) CDList<T, Allocator>(d_nextSegment, d_segmentSizeAlloc, d_list);
    }
    void restore(ContextObj* data) {
      ListSegment* segment = (ListSegment*) data;
      d_nextSegment = segment->d_nextSegment;
      d_segmentSizeAlloc = segment->d_segmentSizeAlloc;
      d_list = segment->d_list;
    }
  public:
    ListSegment(Context* context) :
      ContextObj(context),
      d_nextSegment(NULL),
      d_segmentSizeAlloc(0),
      d_list(NULL) {
    }
    ~ListSegment() {
      destroy();
    }
    void initialize(size_t sizeAlloc, T* list) {
      Assert( d_nextSegment == NULL &&
              d_segmentSizeAlloc == 0 &&
              d_list == NULL,
              "Double-initialization of ListSegment not permitted" );
      makeCurrent();
      d_segmentSizeAlloc = sizeAlloc;
      d_list = list;
    }
    void linkTo(ListSegment* nextSegment) {
      Assert( d_nextSegment == NULL,
              "Double-linking of ListSegment not permitted" );
      makeCurrent();
      d_nextSegment = nextSegment;
    }
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
   * Number of objects in d_list
   */
  unsigned d_size;

  /**
   * Our allocator.
   */
  Allocator d_allocator;

  /**
   * Private copy constructor used only by save().
   */
  CDList(const CDList<T, Allocator>& l) :
    ContextObj(l),
    d_headSegment(l.d_headSegment),
    d_tailSegment(l.d_tailSegment),
    d_callDestructor(false),
    d_size(l.d_size),
    d_allocator(l.d_allocator) {
    Debug("cdlist") << "copy ctor: " << this << " from " << &l << " size " << d_size << std::endl;
  }

  /**
   * Reallocate the array with more space.
   * Throws bad_alloc if memory allocation fails.
   */
  void grow() {
    if(d_headSegment.d_list == NULL) {
      // Allocate an initial list if one does not yet exist
      d_sizeAlloc = 10;
      Debug("cdlist") << "initial grow of cdlist " << this << " level " << getContext()->getLevel() << " to " << d_sizeAlloc << std::endl;
      Assert(d_sizeAlloc <= d_allocator.max_size(),
             "cannot request %u elements due to allocator limits");
      d_headSegment.d_list = d_allocator.allocate(d_sizeAlloc);
      if(d_headSegment.d_list == NULL) {
        throw std::bad_alloc();
      }
    } else {
      // Allocate a new array with double the size
      typedef typename Allocator::rebind<ListSegment>::other SegmentAllocator;
      ContextMemoryManager* cmm = d_allocator.getCMM();
      Context* context = cmm->getContext();
      SegmentAllocator segAllocator = SegmentAllocator(cmm);
      ListSegment* newSegment = segAllocator.allocate(1);
      if(newSegment == NULL) {
        throw std::bad_alloc();
      }
      segAllocator.construct(newSegment, ListSegment(context, NULL, 0, NULL));
      size_t newSize = d_sizeAlloc * 2;
      Assert(newSize <= d_allocator.max_size(),
             "cannot request %u elements due to allocator limits");
      T* newList = d_allocator.allocate(newSize);
      Debug("cdlist") << "2x grow of cdlist " << this << " level " << getContext()->getLevel() << " to " << newSize << " (from " << d_list << " to " << newList << ")" << std::endl;
      if(newList == NULL) {
        throw std::bad_alloc();
      }
      d_tailSegment->linkTo(newSegment);
      d_tailSegment = newSegment;
      d_tailSegment->initialize(newSize, newList);
    }
  }

  /**
   * Implementation of mandatory ContextObj method save: simply copies the
   * current size to a copy using the copy constructor (the pointer and the
   * allocated size are *not* copied as they are not restored on a pop).
   * The saved information is allocated using the ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    ContextObj* data = new(pCMM) CDList<T, Allocator>(*this);
    Debug("cdlist") << "save " << this << " at level " << this->getContext()->getLevel() << " size at " << this->d_size << " sizeAlloc at " << this->d_sizeAlloc << " d_list is " << this->d_list << " data:" << data << std::endl;
    return data;
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply restores the
   * previous size.  Note that the list pointer and the allocated size are not
   * changed.
   */
  void restore(ContextObj* data) {
    Debug("cdlist") << "restore " << this << " level " << this->getContext()->getLevel() << " data == " << data << " call dtor == " << this->d_callDestructor << " d_list == " << this->d_list << std::endl;
    if(this->d_callDestructor) {
      const unsigned size = ((CDList<T, Allocator>*)data)->d_size;
      while(this->d_size != size) {
        --this->d_size;
        this->d_allocator.destroy((*this)[this->d_size]);
      }
    } else {
      this->d_size = ((CDList<T, Allocator>*)data)->d_size;
    }
    this->d_tailSegment = ((CDList<T, Allocator>*)data)->d_tailSegment;
    Debug("cdlist") << "restore " << this << " level " << this->getContext()->getLevel() << " size back to " << this->d_size << " sizeAlloc at " << this->d_sizeAlloc << std::endl;
  }

public:

  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDList(Context* context, bool callDestructor, const Allocator& alloc) :
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
  CDList(bool allocatedInCMM, Context* context, bool callDestructor, const Allocator& alloc) :
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
    this->destroy();

    if(this->d_callDestructor) {
      for(unsigned i = 0; i < this->d_size; ++i) {
        this->d_allocator.destroy((*this)[i]);
      }
    }
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
    Debug("cdlist") << "push_back " << this << " " << getContext()->getLevel() << ": make-current, d_list == " << d_list << "\n";
    makeCurrent();

    Debug("cdlist") << "push_back " << this << " " << getContext()->getLevel() << ": grow? " << d_size << " " << d_sizeAlloc << "\n";
    // FIXME START HERE
    if(d_size == d_sizeAlloc) {
      Debug("cdlist") << "push_back " << this << " " << getContext()->getLevel() << ": grow!\n";
      grow();
    }

    Debug("cdlist") << "push_back " << this << " " << getContext()->getLevel() << ": construct! at " << d_list << "[" << d_size << "] == " << &d_list[d_size] << "\n";
    d_allocator.construct(&d_list[d_size], data);
    Debug("cdlist") << "push_back " << this << " " << getContext()->getLevel() << ": done...\n";
    ++d_size;
    Debug("cdlist") << "push_back " << this << " " << getContext()->getLevel() << ": size now " << d_size << "\n";
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

    friend class CDList<T, Allocator>;

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
};/* class CDList<> */




template <class T>
class CDList<T, ContextMemoryAllocator<T> > : public CDListBase<T, ContextMemoryAllocator<T> > {
  typedef ContextMemoryAllocator<T> Allocator;
public:
  typedef typename CDListBase<T, Allocator>::const_iterator const_iterator;

protected:
  /**
   * Private copy constructor used only by save().  d_list and d_sizeAlloc
   * are not copied: only the base class information and d_size are needed in
   * restore.
   */
  CDList(const CDList<T, Allocator>& l) :
    CDListBase<T, Allocator>(l) {
    this->d_list = l.d_list;
    this->d_size = l.d_size;
    this->d_sizeAlloc = l.d_sizeAlloc;
    Debug("cdlist") << "copy ctor: " << this << " from " << &l << " size " << this->d_size << std::endl;
  }

  /**
   * Implementation of mandatory ContextObj method save: simply copies the
   * current size to a copy using the copy constructor (the pointer and the
   * allocated size are *not* copied as they are not restored on a pop).
   * The saved information is allocated using the ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    ContextObj* data = new(pCMM) CDList<T, Allocator>(*this);
    Debug("cdlist") << "save " << this << " at level " << this->getContext()->getLevel() << " size at " << this->d_size << " sizeAlloc at " << this->d_sizeAlloc << " d_list is " << this->d_list << " data:" << data << std::endl;
    return data;
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply restores the
   * previous size.  Note that the list pointer and the allocated size are not
   * changed.
   */
  void restore(ContextObj* data) {
    Debug("cdlist") << "restore " << this << " level " << this->getContext()->getLevel() << " data == " << data << " call dtor == " << this->d_callDestructor << " d_list == " << this->d_list << std::endl;
    if(this->d_callDestructor) {
      const unsigned size = ((CDList<T, Allocator>*)data)->d_size;
      while(this->d_size != size) {
        --this->d_size;
        this->d_allocator.destroy(&this->d_list[this->d_size]);
      }
    } else {
      this->d_size = ((CDList<T, Allocator>*)data)->d_size;
    }
    this->d_list = ((CDList<T, Allocator>*)data)->d_list;
    this->d_sizeAlloc = ((CDList<T, Allocator>*)data)->d_sizeAlloc;
    Debug("cdlist") << "restore " << this << " level " << this->getContext()->getLevel() << " size back to " << this->d_size << " sizeAlloc at " << this->d_sizeAlloc << std::endl;
  }

public:

  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDList(Context* context, bool callDestructor = true, const Allocator& alloc = Allocator()) :
    CDListBase<T, Allocator>(context, callDestructor, alloc) {
  }

  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDList(bool allocatedInCMM, Context* context, bool callDestructor = true, const Allocator& alloc = Allocator()) :
    CDListBase<T, Allocator>(allocatedInCMM, context, callDestructor, alloc) {
  }

  /**
   * Destructor: delete the list
   */
  ~CDList() throw(AssertionException) {
    this->destroy();

    if(this->d_callDestructor) {
      for(unsigned i = 0; i < this->d_size; ++i) {
        this->d_allocator.destroy(&this->d_list[i]);
      }
    }

    this->d_allocator.deallocate(this->d_list, this->d_sizeAlloc);
  }
};/* class CDList<> */

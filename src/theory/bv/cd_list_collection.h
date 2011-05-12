/*********************                                                        */
/*! \file cd_list_collection.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once

#include <iostream>
#include "context/cdo.h"
#include "theory/bv/generalized_vector.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace context {

/**
 * A class representing a backtrackable set of slice points. The memory should allow indexing with the TreeEntry.left and
 * TreeEntry.right. TreeEntry should also provide null for the non-existing reference and a constructor with (value,
 * left, right).
 */
template<typename value_type>
  class BacktrackableListCollection {

  public:

    /** The type we use to reference the elements */
    typedef ssize_t reference_type;

    /** The null pointer (maximal positive value) */
    static const reference_type null = ((reference_type) (-1)) >> 1;

    /** List elements */
    struct list_element {
      /** Value of the element */
      value_type value;
      /** Previous and next pointers */
      reference_type prev, next;

      /** Construct the element */
      list_element(const value_type& value, reference_type prev,
                   reference_type next) :
        value(value), prev(prev), next(next) {
      }
    };

    /**
     * Memory for list elements. It is index with integers, where negative integers are the non-backtrackable ones
     * and the positive integers are the backtrackable ones.
     */
    typedef gvector<list_element> memory_type;

  private:

    /** Backtrackable iterator */
    struct iterator {

      /** The list we are iterating over */
      reference_type list;
      /** The current list element */
      context::CDO<reference_type>* current;

      /** Constructor */
      iterator(reference_type list, context::Context* context) :
        list(list) {
        current = new (false) context::CDO<reference_type>(context, list);
      }

    };

    /** The context we are using */
    context::Context* d_context;

    /** The memory this set collection will use */
    memory_type d_memory;

    /** Backtrackable number of backtrackable list elements that have been inserted */
    context::CDO<unsigned> d_backtrackableInserted;

    /** Check if the reference is valid in the current context */
    inline bool isValid(reference_type element) const {
      return d_backtrackableInserted == d_memory.positive_size() && (element
          == null || element < (reference_type) d_memory.positive_size());
    }

    /** Backtrack  */
    void backtrack() {
      // Backtrack the lists
      while(d_backtrackableInserted < d_memory.positive_size()) {
        // Get the element
        list_element& element = d_memory.back();
        // Remove it from it's list
        if(element.prev != null) {
          Assert(element.prev + 1 < (reference_type) d_memory.positive_size());
          // If there is a next element, we need to reconnect
          if(element.next != null) {
            Assert(element.next + 1 < (reference_type) d_memory.positive_size());
            list_element& next = d_memory[element.next];
            next.prev = element.prev;
          }
          // Reconnect the previous element to the next
          list_element& prev = d_memory[element.prev];
          prev.next = element.next;
        }
        // Remove the element from memory
        d_memory.pop_back();
      }
    }

    /** Const version of backtrack */
    inline void backtrack() const {
      const_cast<BacktrackableListCollection*> (this)->backtrack();
    }

    /** All the iterators. */
    std::vector<iterator> d_iterators;

  public:

    BacktrackableListCollection(context::Context* context) :
      d_context(context), d_backtrackableInserted(context, 0) {
    }

    /**
     * Returns the current size of the memory.
     */
    size_t size() const {
      backtrack();
      return d_memory.size();
    }

    /**
     * Insert the given value after the given reference. If after is null, a new list will be created.
     */
    template<bool backtrackable>
      reference_type insert(const value_type& value,
                            reference_type after = null) {
        backtrack();
        Assert(isValid(after));

        // Reference of the new element
        reference_type newElement = backtrackable ? d_memory.positive_size()
            : d_memory.negative_size();

        if(after == null) {
          // If requested, create a new list
          if(backtrackable) {
            d_memory.push_back(list_element(value, null, null));
          } else {
            d_memory.push_front(list_element(value, null, null));
          }
        } else {
          // Get the previous element
          list_element& prevElement = d_memory[after];
          // Create the new element
          if(backtrackable) {
            d_memory.push_back(list_element(value, after, prevElement.next));
            d_memory.back().prev = after;
            d_memory.back().next = prevElement.next;
          } else {
            d_memory.push_front(list_element(value, after, prevElement.next));
            d_memory.front().prev = after;
            d_memory.front().next = prevElement.next;
          }
          // Fix up the next element if it's there
          if(prevElement.next != null) {
            d_memory[prevElement.next].prev = newElement;
          }
          // Fix up the previous element if it's there
          prevElement.next = newElement;
        }

        // Return the reference
        return newElement;
      }

    value_type getElement(reference_type list) const {
      backtrack();
      return d_memory[list].value;
    }

    void getStaticElements(reference_type list, std::vector<value_type>& out) const {
      while (list != null) {
        const list_element& element = d_memory[list];
        if (list < 0) {
          out.push_back(element.value);
        }
        list = element.next;
      }
    }

    /**
     * Print the list of elements to the output.
     */
    void print(std::ostream& out, reference_type list) const {
      backtrack();
      Assert(isValid(list));
      out << "[";
      bool first = true;
      while(list != null) {
        if(!first)
          out << ",";
        out << d_memory[list].value;
        first = false;
      }
      out << "]";
    }

    /**
     * String representation of a list.
     */
    std::string toString(reference_type list) const {
      backtrack();
      Assert(isValid(list));

      std::stringstream out;
      print(out, list);
      return out.str();
    }

    /**
     * Since the iterators are managed by the collection, we return references instead of the iterators themself.
     */
    class iterator_reference {

      friend class BacktrackableListCollection;

      /** Index of the iterators in the iterators array */
      size_t d_itIndex;

      /** The responsible list collection */
      BacktrackableListCollection* d_collection;

      /** Useful constructor */
      iterator_reference(size_t itIndex,
                         BacktrackableListCollection* collection) :
        d_itIndex(itIndex), d_collection(collection) {
      }

    public:

      /**
       * Default constructor.
       */
      iterator_reference() :
        d_itIndex(0), d_collection(0) {
      }

      /**
       * Copy constructor.
       */
      iterator_reference(const iterator_reference& it) :
        d_itIndex(it.d_itIndex), d_collection(it.d_collection) {
      }

      /**
       * Assignment operator.
       */
      iterator_reference& operator =(const iterator_reference& it) {
        if(this != &it) {
          d_itIndex = it.d_itIndex;
          d_collection = it.d_collection;
        }
        return *this;
      }

      /**
       * Dereference operator.
       */
      value_type operator *() const {
        const iterator& it = d_collection->d_iterators[d_itIndex];
        return d_collection->getElement(*it.current);
      }

      /**
       * Is there a next element of the list.
       */
      bool hasNext() const {
        iterator& it = d_collection->d_iterators[d_itIndex];
        return d_collection->d_memory[*it.current].next != null;
      }

      /**
       * Move to the next element of the list.
       */
      iterator_reference& operator ++() {
        iterator& it = d_collection->d_iterators[d_itIndex];
        Assert(hasNext());
        *it.current = d_collection->d_memory[*it.current].next;
        return *this;
      }

      /**
       * Insert a new list element after the iterator (these elements are backtrackable).
       */
      void insert(value_type value) {
        iterator& it = d_collection->d_iterators[d_itIndex];
        d_collection->template insert<true> (value, *it.current);
      }

      /**
       * Is this iterator at the end.
       */
      bool isNull() const {
        return *d_collection->d_iterators[d_itIndex].current == null;
      }

      /**
       * Get the elements of the original list (non-backtrackable ones).
       */
      void getStaticElements(std::vector<value_type>& out) const {
        d_collection->getStaticElements(d_collection->d_iterators[d_itIndex].list, out);
      }
    };

    /**
     * Get a reference to a fresh iterator for the given list.
     */
    iterator_reference begin(reference_type list) {
      Assert(list != null && list < 0, "list reference is not a valid static list element");
      size_t index = d_iterators.size();
      d_iterators.push_back(iterator(list, d_context));
      return iterator_reference(index, this);
    }

    /**
     * Ensure that the collection is up-to-date.
     */
    void ensureCurrent() {
      backtrack();
    }
  };

} // Namespace context
} // Namespace CVC4s

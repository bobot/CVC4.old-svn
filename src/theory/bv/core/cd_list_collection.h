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

#include <climits>
#include <sstream>
#include <iostream>

#include "context/cdo.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace context {

/**
 * A class representing a backtrackable list of elements. The elements of a list can be either static or backtrackable.
 * The static elements are never removed, and the backtrackable elements are remove (and the enclosing list relinked)
 * on backtracks according to the context. Additionally, there is each edge can have a type for user purposes.
 */
template<typename value_type, typename edge_type, unsigned edge_type_size>
  class BacktrackableListCollection {

  public:

    /** The type we use to reference the elements */
    typedef size_t reference_type;

    // data layout for references:
    // type | backtrackable | reference

    /** The size of the the reference type in bits */
    static const unsigned reference_type_size = CHAR_BIT * sizeof(reference_type);
    /** The size of the referenct type payload */
    static const unsigned reference_type_payload_size = reference_type_size - edge_type_size - 1;
    /** Payload mask */
    static const reference_type reference_type_payload_mask = ((reference_type) (-1)) >> (edge_type_size + 1);
    /** Backtrackable mask */
    static const reference_type reference_type_backtrackable_mask = 1 << (reference_type_size - reference_type_payload_size);
    /** The null pointer is just all 1 */
    static const reference_type null = -1;

    /**
     * Is this list edge backtrackable?
     */
    static bool isBacktrackable(reference_type ref) {
      return ref & reference_type_backtrackable_mask;
    }

    /**
     * Set the backtrackable flag on.
     */
    static void setBacktrackable(reference_type& ref) {
      ref |= reference_type_backtrackable_mask;
    }

    /**
     * Is this edge be flagged.
     */
    static edge_type getType(reference_type ref) {
      return (edge_type) (ref >> (reference_type_payload_size + 1));
    }

    /**
     * Set the user flag on, can only be used once.
     */
    static void setType(reference_type& ref, edge_type type) {
      Assert(getType(ref) == (edge_type)0);
      ref |= ((reference_type) type << (reference_type_payload_size + 1));
    }

    /**
     * Returns the edge index.
     */
    static size_t getIndex(reference_type ref) {
      return ref & reference_type_payload_mask;
    }

    /** List elements */
    struct list_element {
      /** Value of the element */
      value_type value;
      /** Previous and next pointers */
      reference_type prev, next;

      /** Construct the element */
      list_element(const value_type& value, reference_type prev, reference_type next) :
        value(value), prev(prev), next(next) {
      }
    };

    /**
     * Memory for list elements. It is index with integers, where negative integers are the non-backtrackable ones
     * and the positive integers are the backtrackable ones.
     */
    typedef std::vector<list_element> memory_type;

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

    /** The memory this set collection will use (backtrackable elements) */
    memory_type d_backtrackable_memory;
    /** The memory this set collection will use (statioc elements) */
    memory_type d_static_memory;

    /** Backtrackable number of backtrackable list elements that have been inserted */
    context::CDO<unsigned> d_backtrackableInserted;

    /** Check if the reference is valid in the current context */
    inline bool isValid(reference_type element) const {
      if (element == null) return true;
      if (isBacktrackable(element) && getIndex(element) >= d_backtrackable_memory.size()) return false;
      if (!isBacktrackable(element) && getIndex(element) >= d_static_memory.size()) return false;
      return true;
    }

    /** Get the list element */
    list_element& getElement(reference_type ref) {
      Assert(isValid(ref));
      if (isBacktrackable(ref)) return d_backtrackable_memory[getIndex(ref)];
      else return d_static_memory[getIndex(ref)];
    }

    /** Backtrack  */
    void backtrack() {
      if (d_backtrackableInserted < d_backtrackable_memory.size()) {
        Debug("context::list_collection") << "BacktrackableListCollection::backtrack()" << std::endl;
        // Backtrack the lists
        while(d_backtrackableInserted < d_backtrackable_memory.size()) {
          // Get the element
          list_element& element = d_backtrackable_memory.back();
          // Remove it from it's list
          if(element.prev != null) {
            // If there is a next element, we need to reconnect
            if(element.next != null) {
              list_element& next = getElement(element.next);
              next.prev = element.prev;
            }
            // Reconnect the previous element to the next
            list_element& prev = getElement(element.prev);
            prev.next = element.next;
          }
          // Remove the element from memory
          d_backtrackable_memory.pop_back();
        }
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
      d_context(context),
      d_backtrackableInserted(context, 0)
    {
      Debug("context::list_collection") << "BacktrackableListCollection(): " << std::endl
          << "null = " << +null << std::endl
          << "reference_size = " << +reference_type_size << std::endl
          << "payload mask = " << +reference_type_payload_mask << std::endl
          << "payload size = " << +reference_type_payload_size << std::endl;
    }

    /**
     * Returns the current size of the memory.
     */
    size_t size() const {
      backtrack();
      return d_backtrackable_memory.size() + d_static_memory.size();
    }

    /**
     * Insert the given value after the given reference. If after is null, a new list will be created.
     */
    template<bool backtrackable, edge_type type>
      reference_type insert(const value_type& value, reference_type after = null) {
        backtrack();
        Assert(isValid(after));

        Debug("context::list_collection") << "BacktrackableListCollection::insert(" << value << ", " << toString(after) << ")" << std::endl;

        // Reference of the new element
        reference_type newElement = backtrackable ? d_backtrackable_memory.size() : d_static_memory.size();
        if (backtrackable) {
          d_backtrackableInserted = d_backtrackableInserted + 1;
          setBacktrackable(newElement);
        }

        // Set the edge type
        setType(newElement, type);
        setType(after, type);

        if(after == null) {
          // If requested, create a new list
          if(backtrackable) {
            d_backtrackable_memory.push_back(list_element(value, null, null));
          } else {
            d_static_memory.push_back(list_element(value, null, null));
          }
        } else {
          // Create the new element
          if(backtrackable) {
            d_backtrackable_memory.push_back(list_element(value, after, getElement(after).next));
          } else {
            d_static_memory.push_back(list_element(value, after, getElement(after).next));
          }
          // Fix up the next element if it's there
          list_element& prevElement = getElement(after);
          if(prevElement.next != null) {
            list_element& nextElement = getElement(prevElement.next);
            nextElement.prev = newElement;
          }
          // Fix up the previous element if it's there
          prevElement.next = newElement;

          Debug("context::list_collection") << "BacktrackableListCollection::insert(" << value << ", " << toString(after) << ") => " << newElement << std::endl;
        }

        // Return the reference
        return newElement;
      }

    /** Get the list element (const version) */
    const list_element& getElement(reference_type ref) const {
      Assert(isValid(ref));
      if (isBacktrackable(ref)) return d_backtrackable_memory[getIndex(ref)];
      else return d_static_memory[getIndex(ref)];
    }

    /**
     * Return the element pointed to with the reference.
     */
    value_type getElementValue(reference_type list) const {
      backtrack();
      return getElement(list).value;
    }

    /** 
     * Returns all the elements in the list that are not backtrackable.
     */
    void getStaticElements(reference_type list, std::vector<value_type>& out) const {
      while(list != null) {
        const list_element& element = getElement(list);
        if (isBacktrackable(list)) {
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
        const list_element& element = getElement(list);
        out << element.value;
        list = element.next;
        first = false;
      }
      out << "]";
    }

    /**
     * String representation of the list.
     */
    std::string toString(reference_type list) const {
      std::stringstream ss;
      print(ss, list);
      return ss.str();
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
      iterator_reference(size_t itIndex, BacktrackableListCollection* collection) :
        d_itIndex(itIndex), d_collection(collection) {
      }

    public:

      /**
       * Default constructor.
       */
      iterator_reference() :
        d_itIndex(0), d_collection(0)
      {}

      /**
       * Copy constructor.
       */
      iterator_reference(const iterator_reference& it) :
        d_itIndex(it.d_itIndex), d_collection(it.d_collection)
      {}

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
        return d_collection->getElementValue(*it.current);
      }

      /**
       * Is there a next element of the list.
       */
      bool hasNext() const {
        const iterator& it = d_collection->d_iterators[d_itIndex];
        return d_collection->getElement(*it.current).next != null;
      }

      /**
       * Get the responisble list collection.
       */
      const BacktrackableListCollection& getListCollection() const {
        return *d_collection;
      }

      /**
       * Get the enclosing list.
       */
      reference_type getList() const {
        return d_collection->d_iterators[d_itIndex].list;
      }

      /**
       * Move to the next element of the list.
       */
      iterator_reference& operator ++() {

        Debug("context::list_collection") << "BacktrackableListCollection::iterator_reference ++ (): " << toString() << std::endl;

        iterator& it = d_collection->d_iterators[d_itIndex];
        Assert(hasNext());

        *it.current = d_collection->getElement(*it.current).next;

        Debug("context::list_collection") << "BacktrackableListCollection::iterator_reference ++ (): " << toString() << std::endl;

        return *this;
      }

      /**
       * Insert a new list element after the iterator (these elements are backtrackable).
       */
      template<edge_type type>
      void insert(value_type value) {
        iterator& it = d_collection->d_iterators[d_itIndex];
        d_collection->template insert<true, type> (value, *it.current);
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

      /**
       * Print the list with the iterator emphasized.
       */
      void print(std::ostream& out) const {
        const iterator& it = d_collection->d_iterators[d_itIndex];
        reference_type current = it.list;
        reference_type itReference = *it.current;
        out << "[";
        while(current != null) {
          if(current == itReference)
            out << "(";
          const list_element& currentElement = d_collection->getElement(current);
          out << currentElement.value;
          if(current == itReference)
            out << ")";
          current = currentElement.next;
          if(current != null)
            out << ",";
        }
        out << "]";
      }

      std::string toString() const {
        std::stringstream ss;
        print(ss);
        return ss.str();
      }
    };

    /**
     * Get a reference to a fresh iterator for the given list.
     */
    iterator_reference begin(reference_type list) {
      Assert(list != null && !isBacktrackable(list), "list reference is not a valid static list element");
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
} // Namespace CVC4

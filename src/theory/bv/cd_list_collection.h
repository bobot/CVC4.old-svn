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
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace context {

/**
 * A class representing a backtrackable set of slice points. The memory should allow indexing with the TreeEntry.left and
 * TreeEntry.right. TreeEntry should also provide null for the non-existing reference and a constructor with (value,
 * left, right).
 */
template <typename value_type>
class BacktrackableListCollection {

public:

  /** The type we use to reference the elements */
  typedef size_t reference_type;

  /** The null pointer */
  static const reference_type null = (reference_type)(-1);

  /** List elements */
  struct list_element
  {
    /** Value of the element */
    value_type value;
    /** Previous and next pointers */
    reference_type prev, next;

    /** Construct the element */
    list_element(const value_type& value, reference_type prev, reference_type next) :
      value(value), prev(prev), next(next)
    {}
  };

  /** Memory for list elements */
  typedef std::vector<list_element> memory_type;

private:

  /** The memory this set collection will use */
  memory_type d_memory;

  /** Backtrackable number of list elements that have been inserted */
  context::CDO<unsigned> d_elementsInserted;

  /** Check if the reference is valid in the current context */
  inline bool isValid(reference_type element) const {
    return d_elementsInserted == d_memory.size() && (element == null || element < d_memory.size());
  }

  /** Backtrack and notify of the mark changes */
  void backtrack() {
    // Backtrack the lists
    while (d_elementsInserted < d_memory.size()) {
      // Get the element
      list_element& element = d_memory.back();
      // Remove it from it's list
      if (element.prev != null) {
        Assert(element.prev + 1 < d_memory.size());
        // If there is a next element, we need to reconnect
        if (element.next != null) {
          Assert(element.next + 1 < d_memory.size());
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
    const_cast<BacktrackableListCollection*>(this)->backtrack();
  }

public:

  BacktrackableListCollection(context::Context* context)
  : d_elementsInserted(context, 0) {}

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
  reference_type insert(const value_type& value, reference_type after = null) {
    backtrack();
    Assert(isValid(after));

    // Reference of the new element
    reference_type newElement = d_memory.size();

    if (after == null) {
      // If requested, create a new list
      d_memory.push_back(list_element(value, null, null));
    } else {
      // Get the previous element
      list_element& prevElement = d_memory[after];
      // Create the new element
      d_memory.push_back(list_element(value, after, prevElement.next));
      d_memory.back().prev = after;
      d_memory.back().next = prevElement.next;
      // Fix up the next element if it's there
      if (prevElement.next != null) {
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

  /**
   * Print the list of elements to the output.
   */
  void print(std::ostream& out, reference_type list) const {
    backtrack();
    Assert(isValid(list));
    out << "[";
    bool first = true;
    while (list != null) {
      if (!first) out << ",";
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
};

} // Namespace context
} // Namespace CVC4s

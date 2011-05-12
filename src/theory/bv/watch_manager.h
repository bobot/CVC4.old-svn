/*********************                                                        */
/*! \file watch_manager.h
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

#include <queue>
#include <vector>
#include <ext/hash_map>

#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/cd_list_collection.h"

namespace CVC4 {
namespace theory {
namespace bv {


/**
 * This class encapsulates a watch manager for equalities involving concatenations. For each equality it watches
 * two corresponding concat elements at both sides in order to eagerly deduce when the equality becomes satisfied.
 */
template <typename EqualityNotify>
class ConcatWatchManager {

public:

  /** The memory manager for the context dependent lists */
  typedef context::BacktrackableListCollection<TNode> list_collection;

  /**
   * Substitution x = t
   */
  struct Substitution {
    TNode x, t;
    Substitution(TNode x, TNode t):
      x(x), t(t) {}
  };

  /** The watch element */
  struct Watch {
  
    /** The iterator to the watched left-hand side concat element */
    list_collection::iterator_reference lhsListIt;
    /** The iterator to the watched right-hand side concat element */
    list_collection::iterator_reference rhsListIt;
    
    /** Construct the watch */
    Watch(list_collection& listCollection, list_collection::reference_type lhsList, list_collection::reference_type rhsList):
      lhsListIt(listCollection.begin(lhsList)),
      rhsListIt(listCollection.begin(rhsList))
    {}
    
    /** 
     * Check whether this watch is watching the given term (it might have became irrelevant).
     */
    bool isCurrent(TNode x) const {
    	return *lhsListIt == x || *rhsListIt == x;
    }
    
    /** 
     * Insert the concatenation after the iterator and move the iterator to the next element.
     */
    void substitute(list_collection::iterator_reference& it, TNode concat) {
      if (concat.getKind() == kind::BITVECTOR_CONCAT) {
        for(int i = concat.getNumChildren(); i >= 0; -- i) {
          it.insert(concat[i]);
        }
      } else {
        it.insert(concat);
      }
      ++ it;
    }
    
    /**
     * Try and substitute the given.
     */
    bool substitute(const Substitution& subst) {
      if (*lhsListIt == subst.x) {
        substitute(lhsListIt, subst.t);
        return true;  
      } else if (*rhsListIt == subst.x) {
        substitute(rhsListIt, subst.t);
        return true;
      } else {
        return false;
      }
    }
  };

  /** List of watches */
  typedef std::vector<Watch> watch_list;

  /** Map from nodes to the watches that are watching the node */
  typedef __gnu_cxx::hash_map<TNode, watch_list, TNodeHashFunction> watch_map;

private:

  /** The class to notify when an equality becomes true or false */
  EqualityNotify& d_notifyClass;

  /** The context we are using */
  context::Context* d_context;

  /** The CD collection of lists we are using */
  list_collection d_listCollection;

  /** Map from nodes to watches watching them */
  watch_map d_watches;

  /**
   * Makes a list out of a concatenation.
   */
  list_collection::reference_type mkList(TNode node);

  /** Queue of the left-hand sides to process */
  std::queue<Substitution> d_queue;

public:

  /**
   * Constructs a watch manager.
   */
  ConcatWatchManager(EqualityNotify& notify, context::Context* context):
    d_notifyClass(notify),
    d_context(context),
    d_listCollection(context)
  {}

  /**
   * Add an equality to the watch manager (not context-dependent). The equalities should be over bit-vector normalized
   * core terms, i.e. pure vairables, or concatenations.
   */
  void addEqualityToWatch(TNode lhs, TNode rhs);

  /**
   * Adds an solved equality to the context. This might trigger two registered (via addEqualityToWathc) equalities
   * become true or false, which will be dispatched to the EqualityNotify class.
   */
  void addSubstitution(TNode solvedLhs, TNode rhs);

  /**
   * Propagates the information in the queue, trying to deduce any of the watched equalities true or false. Returns
   * true if no conflict was detected.
   */
  bool propagate();
};

template <typename EqualityNotify>
void ConcatWatchManager<EqualityNotify>::addEqualityToWatch(TNode lhs, TNode rhs) {

  // Make lists of lhs and rhs elements
  list_collection::reference_type lhsList = mkList(lhs);
  list_collection::reference_type rhsList = mkList(rhs);

  // Attach the watches
  Watch watch(d_listCollection, lhsList, rhsList);
  d_watches[d_listCollection.getElement(lhsList)].push_back(watch);
  d_watches[d_listCollection.getElement(rhsList)].push_back(watch);
}

template <typename EqualityNotify>
ConcatWatchManager<EqualityNotify>::list_collection::reference_type ConcatWatchManager<EqualityNotify>::mkList(TNode node) {

  if (node.getKind() == kind::BITVECTOR_CONCAT) {
    list_collection::reference_type result = list_collection::null, current = list_collection::null;
    for (unsigned i = 0; i < node.getNumChildren(); ++ i) {
      Assert(node[i].getKind() != kind::BITVECTOR_CONCAT);
      current = d_listCollection.insert<false>(node[i], current);
      if (i == 0) {
        result = current;
      }
    }
    return result;
  } else {
    return d_listCollection.insert<false>(node);
  }
}

template <typename EqualityNotify>
void ConcatWatchManager<EqualityNotify>::addSubstitution(TNode solvedLhs, TNode rhs) {
  typename watch_map::iterator find = d_watches.find(solvedLhs);
  if (find != d_watches.end()) {
    d_queue.push(Substitution(solvedLhs, rhs));
  }
}

template <typename EqualityNotify>
bool ConcatWatchManager<EqualityNotify>::propagate() {
  // Ensure the list collection is in a good state
  d_listCollection.ensureCurrent();
  // Do the work
  while (!d_queue.empty()) {
    // Get the equation x = t which we need to substitute
    Substitution subst = d_queue.front();
    d_queue.pop();
    // Get the watch-list for x
    typename watch_map::iterator find = d_watches.find(subst.x);
    if (find != d_watches.end()) {
      // Get the watch-list and go through the individual watches
      watch_list& watches = find->second;
      typename watch_list::iterator w = watches.begin();
      typename watch_list::iterator w_end = watches.end();
      for(; w != w_end; ++ w) {
        // Try and substitute
        if (w->substitute(subst)) {
          // Check for equalitites in order to move the iterators  
		}
      }
    }
  }
  return true;
}


} // Namespace bv
} // Namespace theory
} // Namespace CVC4

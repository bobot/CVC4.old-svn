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
#include <sstream>
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
template<typename EqualityNotify>
  class ConcatWatchManager {

  public:

    /** The memory manager for the context dependent lists */
    typedef context::BacktrackableListCollection<TNode> list_collection;

    /**
     * Substitution x = t
     */
    struct Substitution {
      TNode x, t;
      Substitution(TNode x, TNode t) :
        x(x), t(t) {
      }
    };

    /** The watch element */
    struct Watch {

      /** The iterator to the watched left-hand side concat element */
      typename list_collection::iterator_reference lhsListIt;
      /** The iterator to the watched right-hand side concat element */
      typename list_collection::iterator_reference rhsListIt;

      /**
       * Print the watch.
       */
      void print(std::ostream& out) const {
        out << "{ ";
        lhsListIt.print(out);
        out << " == ";
        rhsListIt.print(out);
        out << " }";
      }

      /**
       * String representation of the watch.
       */
      std::string toString() const {
        std::stringstream ss;
        print(ss);
        return ss.str();
      }

      /** The undefined watch */
      Watch()
      {}

      /** Construct the watch */
      Watch(list_collection& listCollection, list_collection::reference_type lhsList, list_collection::reference_type rhsList) :
        lhsListIt(listCollection.begin(lhsList)), rhsListIt(listCollection.begin(rhsList))
      {}

      /** Copy constructor */
      Watch(const Watch& w) :
        lhsListIt(w.lhsListIt),
        rhsListIt(w.rhsListIt)
      {}

      /**
       * Insert the concatenation after the iterator and move the iterator to the next element.
       */
      void substitute(list_collection::iterator_reference& it, TNode concat) {
        if(concat.getKind() == kind::BITVECTOR_CONCAT) {
          for(int i = concat.getNumChildren(); i >= 0; --i) {
            it.insert(concat[i]);
          }
        } else {
          it.insert(concat);
        }
        ++it;
      }

      /**
       * Try and substitute the given.
       */
      bool substitute(const Substitution& subst) {
        if(*lhsListIt == subst.x) {
          substitute(lhsListIt, subst.t);
          return true;
        } else if(*rhsListIt == subst.x) {
          substitute(rhsListIt, subst.t);
          return true;
        } else {
          return false;
        }
      }

      /** 
       * Normalizes the iterator.
       */
      template<typename EqualityManager>
        void normalize(const EqualityManager& eqManager, list_collection::iterator_reference it) {
          while(!it.isNull()) {
            TNode element = *it;
            TNode elementRep = eqManager.getRepresentative(element);
            if(elementRep == element) {
              // If the current element is it's own representative, we are done
              break;
            } else {
              // Otherwise we must perform a substitution, so get the substitutions
              std::vector<TNode> equalities;
              eqManager.getExplanation(element, elementRep, equalities);
              for(unsigned i = 0; i < equalities.size(); ++i) {
                TNode equality = equalities[i];
                if(equality[0] == element) {
                  substitute(it, equality[1]);
                } else {
                  substitute(it, equality[0]);
                }
              }
            }
          }
        }

      /**
       * Normalize the watch.
       */
      template<typename EqualityManager>
        void normalize(const EqualityManager& eqManager) {
        normalize(eqManager, lhsListIt);
        normalize(eqManager, rhsListIt);
      }

      /**
       * Increase the watch pointers by one and normalize (substitute) the first remaining elements.
       */
      template<typename EqualityManager>
        void next(const EqualityManager& eqManager) {
          // Move the iterators
          normalize(eqManager, ++lhsListIt);
          normalize(eqManager, ++rhsListIt);
        }

      /**
       * Get the original equality out of the watch.
       */
      TNode getEquality() const {
        std::vector<TNode> lhsElements, rhsElements;
        rhsListIt.getStaticElements(lhsElements);
        lhsListIt.getStaticElements(rhsElements);
        return utils::mkConcat(lhsElements).eqNode(utils::mkConcat(rhsElements));
      }
    };

    /** List of watches */
    typedef std::vector<Watch> watch_list;

    /** Map from nodes to the watches that are watching the node */
    typedef __gnu_cxx ::hash_map<TNode, watch_list, TNodeHashFunction> watch_map;

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
    ConcatWatchManager(EqualityNotify& notify, context::Context* context) :
      d_notifyClass(notify), d_context(context), d_listCollection(context) {
    }

    /**
     * Add an equality to the watch manager (not context-dependent). The equalities should be over bit-vector normalized
     * core terms, i.e. pure vairables, or concatenations.
     */
    template<typename EqualityManager>
    void addEqualityToWatch(EqualityManager& eq, TNode lhs, TNode rhs);

    /**
     * Adds an solved equality to the context. This might trigger two registered (via addEqualityToWathc) equalities
     * become true or false, which will be dispatched to the EqualityNotify class.
     */
    void addSubstitution(TNode solvedLhs, TNode rhs);

    /**
     * Given a watch finds the next elements to watch. If a propagatio is found it is sent to the notify.
     * @return true if something has been propagated, false otherwise
     */
    template<typename EqualityManager>
    bool findNextToWatch(Watch& w, EqualityManager& eqManager);

    /**
     * Propagates the information in the queue, trying to deduce any of the watched equalities true or false. Returns
     * true if no conflict was detected.
     */
    template<typename EqualityManager>
    void propagate(EqualityManager& eqManager);
  };

template<typename EqualityNotify>
template<typename EqualityManager>
  void ConcatWatchManager<EqualityNotify>::addEqualityToWatch(EqualityManager& eqManager, TNode lhs, TNode rhs) {

    Debug("theory::bv::watch_manager") << "ConcatWatchManager::addEqualityToWatch(" << lhs << ", " << rhs << ")" << std::endl;

    // Make lists of lhs and rhs elements
    list_collection::reference_type lhsList = mkList(lhs);
    list_collection::reference_type rhsList = mkList(rhs);

    // Attach the watches
    Watch watch(d_listCollection, lhsList, rhsList);
    watch.normalize(eqManager);
    bool propagated = findNextToWatch(watch, eqManager);
    if(!propagated) {
      // Add to the watch-list of the non-constant
      if ((*watch.lhsListIt).getKind() != kind::CONST_BITVECTOR) {
        d_watches[*watch.lhsListIt].push_back(watch);
      }
      if ((*watch.rhsListIt).getKind() != kind::CONST_BITVECTOR) {
        d_watches[*watch.rhsListIt].push_back(watch);
      }
    }
  }

  template<typename EqualityNotify>
  ConcatWatchManager<EqualityNotify>::list_collection::reference_type ConcatWatchManager<EqualityNotify>::mkList(TNode node) {

    if(node.getKind() == kind::BITVECTOR_CONCAT) {
      list_collection::reference_type result = list_collection::null, current =
      list_collection::null;
      for(unsigned i = 0; i < node.getNumChildren(); ++i) {
        Assert(node[i].getKind() != kind::BITVECTOR_CONCAT);
        current = d_listCollection.insert<false> (node[i], current);
        if(i == 0) {
          result = current;
        }
      }
      return result;
    } else {
      return d_listCollection.insert<false> (node);
    }
  }

  template<typename EqualityNotify>
  void ConcatWatchManager<EqualityNotify>::addSubstitution(TNode solvedLhs, TNode rhs) {
    typename watch_map::iterator find = d_watches.find(solvedLhs);
    if(find != d_watches.end()) {
      d_queue.push(Substitution(solvedLhs, rhs));
    }
  }

  template<typename EqualityNotify>
  template<typename EqualityManager>
  bool ConcatWatchManager<EqualityNotify>::findNextToWatch(Watch& w, EqualityManager& eqManager) {
    // Check for equalitites in order to move the iterators
    bool propagated = false;
    while (true) {
      // If the current elements are the same we shift
      if(*w.lhsListIt == *w.rhsListIt) {
        if(!w.lhsListIt.hasNext()) {
          // All elements of the list are equal, propagate
          d_notifyClass(w.getEquality(), true);
          propagated = true;
          break;
        }
        // Move to the next element
        w.next(eqManager);
      } else {
        // Get the current elements
        TNode lhsElement = *w.lhsListIt;
        TNode rhsElement = *w.rhsListIt;
        // If both are constants, we need to slice them
        if (lhsElement.getKind() == kind::CONST_BITVECTOR && rhsElement.getKind() == kind::CONST_BITVECTOR) {
          unsigned lhsSize = utils::getSize(lhsElement);
          unsigned rhsSize = utils::getSize(rhsElement);
          if (lhsSize < rhsSize) {
            TNode rhsHigh = utils::mkConst(rhsElement.getConst<BitVector>().extract(rhsSize-1, rhsSize-lhsSize));
            TNode rhsLow = utils::mkConst(rhsElement.getConst<BitVector>().extract(rhsSize-lhsSize-1, 0));
            w.substitute(w.rhsListIt, utils::mkConcat(rhsHigh, rhsLow));
          } else if (lhsSize > rhsSize) {
            TNode lhsHigh = utils::mkConst(lhsElement.getConst<BitVector>().extract(lhsSize - 1, lhsSize - rhsSize));
            TNode lhsLow = utils::mkConst(lhsElement.getConst<BitVector>().extract(lhsSize - rhsSize - 1, 0));
            w.substitute(w.lhsListIt, utils::mkConcat(lhsHigh, lhsLow));
          }
          // Now they are constants of the same size
          if (*w.lhsListIt != *w.rhsListIt) {
            // Since they are different this must be a conflict
            d_notifyClass(w.getEquality(), false);
            propagated = true;
            break;
          }
        } else {
          // Since they are not both constants, it's time to attach
          break;
        }
      }
    }
    // Nothing propagated
    return propagated;
  }

  template<typename EqualityNotify>
  template<typename EqualityManager>
  void ConcatWatchManager<EqualityNotify>::propagate(EqualityManager& eqManager) {

    Debug("theory::bv::watch_manager") << "ConcatWatchManager::propagate()" << std::endl;

    // Ensure the list collection is in a good state
    d_listCollection.ensureCurrent();
    // Do the work
    while(!d_queue.empty())
    {
      // Get the equation x = t which we need to substitute
      Substitution subst = d_queue.front();
      d_queue.pop();
      Debug("theory::bv::watch_manager") << "ConcatWatchManager::propagate(): substituting " << subst.x << " with " << subst.t << std::endl;

      // Get the watch-list for x
      typename watch_map::iterator find = d_watches.find(subst.x);
      if(find != d_watches.end()) {
        // Get the watch-list and go through the individual watches
        watch_list& watches = find->second;
        unsigned i = 0, newSize = 0;
        unsigned i_end = watches.size();
        for(; i != i_end; ++i) {
          // Try and substitute
          Watch& w = watches[i];
          Debug("theory::bv::watch_manager") << "ConcatWatchManager::propagate(): processing watch " << w.toString() << std::endl;

          // Otherwise, try to substitute
          if(w.substitute(subst)) {
            // Attach to the next element
            bool propagated = findNextToWatch(w, eqManager);
            // Add to the updated watches
            if(!propagated) {
              // Add to the watch-list of the non-constant
              if ((*w.lhsListIt).getKind() != kind::CONST_BITVECTOR) {
                d_watches[*w.lhsListIt].push_back(w);
              }
              if ((*w.rhsListIt).getKind() != kind::CONST_BITVECTOR) {
                d_watches[*w.rhsListIt].push_back(w);
              }
            }
            // Keep this watch
            watches[newSize++] = w;
          }
        }
        // Resize the watchlist
        watches.resize(newSize);
      }
    }
  }

} // Namespace bv
} // Namespace theory
} // Namespace CVC4

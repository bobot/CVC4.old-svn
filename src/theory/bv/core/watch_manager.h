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
#include "theory/bv/core/cd_list_collection.h"

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

      /** Id of the watch */
      unsigned id;

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
      Watch(unsigned id, list_collection& listCollection, list_collection::reference_type lhsList, list_collection::reference_type rhsList) :
        id(id), lhsListIt(listCollection.begin(lhsList)), rhsListIt(listCollection.begin(rhsList))
      {}

      /** Copy constructor */
      Watch(const Watch& w) :
        id(w.id),
        lhsListIt(w.lhsListIt),
        rhsListIt(w.rhsListIt)
      {}

      /**
       * Insert the concatenation after the iterator and move the iterator to the next element.
       */
      void substitute(list_collection::iterator_reference& it, TNode concat) {
        if(concat.getKind() == kind::BITVECTOR_CONCAT) {
          for(int i = concat.getNumChildren() - 1; i >= 0; --i) {
            if (i == 0) {
              it.insert<true>(concat[i]);
            } else {
              it.insert<false>(concat[i]);
            }
          }
        } else {
          it.insert<true>(concat);
        }
        ++it;
      }

      /**
       * Try and substitute the given.
       */
      bool substitute(const Substitution& subst) {
        Assert(*lhsListIt != subst.x || *rhsListIt != subst.x);
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
            Debug("theory::bv::watch_manager") << "ConcatWatchManager::normalize(): normalizing " << it.toString() << std::endl;
            TNode element = *it;
            TNode elementRep = eqManager.getRepresentative(element);
            if(elementRep == element) {
              // If the current element is it's own representative, we are done
              break;
            } else {
              // Otherwise we must perform a substitution, so get the substitutions
              substitute(it, elementRep);
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
       * Is this watch done, i.e. propagated equality already.
       */
      bool done() const {
        return (*lhsListIt == *rhsListIt);
      }

      /**
       * Returns the assumptions used in normalizing the list.
       */
      void getSubstitutions(
          const list_collection& listCollection, TNode x, list_collection::reference_type& list,
          std::vector<Substitution>& substitutions)
      {
        // Since null is flagged, it will pop up and we ignore it
        if (list == list_collection::null) {
          return;
        }

        Debug("theory::bv::watch_manager") << "ConcatWatchManager::getSubstitutions(" << x << ", " << listCollection.toString(list) << ")" << std::endl;

        // Get the size we are matching
        unsigned size = utils::getSize(x);

        // Scan until we match the size, and accumulate the nodes in the concat vector
        std::vector<TNode> concat;
        while (size > 0) {
          // Get the current element
          Debug("theory::bv::watch_manager") << "ConcatWatchManager::getSubstitutions(): processing" << listCollection.toString(list) << ", size = " << size << std::endl;
          const list_collection::list_element& current = listCollection.getElement(list);
          // We add it to the concat at this level
          concat.push_back(current.value);
          // Move to the next one
          Assert(size >= utils::getSize(current.value));
          size -= utils::getSize(current.value);
          list = current.next;
          // If no more to consume, we're done
          if (list_collection::isFlagged(list)) {
            getSubstitutions(listCollection, current.value, list, substitutions);
          }
        }

        // Add the substitution
        Debug("theory::bv::watch_manager") << "ConcatWatchManager::getSubstitutions(): adding " << x << " = " << utils::mkConcat(concat) << std::endl;
        substitutions.push_back(Substitution(x, utils::mkConcat(concat)));
      }

      /**
       * Returns the assumptions used in normalizing the watch.
       */
      template<typename EqualityManager>
      void getAssumptions(const EqualityManager& eqManager, TNode lhs, TNode rhs, std::vector<TNode>& assumptions) {
        Debug("theory::bv::watch_manager") << "ConcatWatchManager::getAssumptions(" << lhs << ", " << rhs << ")" << std::endl;
        // The responsible list collection
        const list_collection& listCollection = lhsListIt.getListCollection();
        // We accumulate the substitutions into this vector
        std::vector<Substitution> substitutions;
        // Get the lhs substitutions
        list_collection::reference_type lhsList = lhsListIt.getList();
        getSubstitutions(listCollection, lhs, lhsList, substitutions);
        // Get rid of the last (which is lhs = lhs)
        Assert(lhs == substitutions.back().t);
        substitutions.pop_back();
        // Get the rhs substitutions
        list_collection::reference_type rhsList = rhsListIt.getList();
        getSubstitutions(listCollection, rhs, rhsList, substitutions);
        // Get rid of the last (which is lhs = lhs)
        Assert(rhs == substitutions.back().t);
        substitutions.pop_back();
        // Go through the substitutions and get the reasons
        for (unsigned i = 0; i < substitutions.size(); ++ i) {
          const Substitution& substitution = substitutions[i];
          // If this is a contant that's sliced, there is no explanation
          if (substitution.x.getKind() != kind::CONST_BITVECTOR) {
            eqManager.getExplanation(substitution.x, substitution.t, assumptions);
          }
        }
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

    /** List of terms that we need to ensure are referenced */
    context::CDList<Node> d_termTracker;

    /** The CD collection of lists we are using */
    list_collection d_listCollection;

    /** Map from nodes to watches watching them */
    watch_map d_watches;

    /** List of all watches */
    std::vector<Watch> d_watchesList;

    /** List of original equalities we are watching */
    std::vector<TNode> d_watchedEqualities;

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
      d_notifyClass(notify), d_context(context), d_termTracker(context), d_listCollection(context) {
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
    bool findNextToWatch(Watch watch, EqualityManager& eqManager);

    /**
     * Propagates the information in the queue, trying to deduce any of the watched equalities true or false. Returns
     * true if no conflict was detected.
     */
    template<typename EqualityManager>
    void propagate(EqualityManager& eqManager);

    /**
     * Assumming that the watch has propagated, gatger the reasons behind the propagation.
     */
    template<typename EqualityManager>
    void explain(const EqualityManager& eqManager, unsigned watchId, std::vector<TNode>& assumptions) const;
  };

template<typename EqualityNotify>
template<typename EqualityManager>
  void ConcatWatchManager<EqualityNotify>::addEqualityToWatch(EqualityManager& eqManager, TNode lhs, TNode rhs) {

    Debug("theory::bv::watch_manager") << "ConcatWatchManager::addEqualityToWatch(" << lhs << ", " << rhs << ")" << std::endl;

    // Make lists of lhs and rhs elements
    list_collection::reference_type lhsList = mkList(lhs);
    list_collection::reference_type rhsList = mkList(rhs);

    // Attach the watches
    unsigned watchIndex = d_watchesList.size();
    Watch watch(watchIndex, d_listCollection, lhsList, rhsList);
    d_watchesList.push_back(watch);
    d_watchedEqualities.push_back(lhs.eqNode(rhs));
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
        current = d_listCollection.insert<false, false> (node[i], current);
        if(i == 0) {
          result = current;
        }
      }
      return result;
    } else {
      return d_listCollection.insert<false, false> (node);
    }
  }

  template<typename EqualityNotify>
  void ConcatWatchManager<EqualityNotify>::addSubstitution(TNode solvedLhs, TNode rhs) {
    Debug("theory::bv::watch_manager") << "ConcatWatchManager::addSubstitution(" << solvedLhs << "," << rhs << ")" << std::endl;
    d_queue.push(Substitution(solvedLhs, rhs));
  }

  template<typename EqualityNotify>
  template<typename EqualityManager>
  bool ConcatWatchManager<EqualityNotify>::findNextToWatch(Watch w, EqualityManager& eqManager) {
    // Check for equalitites in order to move the iterators
    Debug("theory::bv::watch_manager") << "ConcatWatchManager::findNextToWatch(" << w.toString() << ")" << std::endl;
    bool propagated = false;
    while (true) {
      // If the current elements are the same we shift
      if(*w.lhsListIt == *w.rhsListIt) {
        if(!w.lhsListIt.hasNext()) {
          // All elements of the list are equal, propagate
          d_notifyClass(w.id, d_watchedEqualities[w.id], true);
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
            Node rhsHigh = utils::mkConst(rhsElement.getConst<BitVector>().extract(rhsSize-1, rhsSize-lhsSize));
            Node rhsLow = utils::mkConst(rhsElement.getConst<BitVector>().extract(rhsSize-lhsSize-1, 0));
            Node concat = utils::mkConcat(rhsHigh, rhsLow);
            w.substitute(w.rhsListIt, concat);
            // Since this node might not exist, we need to track it
            d_termTracker.push_back(concat);
          } else if (lhsSize > rhsSize) {
            Node lhsHigh = utils::mkConst(lhsElement.getConst<BitVector>().extract(lhsSize - 1, lhsSize - rhsSize));
            Node lhsLow = utils::mkConst(lhsElement.getConst<BitVector>().extract(lhsSize - rhsSize - 1, 0));
            Node concat = utils::mkConcat(lhsHigh, lhsLow);
            // Since this node might not exist, we need to track it
            d_termTracker.push_back(concat);
            w.substitute(w.lhsListIt, concat);
          }
          // Now they are constants of the same size
          if (*w.lhsListIt != *w.rhsListIt) {
            // Since they are different this must be a conflict
            d_notifyClass(w.id, d_watchedEqualities[w.id], false);
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
    Debug("theory::bv::watch_manager") << "ConcatWatchManager::findNextToWatch() => " << w.toString() << std::endl;
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
          // If the watch is done we keep and continue
          if (w.done()) {
            watches[newSize++] = w;
          }
          // Otherwise, try to substitute
          else if(w.substitute(subst)) {
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

  template<typename EqualityNotify>
  template<typename EqualityManager>
  void ConcatWatchManager<EqualityNotify>::explain(const EqualityManager& eqManager, unsigned watchId, std::vector<TNode>& assumptions) const {
    // We only propagate in two cases (1) elements are all the same (2) two constant parts are different
    // In the first case we pick all the equalities backwards, in the other we pick eqaulitites until the
    // first original in the watch
    Watch w = d_watchesList[watchId];
    Debug("theory::bv::watch_manager") << "ConcatWatchManager::explain(" << d_watchedEqualities[watchId] << ")" << std::endl;
    if (*w.lhsListIt == *w.rhsListIt) {
      // Equality
      Assert(!w.lhsListIt.hasNext() && !w.rhsListIt.hasNext());
      w.getAssumptions(eqManager, d_watchedEqualities[watchId][0], d_watchedEqualities[watchId][1], assumptions);
    } else {
      // Disequality
    }

  }

} // Namespace bv
} // Namespace theory
} // Namespace CVC4

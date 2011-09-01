/*********************                                                        */
/*! \file equality_engine_impl.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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

#include "cvc4_private.h"

#pragma once

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace uf {

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::enqueue(const MergeCandidate& candidate) {
    Debug("equality") << "EqualityEngine::enqueue(" << candidate.toString(*this) << ")" << std::endl;
    d_propagationQueue.push(candidate);
}

template <typename NotifyClass>
EqualityNodeId EqualityEngine<NotifyClass>::newApplicationNode(TNode original, EqualityNodeId t1, EqualityNodeId t2) {
  Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ")" << std::endl;

  ++ d_stats.functionTermsCount;

  // Get another id for this
  EqualityNodeId funId = newNode(original, true);
  FunctionApplication fun(t1, t2);
  d_applications[funId] = fun;

  // The function application we're creating
  EqualityNodeId t1ClassId = getEqualityNode(t1).getFind();
  EqualityNodeId t2ClassId = getEqualityNode(t2).getFind();
  FunctionApplication funNormalized(t1ClassId, t2ClassId);

  // Add the lookup data, if it's not already there
  typename ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
  if (find == d_applicationLookup.end()) {
    // When we backtrack, if the lookup is not there anymore, we'll add it again
    Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): no lookup, setting up" << std::endl;
    d_applicationLookup[funNormalized] = funId;
  } else {
    // If it's there, we need to merge these two
    Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): lookup exists, adding to queue" << std::endl;
    enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
    propagate();
  }

  // Add to the use lists
  d_equalityNodes[t1].usedIn(funId, d_useListNodes);
  d_equalityNodes[t2].usedIn(funId, d_useListNodes);

  // Return the new id
  Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ") => " << funId << std::endl;

  return funId;
}

template <typename NotifyClass>
EqualityNodeId EqualityEngine<NotifyClass>::newNode(TNode node, bool isApplication) {

  Debug("equality") << "EqualityEngine::newNode(" << node << ", " << (isApplication ? "function" : "regular") << ")" << std::endl;

  ++ d_stats.termsCount;

  // Register the new id of the term
  EqualityNodeId newId = d_nodes.size();
  d_nodeIds[node] = newId;
  // Add the node to it's position
  d_nodes.push_back(node);
  // Note if this is an application or not
  d_applications.push_back(FunctionApplication());
  // Add the trigger list for this node
  d_nodeTriggers.push_back(+null_trigger);
  // Add it to the equality graph
  d_equalityGraph.push_back(+null_edge);
  // Add the equality node to the nodes
  d_equalityNodes.push_back(EqualityNode(newId));

  Debug("equality") << "EqualityEngine::newNode(" << node << ", " << (isApplication ? "function" : "regular") << ") => " << newId << std::endl;

  return newId;
}


template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addTerm(TNode t) {

  Debug("equality") << "EqualityEngine::addTerm(" << t << ")" << std::endl;

  // If there already, we're done
  if (hasTerm(t)) {
    return;
  }

  EqualityNodeId result;

  // If a function application we go in
  if (t.getNumChildren() > 0 && d_congruenceKinds[t.getKind()])
  {
    // Add the operator
    TNode tOp = t.getOperator();
    addTerm(tOp);
    // Add all the children and Curryfy
    result = getNodeId(tOp);
    for (unsigned i = 0; i < t.getNumChildren(); ++ i) {
      // Add the child
      addTerm(t[i]);
      // Add the application
      result = newApplicationNode(t, result, getNodeId(t[i]));
    }
  } else {
    // Otherwise we just create the new id
    result = newNode(t, false);
  }

  Debug("equality") << "EqualityEngine::addTerm(" << t << ") => " << result << std::endl;
}

template <typename NotifyClass>
bool EqualityEngine<NotifyClass>::hasTerm(TNode t) const {
  return d_nodeIds.find(t) != d_nodeIds.end();
}

template <typename NotifyClass>
EqualityNodeId EqualityEngine<NotifyClass>::getNodeId(TNode node) const {
  Assert(hasTerm(node), node.toString().c_str());
  return (*d_nodeIds.find(node)).second;
}

template <typename NotifyClass>
EqualityNode& EqualityEngine<NotifyClass>::getEqualityNode(TNode t) {
  return getEqualityNode(getNodeId(t));
}

template <typename NotifyClass>
EqualityNode& EqualityEngine<NotifyClass>::getEqualityNode(EqualityNodeId nodeId) {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

template <typename NotifyClass>
const EqualityNode& EqualityEngine<NotifyClass>::getEqualityNode(TNode t) const {
  return getEqualityNode(getNodeId(t));
}

template <typename NotifyClass>
const EqualityNode& EqualityEngine<NotifyClass>::getEqualityNode(EqualityNodeId nodeId) const {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addEquality(TNode t1, TNode t2, TNode reason) {

  Debug("equality") << "EqualityEngine::addEquality(" << t1 << "," << t2 << ")" << std::endl;

  // Add the terms if they are not already in the database
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);

  // Add to the queue and propagate
  enqueue(MergeCandidate(t1Id, t2Id, MERGED_THROUGH_EQUALITY, reason));
  propagate();
}

template <typename NotifyClass>
TNode EqualityEngine<NotifyClass>::getRepresentative(TNode t) const {

  Debug("equality") << "EqualityEngine::getRepresentative(" << t << ")" << std::endl;

  Assert(hasTerm(t));

  // Both following commands are semantically const
  EqualityNodeId representativeId = getEqualityNode(t).getFind();

  Debug("equality") << "EqualityEngine::getRepresentative(" << t << ") => " << d_nodes[representativeId] << std::endl;

  return d_nodes[representativeId];
}

template <typename NotifyClass>
bool EqualityEngine<NotifyClass>::areEqual(TNode t1, TNode t2) const {
  Debug("equality") << "EqualityEngine::areEqual(" << t1 << "," << t2 << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Both following commands are semantically const
  EqualityNodeId rep1 = getEqualityNode(t1).getFind();
  EqualityNodeId rep2 = getEqualityNode(t2).getFind();

  Debug("equality") << "EqualityEngine::areEqual(" << t1 << "," << t2 << ") => " << (rep1 == rep2 ? "true" : "false") << std::endl;

  return rep1 == rep2;
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::merge(EqualityNode& class1, EqualityNode& class2, std::vector<TriggerId>& triggers) {

  Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << ")" << std::endl;

  Assert(triggers.empty());

  ++ d_stats.mergesCount;

  EqualityNodeId class1Id = class1.getFind();
  EqualityNodeId class2Id = class2.getFind();

  // Update class2 representative information
  Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): updating class " << class2Id << std::endl;
  EqualityNodeId currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): " << currentId << "->" << class1Id << std::endl;
    currentNode.setFind(class1Id);

    // Go through the triggers and inform if necessary
    TriggerId currentTrigger = d_nodeTriggers[currentId];
    while (currentTrigger != null_trigger) {
      Trigger& trigger = d_equalityTriggers[currentTrigger];
      Trigger& otherTrigger = d_equalityTriggers[currentTrigger ^ 1];

      // If the two are not already in the same class
      if (otherTrigger.classId != trigger.classId) {
        trigger.classId = class1Id;
        // If they became the same, call the trigger
        if (otherTrigger.classId == class1Id) {
          // Id of the real trigger is half the internal one
          triggers.push_back(currentTrigger);
        }
      }

      // Go to the next trigger
      currentTrigger = trigger.nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);


  // Update class2 table lookup and information
  Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of " << class2Id << std::endl;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);    
    Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of node " << currentId << std::endl;
 
    // Go through the uselist and check for congruences
    UseListNodeId currentUseId = currentNode.getUseList();
    while (currentUseId != null_uselist_id) {
      // Get the node of the use list
      UseListNode& useNode = d_useListNodes[currentUseId];
      // Get the function application
      EqualityNodeId funId = useNode.getApplicationId();
      Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): " << currentId << " in " << d_nodes[funId] << std::endl;
      const FunctionApplication& fun = d_applications[useNode.getApplicationId()];
      // Check if there is an application with find arguments
      EqualityNodeId aNormalized = getEqualityNode(fun.a).getFind();
      EqualityNodeId bNormalized = getEqualityNode(fun.b).getFind();
      FunctionApplication funNormalized(aNormalized, bNormalized);
      typename ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
      if (find != d_applicationLookup.end()) {
        // Applications fun and the funNormalized can be merged due to congruence
        if (getEqualityNode(funId).getFind() != getEqualityNode(find->second).getFind()) {
          enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
        }
      } else {
        // There is no representative, so we can add one, we remove this when backtracking
        d_applicationLookup[funNormalized] = funId;
      }
      // Go to the next one in the use list
      currentUseId = useNode.getNext();
    }

    // Move to the next node
    currentId = currentNode.getNext();
  } while (currentId != class2Id);

  // Now merge the lists
  class1.merge<true>(class2);
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::undoMerge(EqualityNode& class1, EqualityNode& class2, EqualityNodeId class2Id) {

  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << ")" << std::endl;

  // Now unmerge the lists (same as merge)
  class1.merge<false>(class2);

  // First undo the table lookup changes
  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << "): undoing lookup changes" << std::endl;
  EqualityNodeId currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Go through the uselist and check for congruences
    UseListNodeId currentUseId = currentNode.getUseList();
    while (currentUseId != null_uselist_id) {
      // Get the node of the use list
      UseListNode& useNode = d_useListNodes[currentUseId];
      // Get the function application
      EqualityNodeId funId = useNode.getApplicationId();
      const FunctionApplication& fun = d_applications[useNode.getApplicationId()];
      // Get the application with find arguments
      EqualityNodeId aNormalized = getEqualityNode(fun.a).getFind();
      EqualityNodeId bNormalized = getEqualityNode(fun.b).getFind();
      FunctionApplication funNormalized(aNormalized, bNormalized);
      typename ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
      // If the id is the one we set, then we undo it
      if (find != d_applicationLookup.end() && find->second == funId) {
        d_applicationLookup.erase(find);
      }
      // Go to the next one in the use list
      currentUseId = useNode.getNext();
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Update class2 representative information
  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << "): undoing representative info" << std::endl;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    currentNode.setFind(class2Id);

    // Go through the trigger list (if any) and undo the class
    TriggerId currentTrigger = d_nodeTriggers[currentId];
    while (currentTrigger != null_trigger) {
      Trigger& trigger = d_equalityTriggers[currentTrigger];
      trigger.classId = class2Id;
      currentTrigger = trigger.nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Now set any missing lookups and check for any congruences on backtrack
  std::vector<MergeCandidate> possibleCongruences;
  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << "): checking for any unset lookups" << std::endl;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Go through the uselist and check for congruences
    UseListNodeId currentUseId = currentNode.getUseList();
    while (currentUseId != null_uselist_id) {
      // Get the node of the use list
      UseListNode& useNode = d_useListNodes[currentUseId];
      // Get the function application
      EqualityNodeId funId = useNode.getApplicationId();
      const FunctionApplication& fun = d_applications[useNode.getApplicationId()];
      // Get the application with find arguments
      EqualityNodeId aNormalized = getEqualityNode(fun.a).getFind();
      EqualityNodeId bNormalized = getEqualityNode(fun.b).getFind();
      FunctionApplication funNormalized(aNormalized, bNormalized);
      typename ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
      Assert(find != d_applicationLookup.end());
      // If the id doesn't exist, we'll set it
      if (find == d_applicationLookup.end()) {
        d_applicationLookup[funNormalized] = funId;
      }
      // Go to the next one in the use list
      currentUseId = useNode.getNext();
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::backtrack() {

  // If we need to backtrack then do it
  if (d_assertedEqualitiesCount < d_assertedEqualities.size()) {

    // Clear the propagation queue
    while (!d_propagationQueue.empty()) {
      d_propagationQueue.pop();
    }

    Debug("equality") << "EqualityEngine::backtrack(): nodes" << std::endl;

    for (int i = (int)d_assertedEqualities.size() - 1, i_end = (int)d_assertedEqualitiesCount; i >= i_end; --i) {
      // Get the ids of the merged classes
      Equality& eq = d_assertedEqualities[i];
      // Undo the merge
      undoMerge(d_equalityNodes[eq.lhs], d_equalityNodes[eq.rhs], eq.rhs);
    }

    d_assertedEqualities.resize(d_assertedEqualitiesCount);

    Debug("equality") << "EqualityEngine::backtrack(): edges" << std::endl;

    for (int i = (int)d_equalityEdges.size() - 2, i_end = (int)(2*d_assertedEqualitiesCount); i >= i_end; i -= 2) {
      EqualityEdge& edge1 = d_equalityEdges[i];
      EqualityEdge& edge2 = d_equalityEdges[i | 1];
      d_equalityGraph[edge2.getNodeId()] = edge1.getNext();
      d_equalityGraph[edge1.getNodeId()] = edge2.getNext();
    }

    d_equalityEdges.resize(2 * d_assertedEqualitiesCount);
  }
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addGraphEdge(EqualityNodeId t1, EqualityNodeId t2, MergeReasonType type, TNode reason) {
  Debug("equality") << "EqualityEngine::addGraphEdge(" << d_nodes[t1] << "," << d_nodes[t2] << "," << reason << ")" << std::endl;
  EqualityEdgeId edge = d_equalityEdges.size();
  d_equalityEdges.push_back(EqualityEdge(t2, d_equalityGraph[t1], type, reason));
  d_equalityEdges.push_back(EqualityEdge(t1, d_equalityGraph[t2], type, reason));
  d_equalityGraph[t1] = edge;
  d_equalityGraph[t2] = edge | 1;

  if (Debug.isOn("equality::internal")) {
    debugPrintGraph();
  }
}

template <typename NotifyClass>
std::string EqualityEngine<NotifyClass>::edgesToString(EqualityEdgeId edgeId) const {
  std::stringstream out;
  bool first = true;
  if (edgeId == null_edge) {
    out << "null";
  } else {
    while (edgeId != null_edge) {
      const EqualityEdge& edge = d_equalityEdges[edgeId];
      if (!first) out << ",";
      out << d_nodes[edge.getNodeId()];
      edgeId = edge.getNext();
      first = false;
    }
  }
  return out.str();
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::getExplanation(TNode t1, TNode t2, std::vector<TNode>& equalities) const {
  Debug("equality") << "EqualityEngine::getExplanation(" << t1 << "," << t2 << ")" << std::endl;

  Assert(getRepresentative(t1) == getRepresentative(t2));

  // Get the explanation
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);
  getExplanation(t1Id, t2Id, equalities);
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::getExplanation(EqualityNodeId t1Id, EqualityNodeId t2Id, std::vector<TNode>& equalities) const {

  Debug("equality") << "EqualityEngine::getExplanation(" << d_nodes[t1Id] << "," << d_nodes[t2Id] << ")" << std::endl;

  // If the nodes are the same, we're done
  if (t1Id == t2Id) return;

  if (Debug.isOn("equality::internal")) {
    const_cast<EqualityEngine*>(this)->debugPrintGraph();
  }

  // Queue for the BFS containing nodes
  std::vector<BfsData> bfsQueue;

  // Find a path from t1 to t2 in the graph (BFS)
  bfsQueue.push_back(BfsData(t1Id, null_id, 0));
  size_t currentIndex = 0;
  while (true) {
    // There should always be a path, and every node can be visited only once (tree)
    Assert(currentIndex < bfsQueue.size());

    // The next node to visit
    BfsData current = bfsQueue[currentIndex];
    EqualityNodeId currentNode = current.nodeId;

    Debug("equality") << "EqualityEngine::getExplanation(): currentNode =  " << d_nodes[currentNode] << std::endl;

    // Go through the equality edges of this node
    EqualityEdgeId currentEdge = d_equalityGraph[currentNode];
    Debug("equality") << "EqualityEngine::getExplanation(): edgesId =  " << currentEdge << std::endl;
    Debug("equality") << "EqualityEngine::getExplanation(): edges =  " << edgesToString(currentEdge) << std::endl;

    while (currentEdge != null_edge) {
      // Get the edge
      const EqualityEdge& edge = d_equalityEdges[currentEdge];

      // If not just the backwards edge
      if ((currentEdge | 1u) != (current.edgeId | 1u)) {

        Debug("equality") << "EqualityEngine::getExplanation(): currentEdge = (" << d_nodes[currentNode] << "," << d_nodes[edge.getNodeId()] << ")" << std::endl;

        // Did we find the path
        if (edge.getNodeId() == t2Id) {

          Debug("equality") << "EqualityEngine::getExplanation(): path found: " << std::endl;

          // Reconstruct the path
          do {
            // The current node
            currentNode = bfsQueue[currentIndex].nodeId;
            EqualityNodeId edgeNode = d_equalityEdges[currentEdge].getNodeId();
            MergeReasonType reasonType = d_equalityEdges[currentEdge].getReasonType();

            Debug("equality") << "EqualityEngine::getExplanation(): currentEdge = " << currentEdge << ", currentNode = " << currentNode << std::endl;

            // Add the actual equality to the vector
            if (reasonType == MERGED_THROUGH_CONGRUENCE) {
              // f(x1, x2) == f(y1, y2) because x1 = y1 and x2 = y2
              Debug("equality") << "EqualityEngine::getExplanation(): due to congruence, going deeper" << std::endl;
              const FunctionApplication& f1 = d_applications[currentNode];
              const FunctionApplication& f2 = d_applications[edgeNode];
              Debug("equality") << push;
              getExplanation(f1.a, f2.a, equalities);
              getExplanation(f1.b, f2.b, equalities);
              Debug("equality") << pop;
            } else {
              // Construct the equality
              Debug("equality") << "EqualityEngine::getExplanation(): adding: " << d_equalityEdges[currentEdge].getReason() << std::endl;
              equalities.push_back(d_equalityEdges[currentEdge].getReason());
            }

            // Go to the previous
            currentEdge = bfsQueue[currentIndex].edgeId;
            currentIndex = bfsQueue[currentIndex].previousIndex;
          } while (currentEdge != null_id);

          // Done
          return;
        }

        // Push to the visitation queue if it's not the backward edge
        bfsQueue.push_back(BfsData(edge.getNodeId(), currentEdge, currentIndex));
      }

      // Go to the next edge
      currentEdge = edge.getNext();
    }

    // Go to the next node to visit
    ++ currentIndex;
  }
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addTriggerEquality(TNode t1, TNode t2, TNode trigger) {

  Debug("equality") << "EqualityEngine::addTrigger(" << t1 << ", " << t2 << ", " << trigger << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Get the information about t1
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t1classId = getEqualityNode(t1Id).getFind();
  TriggerId t1TriggerId = d_nodeTriggers[t1Id];

  // Get the information about t2
  EqualityNodeId t2Id = getNodeId(t2);
  EqualityNodeId t2classId = getEqualityNode(t2Id).getFind();
  TriggerId t2TriggerId = d_nodeTriggers[t2Id];

  Debug("equality") << "EqualityEngine::addTrigger(" << trigger << "): " << t1Id << " (" << t1classId << ") = " << t2Id << " (" << t2classId << ")" << std::endl;

  // Create the triggers
  TriggerId t1NewTriggerId = d_equalityTriggers.size();
  TriggerId t2NewTriggerId = t1NewTriggerId | 1;
  d_equalityTriggers.push_back(Trigger(t1classId, t1TriggerId));
  d_equalityTriggersOriginal.push_back(trigger);
  d_equalityTriggers.push_back(Trigger(t2classId, t2TriggerId));
  d_equalityTriggersOriginal.push_back(trigger);

  // Add the trigger to the trigger graph
  d_nodeTriggers[t1Id] = t1NewTriggerId;
  d_nodeTriggers[t2Id] = t2NewTriggerId;

  // If the trigger is already on, we propagate
  if (t1classId == t2classId) {
    Debug("equality") << "EqualityEngine::addTrigger(" << t1 << "," << t2 << "): triggered at setup time" << std::endl;
    d_notify.notifyEquality(trigger); // Don't care about the return value
  }

  Debug("equality") << "EqualityEngine::addTrigger(" << t1 << "," << t2 << ") => (" << t1NewTriggerId << ", " << t2NewTriggerId << ")" << std::endl;
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::propagate() {

  Debug("equality") << "EqualityEngine::propagate()" << std::endl;

  bool done = false;
  while (!d_propagationQueue.empty()) {

    // The current merge candidate
    const MergeCandidate current = d_propagationQueue.front();
    d_propagationQueue.pop();

    if (done) {
      // If we're done, just empty the queue
      continue;
    }

    // Get the representatives
    EqualityNodeId t1classId = getEqualityNode(current.t1Id).getFind();
    EqualityNodeId t2classId = getEqualityNode(current.t2Id).getFind();

    // If already the same, we're done
    if (t1classId == t2classId) {
      continue;
    }

    // Get the nodes of the representatives
    EqualityNode& node1 = getEqualityNode(t1classId);
    EqualityNode& node2 = getEqualityNode(t2classId);

    Assert(node1.getFind() == t1classId);
    Assert(node2.getFind() == t2classId);

    // Depending on the merge preference (such as size), merge them
    std::vector<TriggerId> triggers;
    if (node2.getSize() > node1.getSize()) {
      Debug("equality") << "EqualityEngine::propagate(): merging " << d_nodes[current.t1Id]<< " into " << d_nodes[current.t2Id] << std::endl;
      merge(node2, node1, triggers);
      d_assertedEqualities.push_back(Equality(t2classId, t1classId));
    } else {
      Debug("equality") << "EqualityEngine::propagate(): merging " << d_nodes[current.t2Id] << " into " << d_nodes[current.t1Id] << std::endl;
      merge(node1, node2, triggers);
      d_assertedEqualities.push_back(Equality(t1classId, t2classId));
    }

    // Add the actuall equality to the equality graph
    addGraphEdge(current.t1Id, current.t2Id, current.type, current.reason);

    // One more equality added
    d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;

    Assert(2*d_assertedEqualities.size() == d_equalityEdges.size());
    Assert(d_assertedEqualities.size() == d_assertedEqualitiesCount);

    // Notify the triggers
    for (size_t trigger = 0, trigger_end = triggers.size(); trigger < trigger_end && !done; ++ trigger) {
      // Notify the trigger and exit if it fails
      done = !d_notify.notifyEquality(d_equalityTriggersOriginal[triggers[trigger]]);
    }
  }
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::debugPrintGraph() const {
  for (EqualityNodeId nodeId = 0; nodeId < d_nodes.size(); ++ nodeId) {

    Debug("equality::internal") << d_nodes[nodeId] << " " << nodeId << "(" << getEqualityNode(nodeId).getFind() << "):";

    EqualityEdgeId edgeId = d_equalityGraph[nodeId];
    while (edgeId != null_edge) {
      const EqualityEdge& edge = d_equalityEdges[edgeId];
      Debug("equality::internal") << " " << d_nodes[edge.getNodeId()] << ":" << edge.getReason();
      edgeId = edge.getNext();
    }

    Debug("equality::internal") << std::endl;
  }
}

} // Namespace uf
} // Namespace theory
} // Namespace CVC4


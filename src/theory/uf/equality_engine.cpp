/*********************                                                        */
/*! \file equality_engine.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): taking, bobot, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace eq {

/**
 * Data used in the BFS search through the equality graph.
 */
struct BfsData {
  // The current node
  EqualityNodeId nodeId;
  // The index of the edge we traversed
  EqualityEdgeId edgeId;
  // Index in the queue of the previous node. Shouldn't be too much of them, at most the size
  // of the biggest equivalence class
  size_t previousIndex;

  BfsData(EqualityNodeId nodeId = null_id, EqualityEdgeId edgeId = null_edge, size_t prev = 0)
  : nodeId(nodeId), edgeId(edgeId), previousIndex(prev) {}
};

class ScopedBool {
  bool& watch;
  bool oldValue;
public:
  ScopedBool(bool& watch, bool newValue)
  : watch(watch), oldValue(watch) {
    watch = newValue;
  }
  ~ScopedBool() {
    watch = oldValue;
  }
};

EqualityEngineNotifyNone EqualityEngine::s_notifyNone;

void EqualityEngine::init() {
  Debug("equality") << "EqualityEdge::EqualityEngine(): id_null = " << +null_id << std::endl;
  Debug("equality") << "EqualityEdge::EqualityEngine(): edge_null = " << +null_edge << std::endl;
  Debug("equality") << "EqualityEdge::EqualityEngine(): trigger_null = " << +null_trigger << std::endl;

  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  d_triggerDatabaseAllocatedSize = 100000;
  d_triggerDatabase = (char*) malloc(d_triggerDatabaseAllocatedSize);

  //We can't notify during the initialization because it notifies
  // QuantifiersEngine.AddTermToDatabase that try to access to the uf
  // instantiator that currently doesn't exist.
  ScopedBool sb(d_performNotify, false);
  addTerm(d_true);
  addTerm(d_false);

  d_trueId = getNodeId(d_true);
  d_falseId = getNodeId(d_false);  
} 

EqualityEngine::~EqualityEngine() throw(AssertionException) {
  free(d_triggerDatabase);
}


EqualityEngine::EqualityEngine(context::Context* context, std::string name) 
: ContextNotifyObj(context)
, d_context(context)
, d_done(context, false)
, d_performNotify(true)
, d_notify(s_notifyNone)
, d_applicationLookupsCount(context, 0)
, d_nodesCount(context, 0)
, d_assertedEqualitiesCount(context, 0)
, d_equalityTriggersCount(context, 0)
, d_stats(name)
, d_triggerDatabaseSize(context, 0)
, d_triggerTermSetUpdatesSize(context, 0)
, d_deducedDisequalitiesSize(context, 0)
, d_deducedDisequalityReasonsSize(context, 0)
, d_propagatedDisequalities(context)
, d_name(name)
{
  init();
}

EqualityEngine::EqualityEngine(EqualityEngineNotify& notify, context::Context* context, std::string name)
: ContextNotifyObj(context)
, d_context(context)
, d_done(context, false)
, d_performNotify(true)
, d_notify(notify)
, d_applicationLookupsCount(context, 0)
, d_nodesCount(context, 0)
, d_assertedEqualitiesCount(context, 0)
, d_equalityTriggersCount(context, 0)
, d_stats(name)
, d_triggerDatabaseSize(context, 0)
, d_triggerTermSetUpdatesSize(context, 0)
, d_deducedDisequalitiesSize(context, 0)
, d_deducedDisequalityReasonsSize(context, 0)
, d_propagatedDisequalities(context)
, d_name(name)
{
  init();
}

void EqualityEngine::enqueue(const MergeCandidate& candidate, bool back) {
  Debug("equality") << d_name << "::eq::enqueue(" << d_nodes[candidate.t1Id] << ", " << d_nodes[candidate.t2Id] << ", " << candidate.type << ")" << std::endl;
  if (back) {
    d_propagationQueue.push_back(candidate);
  } else {
    d_propagationQueue.push_front(candidate);
  }
}

EqualityNodeId EqualityEngine::newApplicationNode(TNode original, EqualityNodeId t1, EqualityNodeId t2, bool isEquality) {
  Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ")" << std::endl;

  ++ d_stats.functionTermsCount;

  // Get another id for this
  EqualityNodeId funId = newNode(original);
  FunctionApplication funOriginal(isEquality, t1, t2);
  // The function application we're creating
  EqualityNodeId t1ClassId = getEqualityNode(t1).getFind();
  EqualityNodeId t2ClassId = getEqualityNode(t2).getFind();
  FunctionApplication funNormalized(isEquality, t1ClassId, t2ClassId);

  // We add the original version
  d_applications[funId] = FunctionApplicationPair(funOriginal, funNormalized);

  // Add the lookup data, if it's not already there
  ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
  if (find == d_applicationLookup.end()) {
    // When we backtrack, if the lookup is not there anymore, we'll add it again
    Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): no lookup, setting up" << std::endl;
    // Mark the normalization to the lookup
    storeApplicationLookup(funNormalized, funId);
    // If an equality over constants we merge to false 
    if (isEquality) {
      if (d_isConstant[t1ClassId] && d_isConstant[t2ClassId] && t1ClassId != t2ClassId) {
        Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): got constants" << std::endl;
        Assert(d_nodes[funId].getKind() == kind::EQUAL);
        enqueue(MergeCandidate(funId, d_falseId, MERGED_THROUGH_CONSTANTS, TNode::null()), false);
        // Also enqueue the symmetric one
        TNode eq = d_nodes[funId];
        Node symmetricEq = eq[1].eqNode(eq[0]);
        if (hasTerm(symmetricEq)) {
          EqualityNodeId symmFunId = getNodeId(symmetricEq);
          enqueue(MergeCandidate(symmFunId, d_falseId, MERGED_THROUGH_CONSTANTS, TNode::null()), false);              
        }
      }
      if (t1ClassId == t2ClassId) {
        enqueue(MergeCandidate(funId, d_trueId, MERGED_THROUGH_REFLEXIVITY, TNode::null()), false);
      }
    }
  } else {
    // If it's there, we need to merge these two
    Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): lookup exists, adding to queue" << std::endl;
    Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): lookup = " << d_nodes[find->second] << std::endl;
    enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
  }

  // Add to the use lists
  Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): adding " << original << " to the uselist of " << d_nodes[t1] << std::endl;
  d_equalityNodes[t1].usedIn(funId, d_useListNodes);
  Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): adding " << original << " to the uselist of " << d_nodes[t2] << std::endl;
  d_equalityNodes[t2].usedIn(funId, d_useListNodes);

  // Return the new id
  Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ") => " << funId << std::endl;

  return funId;
}

EqualityNodeId EqualityEngine::newNode(TNode node) {

  Debug("equality") << d_name << "::eq::newNode(" << node << ")" << std::endl;

  ++ d_stats.termsCount;

  // Register the new id of the term
  EqualityNodeId newId = d_nodes.size();
  d_nodeIds[node] = newId;
  // Add the node to it's position
  d_nodes.push_back(node);
  // Note if this is an application or not
  d_applications.push_back(FunctionApplicationPair());
  // Add the trigger list for this node
  d_nodeTriggers.push_back(+null_trigger);
  // Add it to the equality graph
  d_equalityGraph.push_back(+null_edge);
  // Mark the no-individual trigger
  d_nodeIndividualTrigger.push_back(+null_set_id);
  // Mark non-constant by default
  d_isConstant.push_back(false);
  // Mark Boolean nodes
  d_isBoolean.push_back(false);
  // Mark the node as internal by default
  d_isInternal.push_back(true);
  // Add the equality node to the nodes
  d_equalityNodes.push_back(EqualityNode(newId));

  // Increase the counters
  d_nodesCount = d_nodesCount + 1;

  Debug("equality") << d_name << "::eq::newNode(" << node << ") => " << newId << std::endl;

  // notify e.g. the UF theory strong solver
  if (d_performNotify) {
    d_notify.eqNotifyNewClass(node);
  }

  return newId;
}

void EqualityEngine::addTerm(TNode t) {

  Debug("equality") << d_name << "::eq::addTerm(" << t << ")" << std::endl;

  // If there already, we're done
  if (hasTerm(t)) {
    Debug("equality") << d_name << "::eq::addTerm(" << t << "): already there" << std::endl;
    return;
  }

  if (d_done) {
    return;
  }

  EqualityNodeId result;

  if (t.getKind() == kind::EQUAL) {
    addTerm(t[0]);
    addTerm(t[1]);
    result = newApplicationNode(t, getNodeId(t[0]), getNodeId(t[1]), true);
    d_isInternal[result] = false;
  } else if (t.getNumChildren() > 0 && d_congruenceKinds[t.getKind()]) {
    // Add the operator
    TNode tOp = t.getOperator();
    addTerm(tOp);
    // Add all the children and Curryfy
    result = getNodeId(tOp);
    d_isInternal[result] = true;
    for (unsigned i = 0; i < t.getNumChildren(); ++ i) {
      // Add the child
      addTerm(t[i]);
      // Add the application
      result = newApplicationNode(t, result, getNodeId(t[i]), false);
    }
    d_isInternal[result] = false;
    d_isConstant[result] = t.isConst();
  } else {
    // Otherwise we just create the new id
    result = newNode(t);
    d_isInternal[result] = false;
    d_isConstant[result] = t.isConst();
  }

  if (t.getType().isBoolean()) {
    // We set this here as this only applies to actual terms, not the
    // intermediate application terms
    d_isBoolean[result] = true;
  } else if (t.isConst()) {
    // Non-Boolean constants are trigger terms for all tags
    EqualityNodeId tId = getNodeId(t);
    d_newSetTags = 0;
    d_newSetTriggersSize = THEORY_LAST;
    for (TheoryId currentTheory = THEORY_FIRST; currentTheory != THEORY_LAST; ++ currentTheory) {
      d_newSetTags = Theory::setInsert(currentTheory, d_newSetTags);
      d_newSetTriggers[currentTheory] = tId;
    } 
    // Add it to the list for backtracking
    d_triggerTermSetUpdates.push_back(TriggerSetUpdate(tId, null_set_id));
    d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
    // Mark the the new set as a trigger 
    d_nodeIndividualTrigger[tId] = newTriggerTermSet();
  }

  propagate();

  Debug("equality") << d_name << "::eq::addTerm(" << t << ") => " << result << std::endl;
}

bool EqualityEngine::hasTerm(TNode t) const {
  return d_nodeIds.find(t) != d_nodeIds.end();
}

EqualityNodeId EqualityEngine::getNodeId(TNode node) const {
  Assert(hasTerm(node), node.toString().c_str());
  return (*d_nodeIds.find(node)).second;
}

EqualityNode& EqualityEngine::getEqualityNode(TNode t) {
  return getEqualityNode(getNodeId(t));
}

EqualityNode& EqualityEngine::getEqualityNode(EqualityNodeId nodeId) {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

const EqualityNode& EqualityEngine::getEqualityNode(TNode t) const {
  return getEqualityNode(getNodeId(t));
}

const EqualityNode& EqualityEngine::getEqualityNode(EqualityNodeId nodeId) const {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

void EqualityEngine::assertEqualityInternal(TNode t1, TNode t2, TNode reason) {

  Debug("equality") << d_name << "::eq::addEqualityInternal(" << t1 << "," << t2 << ")" << std::endl;

  if (d_done) {
    return;
  }

  // Add the terms if they are not already in the database
  addTerm(t1);
  addTerm(t2);

  // Add to the queue and propagate
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);
  enqueue(MergeCandidate(t1Id, t2Id, MERGED_THROUGH_EQUALITY, reason));
}

void EqualityEngine::assertPredicate(TNode t, bool polarity, TNode reason) {
  Debug("equality") << d_name << "::eq::addPredicate(" << t << "," << (polarity ? "true" : "false") << ")" << std::endl;
  Assert(t.getKind() != kind::EQUAL, "Use assertEquality instead");
  assertEqualityInternal(t, polarity ? d_true : d_false, reason);
  propagate();
}

void EqualityEngine::mergePredicates(TNode p, TNode q, TNode reason) {
  Debug("equality") << d_name << "::eq::mergePredicats(" << p << "," << q << ")" << std::endl;
  assertEqualityInternal(p, q, reason);
  propagate();
}

void EqualityEngine::assertEquality(TNode eq, bool polarity, TNode reason) {
  Debug("equality") << d_name << "::eq::addEquality(" << eq << "," << (polarity ? "true" : "false") << ")" << std::endl;
  if (polarity) {
    // If two terms are already equal, don't assert anything
    if (hasTerm(eq[0]) && hasTerm(eq[1]) && areEqual(eq[0], eq[1])) {
      return;
    }
    // Add equality between terms
    assertEqualityInternal(eq[0], eq[1], reason);
    propagate();
  } else {
    // If two terms are already dis-equal, don't assert anything
    if (hasTerm(eq[0]) && hasTerm(eq[1]) && areDisequal(eq[0], eq[1], false)) {
      return;
    }

    // notify the theory
    if (d_performNotify) {
      d_notify.eqNotifyDisequal(eq[0], eq[1], reason);
    }

    Debug("equality::trigger") << d_name << "::eq::addEquality(" << eq << "," << (polarity ? "true" : "false") << ")" << std::endl;

    assertEqualityInternal(eq, d_false, reason);
    propagate();    
  
    if (d_done) {
      return;
    }
  
    // If both have constant representatives, we don't notify anyone
    EqualityNodeId a = getNodeId(eq[0]);
    EqualityNodeId b = getNodeId(eq[1]);
    EqualityNodeId aClassId = getEqualityNode(a).getFind();
    EqualityNodeId bClassId = getEqualityNode(b).getFind();
    if (d_isConstant[aClassId] && d_isConstant[bClassId]) {
      return;
    }    
    
    // If we are adding a disequality, notify of the shared term representatives
    EqualityNodeId eqId = getNodeId(eq);
    TriggerTermSetRef aTriggerRef = d_nodeIndividualTrigger[aClassId];
    TriggerTermSetRef bTriggerRef = d_nodeIndividualTrigger[bClassId];
    if (aTriggerRef != +null_set_id && bTriggerRef != +null_set_id) {
      Debug("equality::trigger") << d_name << "::eq::addEquality(" << eq << "," << (polarity ? "true" : "false") << ": have triggers" << std::endl;
      // The sets of trigger terms
      TriggerTermSet& aTriggerTerms = getTriggerTermSet(aTriggerRef);
      TriggerTermSet& bTriggerTerms = getTriggerTermSet(bTriggerRef);
      // Go through and notify the shared dis-equalities 
      Theory::Set aTags = aTriggerTerms.tags;           
      Theory::Set bTags = bTriggerTerms.tags;           
      TheoryId aTag = Theory::setPop(aTags);
      TheoryId bTag = Theory::setPop(bTags);
      int a_i = 0, b_i = 0;
      while (aTag != THEORY_LAST && bTag != THEORY_LAST) {
        if (aTag < bTag) {
          aTag = Theory::setPop(aTags);
          ++ a_i;                  
        } else if (aTag > bTag) {
          bTag = Theory::setPop(bTags);
          ++ b_i;
        } else {
          // Same tags, notify
          EqualityNodeId aSharedId = aTriggerTerms.triggers[a_i++];
          EqualityNodeId bSharedId = bTriggerTerms.triggers[b_i++];
          // Propagate
          if (!hasPropagatedDisequality(aTag, aSharedId, bSharedId)) {
            // Store a proof if not there already
            if (!hasPropagatedDisequality(aSharedId, bSharedId)) {
              d_deducedDisequalityReasons.push_back(EqualityPair(aSharedId, a));
              d_deducedDisequalityReasons.push_back(EqualityPair(bSharedId, b));
              d_deducedDisequalityReasons.push_back(EqualityPair(eqId, d_falseId));
            }
            // Store the propagation
            storePropagatedDisequality(aTag, aSharedId, bSharedId);
            // Notify
            Debug("equality::trigger") << d_name << "::eq::addEquality(" << eq << "," << (polarity ? "true" : "false") << ": notifying " << aTag << " for " << d_nodes[aSharedId] << " != " << d_nodes[bSharedId] << std::endl;
            if (!d_notify.eqNotifyTriggerTermEquality(aTag, d_nodes[aSharedId], d_nodes[bSharedId], false)) {
              break;
            }
          }
          // Pop the next tags
          aTag = Theory::setPop(aTags);
          bTag = Theory::setPop(bTags);
        }
      }
    }
  }
}

TNode EqualityEngine::getRepresentative(TNode t) const {
  Debug("equality::internal") << d_name << "::eq::getRepresentative(" << t << ")" << std::endl;
  Assert(hasTerm(t));
  EqualityNodeId representativeId = getEqualityNode(t).getFind();
  Debug("equality::internal") << d_name << "::eq::getRepresentative(" << t << ") => " << d_nodes[representativeId] << std::endl;
  return d_nodes[representativeId];
}

bool EqualityEngine::merge(EqualityNode& class1, EqualityNode& class2, std::vector<TriggerId>& triggersFired) {

  Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << ")" << std::endl;

  Assert(triggersFired.empty());
  
  ++ d_stats.mergesCount;

  EqualityNodeId class1Id = class1.getFind();
  EqualityNodeId class2Id = class2.getFind();

  Node n1 = d_nodes[class1Id];
  Node n2 = d_nodes[class2Id];
  EqualityNode cc1 = getEqualityNode(n1);
  EqualityNode cc2 = getEqualityNode(n2);
  bool doNotify = false;
  // notify the theory
  // the second part of this check is needed due to the internal implementation of this class.
  // It ensures that we are merging terms and not operators.
  if (d_performNotify && class1Id==cc1.getFind() && class2Id==cc2.getFind()) {
    doNotify = true;
  }
  if (doNotify) {
    d_notify.eqNotifyPreMerge(n1, n2);
  }

  // Check for constant merges
  bool class1isConstant = d_isConstant[class1Id];
  bool class2isConstant = d_isConstant[class2Id];
  Assert(class1isConstant || !class2isConstant, "Should always merge into constants");
  Assert(!class1isConstant || !class2isConstant, "Don't merge constants");

  // Trigger set of class 1
  TriggerTermSetRef class1triggerRef = d_nodeIndividualTrigger[class1Id];
  Theory::Set class1Tags = class1triggerRef == null_set_id ? 0 : getTriggerTermSet(class1triggerRef).tags;
  // Trigger set of class 2
  TriggerTermSetRef class2triggerRef = d_nodeIndividualTrigger[class2Id];
  Theory::Set class2Tags = class2triggerRef == null_set_id ? 0 : getTriggerTermSet(class2triggerRef).tags;

  // Disequalities coming from class2
  TaggedEqualitiesSet class2disequalitiesToNotify;
  // Disequalities coming from class1
  TaggedEqualitiesSet class1disequalitiesToNotify;

  // Individual tags
  Theory::Set class1OnlyTags = Theory::setDifference(class1Tags, class2Tags); 
  Theory::Set class2OnlyTags = Theory::setDifference(class2Tags, class1Tags); 

  // Only get disequalities if they are not both constant
  if (!class1isConstant || !class2isConstant) {
    getDisequalities(!class1isConstant, class2Id, class1OnlyTags, class2disequalitiesToNotify);
    getDisequalities(!class2isConstant, class1Id, class2OnlyTags, class1disequalitiesToNotify);
  }

  // Update class2 representative information
  Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): updating class " << class2Id << std::endl;
  EqualityNodeId currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): " << currentId << "->" << class1Id << std::endl;
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
          triggersFired.push_back(currentTrigger);
        }
      }

      // Go to the next trigger
      currentTrigger = trigger.nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Update class2 table lookup and information if not a boolean
  // since booleans can't be in an application
  if (!d_isBoolean[class2Id]) {
    Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of " << class2Id << std::endl;
    do {
      // Get the current node
      EqualityNode& currentNode = getEqualityNode(currentId);    
      Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of node " << currentId << std::endl;
 
      // Go through the uselist and check for congruences
      UseListNodeId currentUseId = currentNode.getUseList();
      while (currentUseId != null_uselist_id) {
        // Get the node of the use list
        UseListNode& useNode = d_useListNodes[currentUseId];
        // Get the function application
        EqualityNodeId funId = useNode.getApplicationId();
        Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): " << d_nodes[currentId] << " in " << d_nodes[funId] << std::endl;
        const FunctionApplication& fun = d_applications[useNode.getApplicationId()].normalized;
        // Check if there is an application with find arguments
        EqualityNodeId aNormalized = getEqualityNode(fun.a).getFind();
        EqualityNodeId bNormalized = getEqualityNode(fun.b).getFind();
        FunctionApplication funNormalized(fun.isEquality, aNormalized, bNormalized);
        ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
        if (find != d_applicationLookup.end()) {
          // Applications fun and the funNormalized can be merged due to congruence
          if (getEqualityNode(funId).getFind() != getEqualityNode(find->second).getFind()) {
            enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
          }
        } else {
          // There is no representative, so we can add one, we remove this when backtracking
          storeApplicationLookup(funNormalized, funId);
          // Note: both checks below we don't need to do in the above case as the normalized lookup
          //       has already been checked for this
          // Now, if we're constant and it's an equality, check if the other guy is also a constant
          if (fun.isEquality) {
            // If the equation normalizes to two constants, it's disequal
            if (d_isConstant[aNormalized] && d_isConstant[bNormalized] && aNormalized != bNormalized) {
              Assert(d_nodes[funId].getKind() == kind::EQUAL);
              enqueue(MergeCandidate(funId, d_falseId, MERGED_THROUGH_CONSTANTS, TNode::null()), false);
              // Also enqueue the symmetric one
              TNode eq = d_nodes[funId];
              Node symmetricEq = eq[1].eqNode(eq[0]);
              if (hasTerm(symmetricEq)) {
                EqualityNodeId symmFunId = getNodeId(symmetricEq);
                enqueue(MergeCandidate(symmFunId, d_falseId, MERGED_THROUGH_CONSTANTS, TNode::null()), false);              
              }
            }
            // If the function normalizes to a = a, we merge it with true, we check that its not
            // already there so as not to enqueue multiple times when several things get merged
            if (aNormalized == bNormalized && getEqualityNode(funId).getFind() != d_trueId) {
              enqueue(MergeCandidate(funId, d_trueId, MERGED_THROUGH_REFLEXIVITY, TNode::null()), false);                            
            } 
          }
        }
                  
        // Go to the next one in the use list
        currentUseId = useNode.getNext();
      }
  
      // Move to the next node
      currentId = currentNode.getNext();
    } while (currentId != class2Id);
  }
    
  // Now merge the lists
  class1.merge<true>(class2);

  // notify the theory
  if (doNotify) {
    d_notify.eqNotifyPostMerge(n1, n2);
  }

  // Go through the trigger term disequalities and propagate
  if (!propagateTriggerTermDisequalities(class1OnlyTags, class1triggerRef, class2disequalitiesToNotify)) {
    return false;
  }
  if (!propagateTriggerTermDisequalities(class2OnlyTags, class2triggerRef, class1disequalitiesToNotify)) {
    return false;
  }

  // Notify the trigger term merges
  if (class2triggerRef != +null_set_id) {
    if (class1triggerRef == +null_set_id) {
      // If class1 doesn't have individual triggers, but class2 does, mark it
      d_nodeIndividualTrigger[class1Id] = class2triggerRef;
      // Add it to the list for backtracking
      d_triggerTermSetUpdates.push_back(TriggerSetUpdate(class1Id, +null_set_id));
      d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
    } else {
      // Get the triggers
      TriggerTermSet& class1triggers = getTriggerTermSet(class1triggerRef);
      TriggerTermSet& class2triggers = getTriggerTermSet(class2triggerRef);
      
      // Initialize the merged set
      d_newSetTags = Theory::setUnion(class1triggers.tags, class2triggers.tags);
      d_newSetTriggersSize = 0;
      
      int i1 = 0;
      int i2 = 0;
      Theory::Set tags1 = class1triggers.tags;
      Theory::Set tags2 = class2triggers.tags;
      TheoryId tag1 = Theory::setPop(tags1);
      TheoryId tag2 = Theory::setPop(tags2);
      
      // Comparing the THEORY_LAST is OK because all other theories are
      // smaller, and will therefore be preferred
      while (tag1 != THEORY_LAST || tag2 != THEORY_LAST) 
      {
        if (tag1 < tag2) {
          // copy tag1 
          d_newSetTriggers[d_newSetTriggersSize++] = class1triggers.triggers[i1++];
          tag1 = Theory::setPop(tags1);
        } else if (tag1 > tag2) {
          // copy tag2
          d_newSetTriggers[d_newSetTriggersSize++] = class2triggers.triggers[i2++];
          tag2 = Theory::setPop(tags2);
        } else {
          // copy tag1 
          EqualityNodeId tag1id = d_newSetTriggers[d_newSetTriggersSize++] = class1triggers.triggers[i1++];
          // since they are both tagged notify of merge
          if (d_performNotify) {
            EqualityNodeId tag2id = class2triggers.triggers[i2++];
            if (!d_notify.eqNotifyTriggerTermEquality(tag1, d_nodes[tag1id], d_nodes[tag2id], true)) {
              return false;
            }
          }
          // Next tags
          tag1 = Theory::setPop(tags1);
          tag2 = Theory::setPop(tags2);
        }
      }   
      
      // Add the new trigger set, if different from previous one
      if (class1triggers.tags != class2triggers.tags) {
        // Add it to the list for backtracking
        d_triggerTermSetUpdates.push_back(TriggerSetUpdate(class1Id, class1triggerRef));
        d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
        // Mark the the new set as a trigger 
        d_nodeIndividualTrigger[class1Id] = newTriggerTermSet();
      }  
    }	
  }

  // Everything fine
  return true;
}

void EqualityEngine::undoMerge(EqualityNode& class1, EqualityNode& class2, EqualityNodeId class2Id) {

  Debug("equality") << d_name << "::eq::undoMerge(" << class1.getFind() << "," << class2Id << ")" << std::endl;

  // Now unmerge the lists (same as merge)
  class1.merge<false>(class2);

  // Update class2 representative information
  EqualityNodeId currentId = class2Id;
  Debug("equality") << d_name << "::eq::undoMerge(" << class1.getFind() << "," << class2Id << "): undoing representative info" << std::endl;
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

}

void EqualityEngine::backtrack() {

  Debug("equality::backtrack") << "backtracking" << std::endl;

  // If we need to backtrack then do it
  if (d_assertedEqualitiesCount < d_assertedEqualities.size()) {

    // Clear the propagation queue
    while (!d_propagationQueue.empty()) {
      d_propagationQueue.pop_front();
    }

    Debug("equality") << d_name << "::eq::backtrack(): nodes" << std::endl;

    for (int i = (int)d_assertedEqualities.size() - 1, i_end = (int)d_assertedEqualitiesCount; i >= i_end; --i) {
      // Get the ids of the merged classes
      Equality& eq = d_assertedEqualities[i];
      // Undo the merge
      if (eq.lhs != null_id) {
        undoMerge(d_equalityNodes[eq.lhs], d_equalityNodes[eq.rhs], eq.rhs);
      }
    }

    d_assertedEqualities.resize(d_assertedEqualitiesCount);

    Debug("equality") << d_name << "::eq::backtrack(): edges" << std::endl;

    for (int i = (int)d_equalityEdges.size() - 2, i_end = (int)(2*d_assertedEqualitiesCount); i >= i_end; i -= 2) {
      EqualityEdge& edge1 = d_equalityEdges[i];
      EqualityEdge& edge2 = d_equalityEdges[i | 1];
      d_equalityGraph[edge2.getNodeId()] = edge1.getNext();
      d_equalityGraph[edge1.getNodeId()] = edge2.getNext();
    }

    d_equalityEdges.resize(2 * d_assertedEqualitiesCount);
  }

  if (d_triggerTermSetUpdates.size() > d_triggerTermSetUpdatesSize) {
    // Unset the individual triggers
    for (int i = d_triggerTermSetUpdates.size() - 1, i_end = d_triggerTermSetUpdatesSize; i >= i_end; -- i) {
      const TriggerSetUpdate& update = d_triggerTermSetUpdates[i];
      d_nodeIndividualTrigger[update.classId] = update.oldValue;
    }
    d_triggerTermSetUpdates.resize(d_triggerTermSetUpdatesSize);
  }
  
  if (d_equalityTriggers.size() > d_equalityTriggersCount) {
    // Unlink the triggers from the lists
    for (int i = d_equalityTriggers.size() - 1, i_end = d_equalityTriggersCount; i >= i_end; -- i) {
      const Trigger& trigger = d_equalityTriggers[i];
      d_nodeTriggers[trigger.classId] = trigger.nextTrigger;
    }
    // Get rid of the triggers 
    d_equalityTriggers.resize(d_equalityTriggersCount);
    d_equalityTriggersOriginal.resize(d_equalityTriggersCount);
  }

  if (d_applicationLookups.size() > d_applicationLookupsCount) {
    for (int i = d_applicationLookups.size() - 1, i_end = (int) d_applicationLookupsCount; i >= i_end; -- i) {
      d_applicationLookup.erase(d_applicationLookups[i]);
    }
    d_applicationLookups.resize(d_applicationLookupsCount);
  }

  if (d_nodes.size() > d_nodesCount) {
    // Go down the nodes, check the application nodes and remove them from use-lists
    for(int i = d_nodes.size() - 1, i_end = (int)d_nodesCount; i >= i_end; -- i) {
      // Remove from the node -> id map
      Debug("equality") << d_name << "::eq::backtrack(): removing node " << d_nodes[i] << std::endl;
      d_nodeIds.erase(d_nodes[i]);

      const FunctionApplication& app = d_applications[i].original;
      if (app.isApplication()) {
        // Remove b from use-list
        getEqualityNode(app.b).removeTopFromUseList(d_useListNodes);
        // Remove a from use-list
        getEqualityNode(app.a).removeTopFromUseList(d_useListNodes);
      }
    }

    // Now get rid of the nodes and the rest
    d_nodes.resize(d_nodesCount);
    d_applications.resize(d_nodesCount);
    d_nodeTriggers.resize(d_nodesCount);
    d_nodeIndividualTrigger.resize(d_nodesCount);
    d_isConstant.resize(d_nodesCount);
    d_isBoolean.resize(d_nodesCount);
    d_isInternal.resize(d_nodesCount);
    d_equalityGraph.resize(d_nodesCount);
    d_equalityNodes.resize(d_nodesCount);
  }

  if (d_deducedDisequalities.size() > d_deducedDisequalitiesSize) {
    for(int i = d_deducedDisequalities.size() - 1, i_end = (int)d_deducedDisequalitiesSize; i >= i_end; -- i) {
      EqualityPair pair = d_deducedDisequalities[i];
      Assert(d_disequalityReasonsMap.find(pair) != d_disequalityReasonsMap.end());
      // Remove from the map
      d_disequalityReasonsMap.erase(pair);
      std::swap(pair.first, pair.second);
      d_disequalityReasonsMap.erase(pair);
    }
    d_deducedDisequalityReasons.resize(d_deducedDisequalityReasonsSize);
    d_deducedDisequalities.resize(d_deducedDisequalitiesSize);
  }
}

void EqualityEngine::addGraphEdge(EqualityNodeId t1, EqualityNodeId t2, MergeReasonType type, TNode reason) {
  Debug("equality") << d_name << "::eq::addGraphEdge(" << d_nodes[t1] << "," << d_nodes[t2] << "," << reason << ")" << std::endl;
  EqualityEdgeId edge = d_equalityEdges.size();
  d_equalityEdges.push_back(EqualityEdge(t2, d_equalityGraph[t1], type, reason));
  d_equalityEdges.push_back(EqualityEdge(t1, d_equalityGraph[t2], type, reason));
  d_equalityGraph[t1] = edge;
  d_equalityGraph[t2] = edge | 1;

  if (Debug.isOn("equality::internal")) {
    debugPrintGraph();
  }
}

std::string EqualityEngine::edgesToString(EqualityEdgeId edgeId) const {
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

void EqualityEngine::explainEquality(TNode t1, TNode t2, bool polarity, std::vector<TNode>& equalities) const {
  Debug("equality") << d_name << "::eq::explainEquality(" << t1 << ", " << t2 << ", " << (polarity ? "true" : "false") << ")" << std::endl;

  // The terms must be there already
  Assert(hasTerm(t1) && hasTerm(t2));;

  // Get the ids
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);

  if (polarity) {
    // Get the explanation
    getExplanation(t1Id, t2Id, equalities);
  } else {
    // Get the reason for this disequality
    EqualityPair pair(t1Id, t2Id);
    Assert(d_disequalityReasonsMap.find(pair) != d_disequalityReasonsMap.end(), "Don't ask for stuff I didn't notify you about");
    DisequalityReasonRef reasonRef = d_disequalityReasonsMap.find(pair)->second;
    for (unsigned i = reasonRef.mergesStart; i < reasonRef.mergesEnd; ++ i) {
      EqualityPair toExplain = d_deducedDisequalityReasons[i];
      getExplanation(toExplain.first, toExplain.second, equalities);
    }
  }
}

void EqualityEngine::explainPredicate(TNode p, bool polarity, std::vector<TNode>& assertions) const {
  Debug("equality") << d_name << "::eq::explainPredicate(" << p << ")" << std::endl;
  // Must have the term
  Assert(hasTerm(p));
  // Get the explanation
  getExplanation(getNodeId(p), polarity ? d_trueId : d_falseId, assertions);
}

void EqualityEngine::getExplanation(EqualityNodeId t1Id, EqualityNodeId t2Id, std::vector<TNode>& equalities) const {

  Debug("equality") << d_name << "::eq::getExplanation(" << d_nodes[t1Id] << "," << d_nodes[t2Id] << ")" << std::endl;

  // We can only explain the nodes that got merged
#ifdef CVC4_ASSERTIONS
  bool canExplain = getEqualityNode(t1Id).getFind() == getEqualityNode(t2Id).getFind()
                  || (d_done && isConstant(t1Id) && isConstant(t2Id));
  
  if (!canExplain) {
    Warning() << "Can't explain equality:" << std::endl;
    Warning() << d_nodes[t1Id] << " with find " << d_nodes[getEqualityNode(t1Id).getFind()] << std::endl;
    Warning() << d_nodes[t2Id] << " with find " << d_nodes[getEqualityNode(t2Id).getFind()] << std::endl;    
  }
  Assert(canExplain);
#endif

  // If the nodes are the same, we're done
  if (t1Id == t2Id) return;

  if (Debug.isOn("equality::internal")) {
    debugPrintGraph();
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

    Debug("equality") << d_name << "::eq::getExplanation(): currentNode =  " << d_nodes[currentNode] << std::endl;

    // Go through the equality edges of this node
    EqualityEdgeId currentEdge = d_equalityGraph[currentNode];
    if (Debug.isOn("equality")) {
      Debug("equality") << d_name << "::eq::getExplanation(): edgesId =  " << currentEdge << std::endl;
      Debug("equality") << d_name << "::eq::getExplanation(): edges =  " << edgesToString(currentEdge) << std::endl;
    }

    while (currentEdge != null_edge) {
      // Get the edge
      const EqualityEdge& edge = d_equalityEdges[currentEdge];

      // If not just the backwards edge
      if ((currentEdge | 1u) != (current.edgeId | 1u)) {

        Debug("equality") << d_name << "::eq::getExplanation(): currentEdge = (" << d_nodes[currentNode] << "," << d_nodes[edge.getNodeId()] << ")" << std::endl;

        // Did we find the path
        if (edge.getNodeId() == t2Id) {

          Debug("equality") << d_name << "::eq::getExplanation(): path found: " << std::endl;

          // Reconstruct the path
          do {
            // The current node
            currentNode = bfsQueue[currentIndex].nodeId;
            EqualityNodeId edgeNode = d_equalityEdges[currentEdge].getNodeId();
            MergeReasonType reasonType = d_equalityEdges[currentEdge].getReasonType();

            Debug("equality") << d_name << "::eq::getExplanation(): currentEdge = " << currentEdge << ", currentNode = " << currentNode << std::endl;

            // Add the actual equality to the vector
            switch (reasonType) {
            case MERGED_THROUGH_CONGRUENCE: {
              // f(x1, x2) == f(y1, y2) because x1 = y1 and x2 = y2
              Debug("equality") << d_name << "::eq::getExplanation(): due to congruence, going deeper" << std::endl;
              const FunctionApplication& f1 = d_applications[currentNode].original;
              const FunctionApplication& f2 = d_applications[edgeNode].original;
              Debug("equality") << push;
              getExplanation(f1.a, f2.a, equalities);
              getExplanation(f1.b, f2.b, equalities);
              Debug("equality") << pop;
              break;
            } 
            case MERGED_THROUGH_EQUALITY:
              // Construct the equality
              Debug("equality") << d_name << "::eq::getExplanation(): adding: " << d_equalityEdges[currentEdge].getReason() << std::endl;
              equalities.push_back(d_equalityEdges[currentEdge].getReason());
              break;
            case MERGED_THROUGH_REFLEXIVITY: {
              // f(x1, x2) == f(y1, y2) because x1 = y1 and x2 = y2
              Debug("equality") << d_name << "::eq::getExplanation(): due to reflexivity, going deeper" << std::endl;
              EqualityNodeId eqId = currentNode == d_trueId ? edgeNode : currentNode;
              const FunctionApplication& eq = d_applications[eqId].original;
              Assert(eq.isEquality, "Must be an equality");
              
              // Explain why a = b constant
              Debug("equality") << push;
              getExplanation(eq.a, eq.b, equalities);
              Debug("equality") << pop;
              
              break;              
            }
            case MERGED_THROUGH_CONSTANTS: {
              // (a = b) == false because a and b are different constants
              Debug("equality") << d_name << "::eq::getExplanation(): due to constants, going deeper" << std::endl;
              EqualityNodeId eqId = currentNode == d_falseId ? edgeNode : currentNode;
              const FunctionApplication& eq = d_applications[eqId].original;
              Assert(eq.isEquality, "Must be an equality");
              
              Debug("equality") << push;
              // Explain why a is a constant
              Assert(isConstant(eq.a));
              getExplanation(eq.a, getEqualityNode(eq.a).getFind(), equalities);
              // Explain why b is a constant
              Assert(isConstant(eq.b));
              getExplanation(eq.b, getEqualityNode(eq.b).getFind(), equalities);
              Debug("equality") << pop;
              // If the constants were merged, we're in trouble
              Assert(getEqualityNode(eq.a).getFind() != getEqualityNode(eq.b).getFind());

              break;
            }
            default:
              Unreachable();
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

void EqualityEngine::addTriggerEquality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL);

  if (d_done) {
    return;
  }

  // Add the terms
  addTerm(eq[0]);
  addTerm(eq[1]);

  bool skipTrigger = false;

  // If they are equal or disequal already, no need for the trigger
  if (areEqual(eq[0], eq[1])) {
    d_notify.eqNotifyTriggerEquality(eq, true);
    skipTrigger = true;
  }
  if (areDisequal(eq[0], eq[1], true)) {
    d_notify.eqNotifyTriggerEquality(eq, false);
    skipTrigger = true;
  }

  if (skipTrigger) {
    return;
  }

  // Add the equality
  addTerm(eq);

  // Positive trigger
  addTriggerEqualityInternal(eq[0], eq[1], eq, true);
  // Negative trigger
  addTriggerEqualityInternal(eq, d_false, eq, false);
}

void EqualityEngine::addTriggerPredicate(TNode predicate) {
  Assert(predicate.getKind() != kind::NOT && predicate.getKind() != kind::EQUAL);
  Assert(d_congruenceKinds.tst(predicate.getKind()), "No point in adding non-congruence predicates");

  if (d_done) {
    return;
  }

  // Add the term
  addTerm(predicate);

  bool skipTrigger = false;

  // If it's know already, no need for the trigger
  if (areEqual(predicate, d_true)) {
    d_notify.eqNotifyTriggerPredicate(predicate, true);
    skipTrigger = true;
  }
  if (areEqual(predicate, d_false)) {
    d_notify.eqNotifyTriggerPredicate(predicate, false);
    skipTrigger = true;
  }

  if (skipTrigger) {
    return;
  }

  // Positive trigger
  addTriggerEqualityInternal(predicate, d_true, predicate, true);
  // Negative trigger
  addTriggerEqualityInternal(predicate, d_false, predicate, false);
}

void EqualityEngine::addTriggerEqualityInternal(TNode t1, TNode t2, TNode trigger, bool polarity) {

  Debug("equality") << d_name << "::eq::addTrigger(" << t1 << ", " << t2 << ", " << trigger << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  if (d_done) {
    return;
  }

  // Get the information about t1
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t1classId = getEqualityNode(t1Id).getFind();
  // We will attach it to the class representative, since then we know how to backtrack it
  TriggerId t1TriggerId = d_nodeTriggers[t1classId];

  // Get the information about t2
  EqualityNodeId t2Id = getNodeId(t2);
  EqualityNodeId t2classId = getEqualityNode(t2Id).getFind();
  // We will attach it to the class representative, since then we know how to backtrack it
  TriggerId t2TriggerId = d_nodeTriggers[t2classId];

  Debug("equality") << d_name << "::eq::addTrigger(" << trigger << "): " << t1Id << " (" << t1classId << ") = " << t2Id << " (" << t2classId << ")" << std::endl;

  // Create the triggers
  TriggerId t1NewTriggerId = d_equalityTriggers.size();
  d_equalityTriggers.push_back(Trigger(t1classId, t1TriggerId));
  d_equalityTriggersOriginal.push_back(TriggerInfo(trigger, polarity));
  TriggerId t2NewTriggerId = d_equalityTriggers.size();
  d_equalityTriggers.push_back(Trigger(t2classId, t2TriggerId));
  d_equalityTriggersOriginal.push_back(TriggerInfo(trigger, polarity));

  // Update the counters
  d_equalityTriggersCount = d_equalityTriggers.size();
  Assert(d_equalityTriggers.size() == d_equalityTriggersOriginal.size());
  Assert(d_equalityTriggers.size() % 2 == 0);

  // Add the trigger to the trigger graph
  d_nodeTriggers[t1classId] = t1NewTriggerId;
  d_nodeTriggers[t2classId] = t2NewTriggerId;

  if (Debug.isOn("equality::internal")) {
    debugPrintGraph();
  }

  Debug("equality") << d_name << "::eq::addTrigger(" << t1 << "," << t2 << ") => (" << t1NewTriggerId << ", " << t2NewTriggerId << ")" << std::endl;
}

void EqualityEngine::propagate() {

  Debug("equality") << d_name << "::eq::propagate()" << std::endl;

  while (!d_propagationQueue.empty()) {

    // The current merge candidate
    const MergeCandidate current = d_propagationQueue.front();
    d_propagationQueue.pop_front();

    if (d_done) {
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

    Debug("equality::internal") << d_name << "::eq::propagate(): t1: " << (d_isInternal[t1classId] ? "internal" : "proper") << std::endl;
    Debug("equality::internal") << d_name << "::eq::propagate(): t2: " << (d_isInternal[t2classId] ? "internal" : "proper") << std::endl;

    // Get the nodes of the representatives
    EqualityNode& node1 = getEqualityNode(t1classId);
    EqualityNode& node2 = getEqualityNode(t2classId);

    Assert(node1.getFind() == t1classId);
    Assert(node2.getFind() == t2classId);

    // Add the actual equality to the equality graph
    addGraphEdge(current.t1Id, current.t2Id, current.type, current.reason);

    // If constants are being merged we're done 
    if (d_isConstant[t1classId] && d_isConstant[t2classId]) {
      // When merging constants we are inconsistent, hence done
      d_done = true;
      // But in order to keep invariants (edges = 2*equalities) we put an equalities in
      // Note that we can explain this merge as we have a graph edge
      d_assertedEqualities.push_back(Equality(null_id, null_id));
      d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;
      // Notify
      if (d_performNotify) {
        d_notify.eqNotifyConstantTermMerge(d_nodes[t1classId], d_nodes[t2classId]);
      }
      // Empty the queue and exit
      continue;
    }

    // Depending on the merge preference (such as size, or being a constant), merge them
    std::vector<TriggerId> triggers;
    if ((node2.getSize() > node1.getSize() && !d_isConstant[t1classId]) || d_isConstant[t2classId]) {
      Debug("equality") << d_name << "::eq::propagate(): merging " << d_nodes[current.t1Id]<< " into " << d_nodes[current.t2Id] << std::endl;
      d_assertedEqualities.push_back(Equality(t2classId, t1classId));
      d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;
      if (!merge(node2, node1, triggers)) {
        d_done = true;
      }
    } else {
      Debug("equality") << d_name << "::eq::propagate(): merging " << d_nodes[current.t2Id] << " into " << d_nodes[current.t1Id] << std::endl;
      d_assertedEqualities.push_back(Equality(t1classId, t2classId));
      d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;
    if (!merge(node1, node2, triggers)) {
        d_done = true;
      }
    }

    // Notify the triggers
    if (d_performNotify && !d_done) {
      for (size_t trigger_i = 0, trigger_end = triggers.size(); trigger_i < trigger_end && !d_done; ++ trigger_i) {
        const TriggerInfo& triggerInfo = d_equalityTriggersOriginal[triggers[trigger_i]];
        if (triggerInfo.trigger.getKind() == kind::EQUAL) {
          // Special treatment for disequalities
          if (!triggerInfo.polarity) {
            // Store that we are propagating a diseauality
            TNode equality = triggerInfo.trigger;
            EqualityNodeId original = getNodeId(equality);
            TNode lhs = equality[0];
            TNode rhs = equality[1];
            EqualityNodeId lhsId = getNodeId(lhs);
            EqualityNodeId rhsId = getNodeId(rhs);
            if (!hasPropagatedDisequality(THEORY_BOOL, lhsId, rhsId)) {
              if (!hasPropagatedDisequality(lhsId, rhsId)) {
                d_deducedDisequalityReasons.push_back(EqualityPair(original, d_falseId));
              }
              storePropagatedDisequality(THEORY_BOOL, lhsId, rhsId);
              if (!d_notify.eqNotifyTriggerEquality(triggerInfo.trigger, triggerInfo.polarity)) {
                d_done = true;
              }
            }
          } else {
            // Equalities are simple
            if (!d_notify.eqNotifyTriggerEquality(triggerInfo.trigger, triggerInfo.polarity)) {
              d_done = true;
            }
          }
        } else {
          if (!d_notify.eqNotifyTriggerPredicate(triggerInfo.trigger, triggerInfo.polarity)) {
            d_done = true;
          }
        }
      }
    }
  }
}

void EqualityEngine::debugPrintGraph() const {
  for (EqualityNodeId nodeId = 0; nodeId < d_nodes.size(); ++ nodeId) {

    Debug("equality::graph") << d_nodes[nodeId] << " " << nodeId << "(" << getEqualityNode(nodeId).getFind() << "):";

    EqualityEdgeId edgeId = d_equalityGraph[nodeId];
    while (edgeId != null_edge) {
      const EqualityEdge& edge = d_equalityEdges[edgeId];
      Debug("equality::graph") << " " << d_nodes[edge.getNodeId()] << ":" << edge.getReason();
      edgeId = edge.getNext();
    }

    Debug("equality::graph") << std::endl;
  }
}

bool EqualityEngine::areEqual(TNode t1, TNode t2) const {
  Debug("equality") << d_name << "::eq::areEqual(" << t1 << "," << t2 << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  return getEqualityNode(t1).getFind() == getEqualityNode(t2).getFind();
}

bool EqualityEngine::areDisequal(TNode t1, TNode t2, bool ensureProof) const
{
  Debug("equality") << d_name << "::eq::areDisequal(" << t1 << "," << t2 << ")" << std::endl;

  // Add the terms
  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Get ids
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);

  // If we propagated this disequality we're true
  if (hasPropagatedDisequality(t1Id, t2Id)) {
    return true;
  }

  // Get equivalence classes
  EqualityNodeId t1ClassId = getEqualityNode(t1Id).getFind();
  EqualityNodeId t2ClassId = getEqualityNode(t2Id).getFind();

  // We are semantically const, for remembering stuff
  EqualityEngine* nonConst = const_cast<EqualityEngine*>(this);

  // Check for constants
  if (d_isConstant[t1ClassId] && d_isConstant[t2ClassId] && t1ClassId != t2ClassId) {
    if (ensureProof) {
      nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t1Id, t1ClassId));
      nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t2Id, t2ClassId));
      nonConst->storePropagatedDisequality(THEORY_LAST, t1Id, t2Id);
    }
    return true;
  }

  // Check the equality itself if it exists
  Node eq = t1.eqNode(t2);
  if (hasTerm(eq)) {
    if (getEqualityNode(eq).getFind() == getEqualityNode(d_falseId).getFind()) {
      if (ensureProof) {
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(getNodeId(eq), d_falseId));
        nonConst->storePropagatedDisequality(THEORY_LAST, t1Id, t2Id);
      }
      return true;
    }
  }
 
  // Check the other equality itself if it exists
  eq = t2.eqNode(t1);
  if (hasTerm(eq)) {
    if (getEqualityNode(eq).getFind() == getEqualityNode(d_false).getFind()) {
      if (ensureProof) {
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(getNodeId(eq), d_falseId));
        nonConst->storePropagatedDisequality(THEORY_LAST, t1Id, t2Id);
      }
      return true;
    }
  }
  
  // Create the equality
  FunctionApplication eqNormalized(true, t1ClassId, t2ClassId);
  ApplicationIdsMap::const_iterator find = d_applicationLookup.find(eqNormalized);
  if (find != d_applicationLookup.end()) {
    if (getEqualityNode(find->second).getFind() == getEqualityNode(d_falseId).getFind()) {
      if (ensureProof) {
        const FunctionApplication original = d_applications[find->second].original;
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t1Id, original.a));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t2Id, original.b));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(original.a, t1ClassId));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(original.b, t2ClassId));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(find->second, d_falseId));
        nonConst->storePropagatedDisequality(THEORY_LAST, t1Id, t2Id);
      }
      return true;
    }
  }
  
  // Check the symmetric disequality
  std::swap(eqNormalized.a, eqNormalized.b);
  find = d_applicationLookup.find(eqNormalized);
  if (find != d_applicationLookup.end()) {
    if (getEqualityNode(find->second).getFind() == getEqualityNode(d_falseId).getFind()) {
      if (ensureProof) {
        const FunctionApplication original = d_applications[find->second].original;
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t2Id, original.a));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t1Id, original.b));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(original.a, t2ClassId));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(original.b, t1ClassId));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(find->second, d_falseId));
        nonConst->storePropagatedDisequality(THEORY_LAST, t1Id, t2Id);
      }
      return true;
    }
  }
    
  // Couldn't deduce dis-equalityReturn whether the terms are disequal
  return false;
}

size_t EqualityEngine::getSize(TNode t)
{
  // Add the term
  addTerm(t);
  return getEqualityNode(getEqualityNode(t).getFind()).getSize();
}

void EqualityEngine::addTriggerTerm(TNode t, TheoryId tag)
{
  Debug("equality::trigger") << d_name << "::eq::addTriggerTerm(" << t << ", " << tag << ")" << std::endl;

  Assert(tag != THEORY_LAST);
  Assert(tag != THEORY_BOOL, "This one is used internally, bummer");

  if (d_done) {
    return;
  }

  // Add the term if it's not already there
  addTerm(t);

  // Get the node id
  EqualityNodeId eqNodeId = getNodeId(t);
  EqualityNode& eqNode = getEqualityNode(eqNodeId);
  EqualityNodeId classId = eqNode.getFind();

  // Possibly existing set of triggers
  TriggerTermSetRef triggerSetRef = d_nodeIndividualTrigger[classId];
  if (triggerSetRef != +null_set_id && getTriggerTermSet(triggerSetRef).hasTrigger(tag)) {
    // If the term already is in the equivalence class that a tagged representative, just notify
    if (d_performNotify) {
      EqualityNodeId triggerId = getTriggerTermSet(triggerSetRef).getTrigger(tag);
      Debug("equality::trigger") << d_name << "::eq::addTriggerTerm(" << t << ", " << tag << "): already have this trigger in class with " << d_nodes[triggerId] << std::endl;
      if (eqNodeId != triggerId && !d_notify.eqNotifyTriggerTermEquality(tag, t, d_nodes[triggerId], true)) {
        d_done = true;
      }
    }
  } else {

    // Check for disequalities by going through the equivalence class looking for equalities in the
    // uselists that have been asserted to false. All the representatives appearing on the other
    // side of such disequalities, that have the tag on, are put in a set.
    TaggedEqualitiesSet disequalitiesToNotify;
    Theory::Set tags = Theory::setInsert(tag);
    getDisequalities(!d_isConstant[classId], classId, tags, disequalitiesToNotify);

    // Setup the data for the new set
    if (triggerSetRef != null_set_id) {
      // Get the existing set
      TriggerTermSet& triggerSet = getTriggerTermSet(triggerSetRef);
      // Initialize the new set for copy/insert
      d_newSetTags = Theory::setInsert(tag, triggerSet.tags);
      d_newSetTriggersSize = 0;
      // Copy into to new one, and insert the new tag/id      
      unsigned i = 0;
      Theory::Set tags = d_newSetTags;
      TheoryId current; 
      while ((current = Theory::setPop(tags)) != THEORY_LAST) {
        // Remove from the tags
        tags = Theory::setRemove(current, tags);
        // Insert the id into the triggers
        d_newSetTriggers[d_newSetTriggersSize++] = 
          current == tag ? eqNodeId : triggerSet.triggers[i++];
      }
    } else {
      // Setup a singleton 
      d_newSetTags = Theory::setInsert(tag);
      d_newSetTriggers[0] = eqNodeId;
      d_newSetTriggersSize = 1;
    }

    // Add it to the list for backtracking
    d_triggerTermSetUpdates.push_back(TriggerSetUpdate(classId, triggerSetRef));
    d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
    // Mark the the new set as a trigger 
    d_nodeIndividualTrigger[classId] = triggerSetRef = newTriggerTermSet();

    // Propagate trigger term disequalities we remembered
    Debug("equality::trigger") << d_name << "::eq::addTriggerTerm(" << t << ", " << tag << "): propagating " << disequalitiesToNotify.size() << " disequalities " << std::endl;
    propagateTriggerTermDisequalities(tags, triggerSetRef, disequalitiesToNotify);
  }
}

bool EqualityEngine::isTriggerTerm(TNode t, TheoryId tag) const {
  if (!hasTerm(t)) return false;
  EqualityNodeId classId = getEqualityNode(t).getFind();
  TriggerTermSetRef triggerSetRef = d_nodeIndividualTrigger[classId];
  return triggerSetRef != +null_set_id && getTriggerTermSet(triggerSetRef).hasTrigger(tag);
}


TNode EqualityEngine::getTriggerTermRepresentative(TNode t, TheoryId tag) const {
  Assert(isTriggerTerm(t, tag));
  EqualityNodeId classId = getEqualityNode(t).getFind();
  const TriggerTermSet& triggerSet = getTriggerTermSet(d_nodeIndividualTrigger[classId]);
  unsigned i = 0;
  Theory::Set tags = triggerSet.tags;
  while (Theory::setPop(tags) != tag) {
    ++ i;
  }
  return d_nodes[triggerSet.triggers[i]];
}

void EqualityEngine::storeApplicationLookup(FunctionApplication& funNormalized, EqualityNodeId funId) {
  Assert(d_applicationLookup.find(funNormalized) == d_applicationLookup.end());
  d_applicationLookup[funNormalized] = funId;
  d_applicationLookups.push_back(funNormalized);
  d_applicationLookupsCount = d_applicationLookupsCount + 1;
  Debug("equality::backtrack") << "d_applicationLookupsCount = " << d_applicationLookupsCount << std::endl;
  Debug("equality::backtrack") << "d_applicationLookups.size() = " << d_applicationLookups.size() << std::endl;
  Assert(d_applicationLookupsCount == d_applicationLookups.size());
}

void EqualityEngine::getUseListTerms(TNode t, std::set<TNode>& output) {
  if (hasTerm(t)) {
    // Get the equivalence class
    EqualityNodeId classId = getEqualityNode(t).getFind();
    // Go through the equivalence class and get where t is used in
    EqualityNodeId currentId = classId;
    do {
      // Get the current node
      EqualityNode& currentNode = getEqualityNode(currentId);
      // Go through the use-list
      UseListNodeId currentUseId = currentNode.getUseList();
      while (currentUseId != null_uselist_id) {
        // Get the node of the use list
        UseListNode& useNode = d_useListNodes[currentUseId];
        // Get the function application
        EqualityNodeId funId = useNode.getApplicationId();
        output.insert(d_nodes[funId]);
        // Go to the next one in the use list
        currentUseId = useNode.getNext();
      }
      // Move to the next node
      currentId = currentNode.getNext();
    } while (currentId != classId);
  }
}

EqualityEngine::TriggerTermSetRef EqualityEngine::newTriggerTermSet() {
  // Size of the required set
  size_t size = sizeof(TriggerTermSet) + d_newSetTriggersSize*sizeof(EqualityNodeId);
  // Align the size
  size = (size + 7) & ~((size_t)7);
  // Reallocate if necessary
  if (d_triggerDatabaseSize + size > d_triggerDatabaseAllocatedSize) {
    d_triggerDatabaseAllocatedSize *= 2;
    d_triggerDatabase = (char*) realloc(d_triggerDatabase, d_triggerDatabaseAllocatedSize);
  }
  // New reference
  TriggerTermSetRef newTriggerSetRef = d_triggerDatabaseSize;
  // Update the size
  d_triggerDatabaseSize = d_triggerDatabaseSize + size;
  // Copy the information
  TriggerTermSet& newSet = getTriggerTermSet(newTriggerSetRef);
  newSet.tags = d_newSetTags;
  for (unsigned i = 0; i < d_newSetTriggersSize; ++i) {
    newSet.triggers[i] = d_newSetTriggers[i];
  }
  // Return the new reference
  return newTriggerSetRef;
}

bool EqualityEngine::hasPropagatedDisequality(EqualityNodeId lhsId, EqualityNodeId rhsId) const {
  EqualityPair eq(lhsId, rhsId);
  bool propagated = d_propagatedDisequalities.find(eq) != d_propagatedDisequalities.end();
#ifdef CVC4_ASSERTIONS
  bool stored = d_disequalityReasonsMap.find(eq) != d_disequalityReasonsMap.end();
  Assert(propagated == stored, "These two should be in sync");
#endif
  Debug("equality::disequality") << d_name << "::eq::hasPropagatedDisequality(" << d_nodes[lhsId] << ", " << d_nodes[rhsId] << ") => " << (propagated ? "true" : "false") << std::endl;
  return propagated;
}

bool EqualityEngine::hasPropagatedDisequality(TheoryId tag, EqualityNodeId lhsId, EqualityNodeId rhsId) const {

  EqualityPair eq(lhsId, rhsId);

  PropagatedDisequalitiesMap::const_iterator it = d_propagatedDisequalities.find(eq);
  if (it == d_propagatedDisequalities.end()) {
    Assert(d_disequalityReasonsMap.find(eq) == d_disequalityReasonsMap.end(), "Why do we have a proof if not propagated");
    Debug("equality::disequality") << d_name << "::eq::hasPropagatedDisequality(" << tag << ", " << d_nodes[lhsId] << ", " << d_nodes[rhsId] << ") => false" << std::endl;
    return false;
  }
  Assert(d_disequalityReasonsMap.find(eq) != d_disequalityReasonsMap.end(), "We propagated but there is no proof");
  bool result = Theory::setContains(tag, (*it).second);
  Debug("equality::disequality") << d_name << "::eq::hasPropagatedDisequality(" << tag << ", " << d_nodes[lhsId] << ", " << d_nodes[rhsId] << ") => " << (result ? "true" : "false") << std::endl;
  return result;
}


void EqualityEngine::storePropagatedDisequality(TheoryId tag, EqualityNodeId lhsId, EqualityNodeId rhsId) {

  Assert(!hasPropagatedDisequality(tag, lhsId, rhsId), "Check before you store it");
  Assert(lhsId != rhsId, "Wow, wtf!");

  Debug("equality::disequality") << d_name << "::eq::storePropagatedDisequality(" << tag << ", " << d_nodes[lhsId] << ", " << d_nodes[rhsId] << ")" << std::endl;

  EqualityPair pair1(lhsId, rhsId);
  EqualityPair pair2(rhsId, lhsId);

  // Store the fact that we've propagated this already
  Theory::Set notified = 0;
  PropagatedDisequalitiesMap::const_iterator find = d_propagatedDisequalities.find(pair1);
  if (find == d_propagatedDisequalities.end()) {
    notified = Theory::setInsert(tag);
  } else {
    notified = Theory::setInsert(tag, (*find).second);
  }
  d_propagatedDisequalities[pair1] = notified;
  d_propagatedDisequalities[pair2] = notified;

  // Store the proof if provided
  if (d_deducedDisequalityReasons.size() > d_deducedDisequalityReasonsSize) {
    Debug("equality::disequality") << d_name << "::eq::storePropagatedDisequality(" << tag << ", " << d_nodes[lhsId] << ", " << d_nodes[rhsId] << "): storing proof" << std::endl;
    Assert(d_disequalityReasonsMap.find(pair1) == d_disequalityReasonsMap.end(), "There can't be a proof if you're adding a new one");
    DisequalityReasonRef ref(d_deducedDisequalityReasonsSize, d_deducedDisequalityReasons.size());
#ifdef CVC4_ASSERTIONS
    // Check that the reasons are valid
    for (unsigned i = ref.mergesStart; i < ref.mergesEnd; ++ i) {
      Assert(getEqualityNode(d_deducedDisequalityReasons[i].first).getFind() == getEqualityNode(d_deducedDisequalityReasons[i].second).getFind());
    }
#endif
    if (Debug.isOn("equality::disequality")) {
      for (unsigned i = ref.mergesStart; i < ref.mergesEnd; ++ i) {
        TNode lhs = d_nodes[d_deducedDisequalityReasons[i].first];
        TNode rhs = d_nodes[d_deducedDisequalityReasons[i].second];
        Debug("equality::disequality") << d_name << "::eq::storePropagatedDisequality(): because " << lhs << " == " << rhs << std::endl;
      }

    }

    // Store for backtracking
    d_deducedDisequalities.push_back(pair1);
    d_deducedDisequalitiesSize = d_deducedDisequalities.size();
    d_deducedDisequalityReasonsSize = d_deducedDisequalityReasons.size();
    // Store the proof reference
    d_disequalityReasonsMap[pair1] = ref;
    d_disequalityReasonsMap[pair2] = ref;
  } else {
    Assert(d_disequalityReasonsMap.find(pair1) != d_disequalityReasonsMap.end(), "You must provide a proof initially");
  }
}

void EqualityEngine::getDisequalities(bool allowConstants, EqualityNodeId classId, Theory::Set inputTags, TaggedEqualitiesSet& out) {
  // Must be empty on input
  Assert(out.size() == 0);
  // The class we are looking for, shouldn't have any of the tags we are looking for already set
  Assert(d_nodeIndividualTrigger[classId] == null_set_id || Theory::setIntersection(getTriggerTermSet(d_nodeIndividualTrigger[classId]).tags, inputTags) == 0);

  if (inputTags == 0) {
    return;
  }

  // Set of already (through disequalities) visited equivalence classes
  std::set<EqualityNodeId> alreadyVisited;

  // Go through the equivalence class
  EqualityNodeId currentId = classId;
  do {

    Debug("equality::trigger") << d_name << "::getDisequalities() : going through uselist of " << d_nodes[currentId] << std::endl;

    // Current node in the equivalence class
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Go through the uselist and look for disequalities
    UseListNodeId currentUseId = currentNode.getUseList();
    while (currentUseId != null_uselist_id) {
      UseListNode& useListNode = d_useListNodes[currentUseId];
      EqualityNodeId funId = useListNode.getApplicationId();

      Debug("equality::trigger") << d_name << "::getDisequalities() : checking " << d_nodes[funId] << std::endl;

      const FunctionApplication& fun = d_applications[useListNode.getApplicationId()].original;
      // If it's an equality asserted to false, we do the work
      if (fun.isEquality && getEqualityNode(funId).getFind() == getEqualityNode(d_false).getFind()) {
        // Get the other equality member
        bool lhs = false;
        EqualityNodeId toCompare = fun.b;
        if (toCompare == currentId) {
          toCompare = fun.a;
          lhs = true;
        }
        // Representative of the other member
        EqualityNodeId toCompareRep = getEqualityNode(toCompare).getFind();
        if (toCompareRep == classId) {
          // We're in conflict, so we will send it out from merge
          out.clear();
          return;
        }
        // Check if we already have this one
        if (alreadyVisited.count(toCompareRep) == 0) {
          // Mark as visited
          alreadyVisited.insert(toCompareRep);
          // Get the trigger set
          TriggerTermSetRef toCompareTriggerSetRef = d_nodeIndividualTrigger[toCompareRep];
          // We only care if we're not both constants and there are trigger terms in the other class
          if ((allowConstants || !d_isConstant[toCompareRep]) && toCompareTriggerSetRef != null_set_id) {
            // Tags of the other gey
            TriggerTermSet& toCompareTriggerSet = getTriggerTermSet(toCompareTriggerSetRef);
            // We only care if there are things in inputTags that is also in toCompareTags
            Theory::Set commonTags = Theory::setIntersection(inputTags, toCompareTriggerSet.tags);
            if (commonTags) {
              out.push_back(TaggedEquality(funId, toCompareTriggerSetRef, lhs));
            }
          }
        }
      }
      // Go to the next one in the use list
      currentUseId = useListNode.getNext();
    }
    // Next in equivalence class
    currentId = currentNode.getNext();
  } while (!d_done && currentId != classId);

}

bool EqualityEngine::propagateTriggerTermDisequalities(Theory::Set tags, TriggerTermSetRef triggerSetRef, const TaggedEqualitiesSet& disequalitiesToNotify) {
  
  // No tags, no food
  if (!tags) {
    return !d_done;
  }

  Assert(triggerSetRef != null_set_id);

  // This is the class trigger set
  const TriggerTermSet& triggerSet = getTriggerTermSet(triggerSetRef); 
  // Go through the disequalities and notify
  TaggedEqualitiesSet::const_iterator it = disequalitiesToNotify.begin();
  TaggedEqualitiesSet::const_iterator it_end = disequalitiesToNotify.end();
  for (; !d_done && it != it_end; ++ it) {
    // The information about the equality that is asserted to false
    const TaggedEquality& disequalityInfo = *it;
    const TriggerTermSet& disequalityTriggerSet = getTriggerTermSet(disequalityInfo.triggerSetRef); 
    Theory::Set commonTags = Theory::setIntersection(disequalityTriggerSet.tags, tags);
    Assert(commonTags);
    // This is the actual function
    const FunctionApplication& fun = d_applications[disequalityInfo.equalityId].original;
    // Figure out who we are comparing to in the original equality
    EqualityNodeId toCompare = disequalityInfo.lhs ? fun.a : fun.b;
    EqualityNodeId myCompare = disequalityInfo.lhs ? fun.b : fun.a;
    if (getEqualityNode(toCompare).getFind() == getEqualityNode(myCompare).getFind()) {
      // We're propagating a != a, which means we're inconsistent, just bail and let it go into
      // a regular conflict
      return !d_done;
    }
    // Go through the tags, and add the disequalities
    TheoryId currentTag;
    while (!d_done && ((currentTag = Theory::setPop(commonTags)) != THEORY_LAST)) {
      // Get the tag representative
      EqualityNodeId tagRep = disequalityTriggerSet.getTrigger(currentTag);
      EqualityNodeId myRep = triggerSet.getTrigger(currentTag);
      // Propagate
      if (!hasPropagatedDisequality(currentTag, myRep, tagRep)) {
        // Construct the proof if not there already
        if (!hasPropagatedDisequality(myRep, tagRep)) {
          d_deducedDisequalityReasons.push_back(EqualityPair(myCompare, myRep));
          d_deducedDisequalityReasons.push_back(EqualityPair(toCompare, tagRep));
          d_deducedDisequalityReasons.push_back(EqualityPair(disequalityInfo.equalityId, d_falseId));
        }
        // Store the propagation
        storePropagatedDisequality(currentTag, myRep, tagRep);
        // Notify
        if (d_performNotify) {
          if (!d_notify.eqNotifyTriggerTermEquality(currentTag, d_nodes[myRep], d_nodes[tagRep], false)) {
            d_done = true;
          }
        }
      }
    }
  }
  
  return !d_done;
}

EqClassesIterator::EqClassesIterator() :
    d_ee(NULL), d_it(0) {
}

EqClassesIterator::EqClassesIterator(const eq::EqualityEngine* ee)
: d_ee(ee)
{
  Assert(d_ee->consistent());
  d_it = 0;
  // Go to the first non-internal node that is it's own representative
  if(d_it < d_ee->d_nodesCount && (d_ee->d_isInternal[d_it] || d_ee->getEqualityNode(d_it).getFind() != d_it)) {
    ++d_it;
  }
}

Node EqClassesIterator::operator*() const {
  return d_ee->d_nodes[d_it];
}

bool EqClassesIterator::operator==(const EqClassesIterator& i) const {
  return d_ee == i.d_ee && d_it == i.d_it;
}

bool EqClassesIterator::operator!=(const EqClassesIterator& i) const {
  return !(*this == i);
}

EqClassesIterator& EqClassesIterator::operator++() {
  ++d_it;
  while(d_it < d_ee->d_nodesCount && (d_ee->d_isInternal[d_it] || d_ee->getEqualityNode(d_it).getFind() != d_it)) {
    ++d_it;
  }
  return *this;
}

EqClassesIterator EqClassesIterator::operator++(int) {
  EqClassesIterator i = *this;
  ++*this;
  return i;
}

bool EqClassesIterator::isFinished() const {
  return d_it >= d_ee->d_nodesCount;
}

EqClassIterator::EqClassIterator()
: d_ee(NULL)
, d_start(null_id)
, d_current(null_id)
{}

EqClassIterator::EqClassIterator(Node eqc, const eq::EqualityEngine* ee)
: d_ee(ee)
{
  Assert(d_ee->consistent());
  d_current = d_start = d_ee->getNodeId(eqc);
  Assert(d_start == d_ee->getEqualityNode(d_start).getFind());
  Assert (!d_ee->d_isInternal[d_start]);
}

Node EqClassIterator::operator*() const {
  return d_ee->d_nodes[d_current];
}

bool EqClassIterator::operator==(const EqClassIterator& i) const {
  return d_ee == i.d_ee && d_current == i.d_current;
}

bool EqClassIterator::operator!=(const EqClassIterator& i) const {
  return !(*this == i);
}

EqClassIterator& EqClassIterator::operator++() {
  Assert(!isFinished());

  Assert(d_start == d_ee->getEqualityNode(d_current).getFind());
  Assert(!d_ee->d_isInternal[d_current]);

  // Find the next one
  do {
    d_current = d_ee->getEqualityNode(d_current).getNext();
  } while(d_ee->d_isInternal[d_current]);

  Assert(d_start == d_ee->getEqualityNode(d_current).getFind());
  Assert(!d_ee->d_isInternal[d_current]);

  if(d_current == d_start) {
    // we end when we have cycled back to the original representative
    d_current = null_id;
  }
  return *this;
}

EqClassIterator EqClassIterator::operator++(int) {
  EqClassIterator i = *this;
  ++*this;
  return i;
}

bool EqClassIterator::isFinished() const {
  return d_current == null_id;
}


} // Namespace uf
} // Namespace theory
} // Namespace CVC4


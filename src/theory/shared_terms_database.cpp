/*********************                                                        */
/*! \file shared_terms_database.cpp
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
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/shared_terms_database.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace theory;

SharedTermsDatabase::SharedTermsDatabase(TheoryEngine* theoryEngine, context::Context* context)
: ContextNotifyObj(context)
, d_context(context)
, d_statSharedTerms("theory::shared_terms", 0)
, d_addedSharedTermsSize(context, 0)
, d_termsToTheories(context)
, d_alreadyNotifiedMap(context)
, d_registeredEqualities(context)
, d_EENotify(*this)
, d_equalityEngine(d_EENotify, context, "SharedTermsDatabase")
, d_theoryEngine(theoryEngine)
, d_inConflict(context, false)
{
  StatisticsRegistry::registerStat(&d_statSharedTerms);
}

SharedTermsDatabase::~SharedTermsDatabase() throw(AssertionException)
{
  StatisticsRegistry::unregisterStat(&d_statSharedTerms);
}

void SharedTermsDatabase::addEqualityToPropagate(TNode equality) {
  d_registeredEqualities.insert(equality);
  d_equalityEngine.addTriggerEquality(equality);
  checkForConflict();
}


void SharedTermsDatabase::addSharedTerm(TNode atom, TNode term, Theory::Set theories) {
  Debug("register") << "SharedTermsDatabase::addSharedTerm(" << atom << ", " << term << ", " << Theory::setToString(theories) << ")" << std::endl;

  std::pair<TNode, TNode> search_pair(atom, term);
  SharedTermsTheoriesMap::iterator find = d_termsToTheories.find(search_pair);
  if (find == d_termsToTheories.end()) {
    // First time for this term and this atom
    d_atomsToTerms[atom].push_back(term);
    d_addedSharedTerms.push_back(atom);
    d_addedSharedTermsSize = d_addedSharedTermsSize + 1;
    d_termsToTheories[search_pair] = theories;
  } else {
    Assert(theories != (*find).second);
    d_termsToTheories[search_pair] = Theory::setUnion(theories, (*find).second);
  }
}

SharedTermsDatabase::shared_terms_iterator SharedTermsDatabase::begin(TNode atom) const {
  Assert(hasSharedTerms(atom));
  return d_atomsToTerms.find(atom)->second.begin();
}

SharedTermsDatabase::shared_terms_iterator SharedTermsDatabase::end(TNode atom) const {
  Assert(hasSharedTerms(atom));
  return d_atomsToTerms.find(atom)->second.end();
}

bool SharedTermsDatabase::hasSharedTerms(TNode atom) const {
  return d_atomsToTerms.find(atom) != d_atomsToTerms.end();
}

void SharedTermsDatabase::backtrack() {
  for (int i = d_addedSharedTerms.size() - 1, i_end = (int)d_addedSharedTermsSize; i >= i_end; -- i) {
    TNode atom = d_addedSharedTerms[i];
    shared_terms_list& list = d_atomsToTerms[atom];
    list.pop_back();
    if (list.empty()) {
      d_atomsToTerms.erase(atom);
    }
  }
  d_addedSharedTerms.resize(d_addedSharedTermsSize);
}

Theory::Set SharedTermsDatabase::getTheoriesToNotify(TNode atom, TNode term) const {
  // Get the theories that share this term from this atom
  std::pair<TNode, TNode> search_pair(atom, term);
  SharedTermsTheoriesMap::iterator find = d_termsToTheories.find(search_pair);
  Assert(find != d_termsToTheories.end());

  // Get the theories that were already notified
  Theory::Set alreadyNotified = 0;
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    alreadyNotified = (*theoriesFind).second;
  }

  // Return the ones that haven't been notified yet
  return Theory::setDifference((*find).second, alreadyNotified);
}


Theory::Set SharedTermsDatabase::getNotifiedTheories(TNode term) const {
  // Get the theories that were already notified
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    return (*theoriesFind).second;
  } else {
    return 0;
  }
}

bool SharedTermsDatabase::propagateSharedEquality(TheoryId theory, TNode a, TNode b, bool value)
{
  Debug("shared-terms-database") << "SharedTermsDatabase::newEquality(" << theory << a << "," << b << ", " << (value ? "true" : "false") << ")" << endl;

  if (d_inConflict) {
    return false;
  }

  // Propagate away
  Node equality = a.eqNode(b);
  if (value) {
    d_theoryEngine->assertToTheory(equality, theory, THEORY_BUILTIN);
  } else {
    d_theoryEngine->assertToTheory(equality.notNode(), theory, THEORY_BUILTIN);
  }

  // As you were
  return true;
}

void SharedTermsDatabase::markNotified(TNode term, Theory::Set theories) {

  // Find out if there are any new theories that were notified about this term
  Theory::Set alreadyNotified = 0;
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    alreadyNotified = (*theoriesFind).second;
  }
  Theory::Set newlyNotified = Theory::setDifference(theories, alreadyNotified);

  // If no new theories were notified, we are done
  if (newlyNotified == 0) {
    return;
  }

  Debug("shared-terms-database") << "SharedTermsDatabase::markNotified(" << term << ")" << endl;

  // First update the set of notified theories for this term
  d_alreadyNotifiedMap[term] = Theory::setUnion(newlyNotified, alreadyNotified);

  // Mark the shared terms in the equality engine
  theory::TheoryId currentTheory;
  while ((currentTheory = Theory::setPop(newlyNotified)) != THEORY_LAST) {
    d_equalityEngine.addTriggerTerm(term, currentTheory);
  }

  // Check for any conflits
  checkForConflict();
}

bool SharedTermsDatabase::areEqual(TNode a, TNode b) const {
  if (d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b)) {
    return d_equalityEngine.areEqual(a,b);
  } else {
    Assert(d_equalityEngine.hasTerm(a) || a.isConst());
    Assert(d_equalityEngine.hasTerm(b) || b.isConst());
    // since one (or both) of them is a constant, and the other is in the equality engine, they are not same
    return false;
  }
}

bool SharedTermsDatabase::areDisequal(TNode a, TNode b) const {
  if (d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b)) {
    return d_equalityEngine.areDisequal(a,b,false);
  } else {
    Assert(d_equalityEngine.hasTerm(a) || a.isConst());
    Assert(d_equalityEngine.hasTerm(b) || b.isConst());
    // one (or both) are in the equality engine
    return false;
  }
}

void SharedTermsDatabase::assertEquality(TNode equality, bool polarity, TNode reason)
{
  Debug("shared-terms-database::assert") << "SharedTermsDatabase::assertEquality(" << equality << ", " << (polarity ? "true" : "false") << ", " << reason << ")" << endl;
  // Add it to the equality engine
  d_equalityEngine.assertEquality(equality, polarity, reason);
  // Check for conflict
  checkForConflict();
}

bool SharedTermsDatabase::propagateEquality(TNode equality, bool polarity) {
  if (polarity) {
    d_theoryEngine->propagate(equality, THEORY_BUILTIN);
  } else {
    d_theoryEngine->propagate(equality.notNode(), THEORY_BUILTIN);
  }
  return true;
}

static Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}

void SharedTermsDatabase::checkForConflict() {
  if (d_inConflict) {
    d_inConflict = false;
    std::vector<TNode> assumptions;
    d_equalityEngine.explainEquality(d_conflictLHS, d_conflictRHS, d_conflictPolarity, assumptions);
    Node conflict = mkAnd(assumptions);
    d_theoryEngine->conflict(conflict, THEORY_BUILTIN);
    d_conflictLHS = d_conflictRHS = Node::null();
  }
}

bool SharedTermsDatabase::isKnown(TNode literal) const {
  bool polarity = literal.getKind() != kind::NOT;
  TNode equality = polarity ? literal : literal[0];
  if (polarity) {
    return d_equalityEngine.areEqual(equality[0], equality[1]);
  } else {
    return d_equalityEngine.areDisequal(equality[0], equality[1], false);
  }
}

Node SharedTermsDatabase::explain(TNode literal) const {
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  Assert(atom.getKind() == kind::EQUAL);
  std::vector<TNode> assumptions;
  d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  return mkAnd(assumptions);
}

void SharedTermsDatabase::collectModelInfo( theory::TheoryModel* m, bool fullModel ){
  m->assertEqualityEngine( &d_equalityEngine );
}

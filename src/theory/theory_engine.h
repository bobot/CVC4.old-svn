/*********************                                                        */
/*! \file theory_engine.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway, barrett, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory engine
 **
 ** The theory engine.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_ENGINE_H
#define __CVC4__THEORY_ENGINE_H

#include <deque>
#include <vector>
#include <utility>

#include "expr/node.h"
#include "expr/command.h"
#include "prop/prop_engine.h"
#include "context/cdhashset.h"
#include "theory/theory.h"
#include "theory/substitutions.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"
#include "theory/valuation.h"
#include "util/options.h"
#include "util/stats.h"
#include "util/hash.h"
#include "util/cache.h"
#include "theory/ite_simplifier.h"
#include "theory/unconstrained_simplifier.h"
#include "theory/model.h"

namespace CVC4 {

/**
 * A pair of a theory and a node. This is used to mark the flow of
 * propagations between theories.
 */
struct NodeTheoryPair {
  Node node;
  theory::TheoryId theory;
  size_t timestamp;
  NodeTheoryPair(TNode node, theory::TheoryId theory, size_t timestamp)
  : node(node), theory(theory), timestamp(timestamp) {}
  NodeTheoryPair()
  : theory(theory::THEORY_LAST) {}
  // Comparison doesn't take into account the timestamp
  bool operator == (const NodeTheoryPair& pair) const {
    return node == pair.node && theory == pair.theory;
  }
};/* struct NodeTheoryPair */

struct NodeTheoryPairHashFunction {
  NodeHashFunction hashFunction;
  // Hash doesn't take into account the timestamp
  size_t operator()(const NodeTheoryPair& pair) const {
    return hashFunction(pair.node)*0x9e3779b9 + pair.theory;
  }
};/* struct NodeTheoryPairHashFunction */

namespace theory {
  class Instantiator;
}/* CVC4::theory namespace */

class DecisionEngine;

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * CVC4.
 */
class TheoryEngine {

  /** Shared terms database can use the internals notify the theories */
  friend class SharedTermsDatabase;

  /** Associated PropEngine engine */
  prop::PropEngine* d_propEngine;

  /** Access to decision engine */
  DecisionEngine* d_decisionEngine;

  /** Our context */
  context::Context* d_context;

  /** Our user context */
  context::UserContext* d_userContext;

  /**
   * A table of from theory IDs to theory pointers. Never use this table
   * directly, use theoryOf() instead.
   */
  theory::Theory* d_theoryTable[theory::THEORY_LAST];

  /**
   * A collection of theories that are "active" for the current run.
   * This set is provided by the user (as a logic string, say, in SMT-LIBv2
   * format input), or else by default it's all-inclusive.  This is important
   * because we can optimize for single-theory runs (no sharing), can reduce
   * the cost of walking the DAG on registration, etc.
   */
  const LogicInfo& d_logicInfo;

  /**
   * The database of shared terms.
   */
  SharedTermsDatabase d_sharedTerms;

  /**
   * The quantifiers engine
   */
  theory::QuantifiersEngine* d_quantEngine;

  /**
   * Default model object
   */
  theory::DefaultModel* d_curr_model;
  /**
   * Model builder object
   */
  theory::TheoryEngineModelBuilder* d_curr_model_builder;

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  typedef std::hash_map<TNode, Node, TNodeHashFunction> TNodeMap;

  /**
  * Cache for theory-preprocessing of assertions
   */
  NodeMap d_ppCache;

  /**
   * Used for "missed-t-propagations" dumping mode only.  A set of all
   * theory-propagable literals.
   */
  context::CDList<TNode> d_possiblePropagations;

  /**
   * Used for "missed-t-propagations" dumping mode only.  A
   * context-dependent set of those theory-propagable literals that
   * have been propagated.
   */
  context::CDHashSet<TNode, TNodeHashFunction> d_hasPropagated;

  /**
   * Statistics for a particular theory.
   */
  class Statistics {

    static std::string mkName(std::string prefix,
                              theory::TheoryId theory,
                              std::string suffix) {
      std::stringstream ss;
      ss << prefix << theory << suffix;
      return ss.str();
    }

  public:

    IntStat conflicts, propagations, lemmas, propagationsAsDecisions, requirePhase, flipDecision;

    Statistics(theory::TheoryId theory):
      conflicts(mkName("theory<", theory, ">::conflicts"), 0),
      propagations(mkName("theory<", theory, ">::propagations"), 0),
      lemmas(mkName("theory<", theory, ">::lemmas"), 0),
      propagationsAsDecisions(mkName("theory<", theory, ">::propagationsAsDecisions"), 0),
      requirePhase(mkName("theory<", theory, ">::requirePhase"), 0),
      flipDecision(mkName("theory<", theory, ">::flipDecision"), 0)
    {
      StatisticsRegistry::registerStat(&conflicts);
      StatisticsRegistry::registerStat(&propagations);
      StatisticsRegistry::registerStat(&lemmas);
      StatisticsRegistry::registerStat(&propagationsAsDecisions);
      StatisticsRegistry::registerStat(&requirePhase);
      StatisticsRegistry::registerStat(&flipDecision);
    }

    ~Statistics() {
      StatisticsRegistry::unregisterStat(&conflicts);
      StatisticsRegistry::unregisterStat(&propagations);
      StatisticsRegistry::unregisterStat(&lemmas);
      StatisticsRegistry::unregisterStat(&propagationsAsDecisions);
      StatisticsRegistry::unregisterStat(&requirePhase);
      StatisticsRegistry::unregisterStat(&flipDecision);
    }
  };/* class TheoryEngine::Statistics */


  /**
   * An output channel for Theory that passes messages
   * back to a TheoryEngine.
   */
  class EngineOutputChannel : public theory::OutputChannel {

    friend class TheoryEngine;

    /**
     * The theory engine we're communicating with.
     */
    TheoryEngine* d_engine;

    /**
     * The statistics of the theory interractions.
     */
    Statistics d_statistics;

    /**
     * The theory owning this chanell.
     */
    theory::TheoryId d_theory;

  public:

    EngineOutputChannel(TheoryEngine* engine, theory::TheoryId theory) :
      d_engine(engine),
      d_statistics(theory),
      d_theory(theory)
    {
    }

    void conflict(TNode conflictNode) throw(AssertionException) {
      Trace("theory::conflict") << "EngineOutputChannel<" << d_theory << ">::conflict(" << conflictNode << ")" << std::endl;
      ++ d_statistics.conflicts;
      d_engine->d_outputChannelUsed = true;
      d_engine->conflict(conflictNode, d_theory);
    }

    bool propagate(TNode literal) throw(AssertionException) {
      Trace("theory::propagate") << "EngineOutputChannel<" << d_theory << ">::propagate(" << literal << ")" << std::endl;
      ++ d_statistics.propagations;
      d_engine->d_outputChannelUsed = true;
      return d_engine->propagate(literal, d_theory);
    }

    void propagateAsDecision(TNode literal) throw(AssertionException) {
      Trace("theory::propagate") << "EngineOutputChannel<" << d_theory << ">::propagateAsDecision(" << literal << ")" << std::endl;
      ++ d_statistics.propagationsAsDecisions;
      d_engine->d_outputChannelUsed = true;
      d_engine->propagateAsDecision(literal, d_theory);
    }

    theory::LemmaStatus lemma(TNode lemma, bool removable = false) throw(TypeCheckingExceptionPrivate, AssertionException) {
      Trace("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma(" << lemma << ")" << std::endl;
      ++ d_statistics.lemmas;
      d_engine->d_outputChannelUsed = true;
      return d_engine->lemma(lemma, false, removable);
    }

    void requirePhase(TNode n, bool phase)
      throw(theory::Interrupted, AssertionException) {
      Debug("theory") << "EngineOutputChannel::requirePhase("
                      << n << ", " << phase << ")" << std::endl;
      ++ d_statistics.requirePhase;
      d_engine->d_propEngine->requirePhase(n, phase);
    }

    bool flipDecision()
      throw(theory::Interrupted, AssertionException) {
      Debug("theory") << "EngineOutputChannel::flipDecision()" << std::endl;
      ++ d_statistics.flipDecision;
      return d_engine->d_propEngine->flipDecision();
    }

    void setIncomplete() throw(AssertionException) {
      Trace("theory") << "TheoryEngine::setIncomplete()" << std::endl;
      d_engine->setIncomplete(d_theory);
    }

    void spendResource() throw() {
      d_engine->spendResource();
    }

  };/* class TheoryEngine::EngineOutputChannel */

  /**
   * Output channels for individual theories.
   */
  EngineOutputChannel* d_theoryOut[theory::THEORY_LAST];

  /**
   * Are we in conflict.
   */
  context::CDO<bool> d_inConflict;

  /**
   * Called by the theories to notify of a conflict.
   */
  void conflict(TNode conflict, theory::TheoryId theoryId);

  /**
   * Debugging flag to ensure that shutdown() is called before the
   * destructor.
   */
  bool d_hasShutDown;

  /**
   * True if a theory has notified us of incompleteness (at this
   * context level or below).
   */
  context::CDO<bool> d_incomplete;

  /**
   * Called by the theories to notify that the current branch is incomplete.
   */
  void setIncomplete(theory::TheoryId theory) {
    d_incomplete = true;
  }

  /**
   * "Spend" a resource during a search or preprocessing.
   */
  void spendResource() throw() {
    d_propEngine->spendResource();
  }

  /**
   * Mapping of propagations from recievers to senders.
   */
  typedef context::CDHashMap<NodeTheoryPair, NodeTheoryPair, NodeTheoryPairHashFunction> PropagationMap;
  PropagationMap d_propagationMap;

  /**
   * Timestamp of propagations
   */
  context::CDO<size_t> d_propagationMapTimestamp;

  /**
   * Literals that are propagated by the theory. Note that these are TNodes.
   * The theory can only propagate nodes that have an assigned literal in the
   * SAT solver and are hence referenced in the SAT solver.
   */
  context::CDList<TNode> d_propagatedLiterals;

  /**
   * The index of the next literal to be propagated by a theory.
   */
  context::CDO<unsigned> d_propagatedLiteralsIndex;

  /**
   * Decisions that are requested via propagateAsDecision().  The theory
   * can only request decisions on nodes that have an assigned litearl in
   * the SAT solver and are hence referenced in the SAT solver (making the
   * use of TNode safe).
   */
  context::CDList<TNode> d_decisionRequests;

  /**
   * The index of the next decision requested by a theory.
   */
  context::CDO<unsigned> d_decisionRequestsIndex;

  /**
   * Called by the output channel to propagate literals and facts
   * @return false if immediate conflict
   */
  bool propagate(TNode literal, theory::TheoryId theory);

  /**
   * Internal method to call the propagation routines and collect the
   * propagated literals.
   */
  void propagate(theory::Theory::Effort effort);

  /**
   * Called by the output channel to request decisions "as soon as
   * possible."
   */
  void propagateAsDecision(TNode literal, theory::TheoryId theory);

  /**
   * A variable to mark if we added any lemmas.
   */
  bool d_lemmasAdded;

  /**
   * A variable to mark if the OutputChannel was "used" by any theory
   * since the start of the last check.  If it has been, we require
   * a FULL_EFFORT check before exiting and reporting SAT.
   *
   * See the documentation for the needCheck() function, below.
   */
  bool d_outputChannelUsed;

  /**
   * Adds a new lemma, returning its status.
   */
  theory::LemmaStatus lemma(TNode node, bool negated, bool removable);

  /** Time spent in theory combination */
  TimerStat d_combineTheoriesTime;

  Node d_true;
  Node d_false;

public:

  /** Constructs a theory engine */
  TheoryEngine(context::Context* context, context::UserContext* userContext, const LogicInfo& logic);

  /** Destroys a theory engine */
  ~TheoryEngine();

  /**
   * Adds a theory. Only one theory per TheoryId can be present, so if
   * there is another theory it will be deleted.
   */
  template <class TheoryClass>
  inline void addTheory(theory::TheoryId theoryId) {
    Assert(d_theoryTable[theoryId] == NULL && d_theoryOut[theoryId] == NULL);
    d_theoryOut[theoryId] = new EngineOutputChannel(this, theoryId);
    d_theoryTable[theoryId] = new TheoryClass(d_context, d_userContext, *d_theoryOut[theoryId], theory::Valuation(this), d_logicInfo, getQuantifiersEngine());
  }

  inline void setPropEngine(prop::PropEngine* propEngine) {
    Assert(d_propEngine == NULL);
    d_propEngine = propEngine;
  }

  inline void setDecisionEngine(DecisionEngine* decisionEngine) {
    Assert(d_decisionEngine == NULL);
    d_decisionEngine = decisionEngine;
  }

  /**
   * Get a pointer to the underlying propositional engine.
   */
  inline prop::PropEngine* getPropEngine() const {
    return d_propEngine;
  }

  /**
   * Get a pointer to the underlying sat context.
   */
  inline context::Context* getSatContext() const {
    return d_context;
  }

  /**
   * Get a pointer to the underlying user context.
   */
  inline context::Context* getUserContext() const {
    return d_userContext;
  }

  /**
   * Get a pointer to the underlying quantifiers engine.
   */
  theory::QuantifiersEngine* getQuantifiersEngine() const {
    return d_quantEngine;
  }

private:

  /**
   * Helper for preprocess
   */
  Node ppTheoryRewrite(TNode term);

  /**
   * Queue of nodes for pre-registration.
   */
  std::queue<TNode> d_preregisterQueue;

  /**
   * Boolean flag denoting we are in pre-registration.
   */
  bool d_inPreregister;

  /**
   * Did the theories get any new facts since the last time we called
   * check()
   */
  context::CDO<bool> d_factsAsserted;

  /**
   * Assert the formula to the given theory.
   * @param assertion the assertion to send (not necesserily normalized)
   * @param original the assertion as it was sent in from the propagating theory
   * @param toTheoryId the theory to assert to
   * @param fromTheoryId the theory that sent it
   */
  void assertToTheory(TNode assertion, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId);

  /**
   * Marks a theory propagation from a theory to a theory where a
   * theory could be the THEORY_SAT_SOLVER for literals coming from
   * or being propagated to the SAT solver. If the receiving theory
   * already recieved the literal, the method returns false, otherwise
   * it returns true.
   *
   * @param assertion the normalized assertion being sent
   * @param originalAssertion the actual assertion that was sent
   * @param toTheoryId the theory that is on the receiving end
   * @param fromTheoryId the theory that sent the assertino
   * @return true if a new assertion, false if theory already got it
   */
  bool markPropagation(TNode assertion, TNode originalAssertions, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId);

  /**
   * Computes the explanation by travarsing the propagation graph and
   * asking relevant theories to explain the propagations. Initially
   * the explanation vector should contain only the element (node, theory)
   * where the node is the one to be explained, and the theory is the
   * theory that sent the literal.
   */
  void getExplanation(std::vector<NodeTheoryPair>& explanationVector);

public:

  /**
   * Signal the start of a new round of assertion preprocessing
   */
  void preprocessStart();

  /**
   * Runs theory specific preprocessing on the non-Boolean parts of
   * the formula.  This is only called on input assertions, after ITEs
   * have been removed.
   */
  Node preprocess(TNode node);

  /**
   * Return whether or not we are incomplete (in the current context).
   */
  inline bool isIncomplete() const {
    return d_incomplete;
  }

  /**
   * Returns true if we need another round of checking.  If this
   * returns true, check(FULL_EFFORT) _must_ be called by the
   * propositional layer before reporting SAT.
   *
   * This is especially necessary for incomplete theories that lazily
   * output some lemmas on FULL_EFFORT check (e.g. quantifier reasoning
   * outputing quantifier instantiations).  In such a case, a lemma can
   * be asserted that is simplified away (perhaps it's already true).
   * However, we must maintain the invariant that, if a theory uses the
   * OutputChannel, it implicitly requests that another check(FULL_EFFORT)
   * be performed before exit, even if no new facts are on its fact queue,
   * as it might decide to further instantiate some lemmas, precluding
   * a SAT response.
   */
  inline bool needCheck() const {
    return d_outputChannelUsed || d_lemmasAdded;
  }

  /**
   * This is called at shutdown time by the SmtEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory.
   */
  void shutdown();

  /**
   * Solve the given literal with a theory that owns it.
   */
  theory::Theory::PPAssertStatus solve(TNode literal,
                                    theory::SubstitutionMap& substitutionOut);

  /**
   * Preregister a Theory atom with the responsible theory (or
   * theories).
   */
  void preRegister(TNode preprocessed);

  /**
   * Assert the formula to the appropriate theory.
   * @param node the assertion
   */
  void assertFact(TNode node);

  /**
   * Check all (currently-active) theories for conflicts.
   * @param effort the effort level to use
   */
  void check(theory::Theory::Effort effort);

  /**
   * Run the combination framework.
   */
  void combineTheories();

  /**
   * Calls ppStaticLearn() on all theories, accumulating their
   * combined contributions in the "learned" builder.
   */
  void ppStaticLearn(TNode in, NodeBuilder<>& learned);

  /**
   * Calls presolve() on all theories and returns true
   * if one of the theories discovers a conflict.
   */
  bool presolve();

   /**
   * Calls postsolve() on all theories.
   */
  void postsolve();

  /**
   * Calls notifyRestart() on all active theories.
   */
  void notifyRestart();

  void getPropagatedLiterals(std::vector<TNode>& literals) {
    for (; d_propagatedLiteralsIndex < d_propagatedLiterals.size(); d_propagatedLiteralsIndex = d_propagatedLiteralsIndex + 1) {
      Debug("getPropagatedLiterals") << "TheoryEngine::getPropagatedLiterals: propagating: " << d_propagatedLiterals[d_propagatedLiteralsIndex] << std::endl;
      literals.push_back(d_propagatedLiterals[d_propagatedLiteralsIndex]);
    }
  }

  TNode getNextDecisionRequest() {
    if(d_decisionRequestsIndex < d_decisionRequests.size()) {
      TNode req = d_decisionRequests[d_decisionRequestsIndex];
      Debug("propagateAsDecision") << "TheoryEngine requesting decision["
                                   << d_decisionRequestsIndex << "]: "
                                   << req << std::endl;
      d_decisionRequestsIndex = d_decisionRequestsIndex + 1;
      return req;
    } else {
      return TNode::null();
    }
  }

  bool properConflict(TNode conflict) const;
  bool properPropagation(TNode lit) const;
  bool properExplanation(TNode node, TNode expl) const;

  /**
   * Returns an explanation of the node propagated to the SAT solver.
   */
  Node getExplanation(TNode node);

  /**
   * collect model info
   */
  void collectModelInfo( theory::TheoryModel* m );

  /**
   * Get the current model
   */
  theory::TheoryModel* getModel();

  /**
   * Get the model builder
   */
  theory::TheoryEngineModelBuilder* getModelBuilder() { return d_curr_model_builder; }

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(TNode node) {
    return d_theoryTable[theory::Theory::theoryOf(node)];
  }

  /**
   * Get the theory associated to a the given theory id. It will also mark the
   * theory as currently active, we assume that theories are called only through
   * theoryOf.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(theory::TheoryId theoryId) {
    return d_theoryTable[theoryId];
  }

  /** Get the theory for id */
  theory::Theory* getTheory(theory::TheoryId theoryId) {
    return d_theoryTable[theoryId];
  }

  /**
   * Returns the equality status of the two terms, from the theory
   * that owns the domain type.  The types of a and b must be the same.
   */
  theory::EqualityStatus getEqualityStatus(TNode a, TNode b);

private:

  /** Default visitor for pre-registration */
  PreRegisterVisitor d_preRegistrationVisitor;

  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor;

  /** Prints the assertions to the debug stream */
  void printAssertions(const char* tag);

  /** Dump the assertions to the dump */
  void dumpAssertions(const char* tag);

  /** For preprocessing pass simplifying ITEs */
  ITESimplifier d_iteSimplifier;

  /** For preprocessing pass simplifying unconstrained expressions */
  UnconstrainedSimplifier d_unconstrainedSimp;

public:

  Node ppSimpITE(TNode assertion);
  void ppUnconstrainedSimp(std::vector<Node>& assertions);

  SharedTermsDatabase* getSharedTermsDatabase() { return &d_sharedTerms; }

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */

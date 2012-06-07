/*********************                                                        */
/*! \file theory_arith.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Arithmetic theory.
 ** ** Arithmetic theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__THEORY_ARITH_H
#define __CVC4__THEORY__ARITH__THEORY_ARITH_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "expr/node.h"

#include "util/dense_map.h"

#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/matrix.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/linear_equality.h"
#include "theory/arith/simplex.h"
#include "theory/arith/arith_static_learner.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/arith/dio_solver.h"
#include "theory/arith/congruence_manager.h"

#include "theory/arith/constraint.h"

#include "util/stats.h"

#include <vector>
#include <map>
#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * Implementation of QF_LRA.
 * Based upon:
 * http://research.microsoft.com/en-us/um/people/leonardo/cav06.pdf
 */
class TheoryArith : public Theory {
private:
  bool rowImplication(RowIndex ridx, ArithVar v, const DeltaRational& r,  bool upperBound, bool coeffIsPositive);

  /**
   * This counter is false if nothing has been done since the last cut.
   * This is used to break an infinite loop.
   */
  bool d_hasDoneWorkSinceCut;

  /** Static learner. */
  ArithStaticLearner d_learner;

  /**
   * List of the variables in the system.
   * This is needed to keep a positive ref count on slack variables.
   */
  std::vector<Node> d_variables;

  /**
   * The map between arith variables to nodes.
   */
  ArithVarNodeMap d_arithvarNodeMap;

  NodeSet d_setupNodes;
  bool isSetup(Node n){
    return d_setupNodes.find(n) != d_setupNodes.end();
  }
  void markSetup(Node n){
    Assert(!isSetup(n));
    d_setupNodes.insert(n);
  }

  void setupVariable(const Variable& x);
  void setupVariableList(const VarList& vl);
  void setupPolynomial(const Polynomial& poly);
  void setupAtom(TNode atom);

  class SetupLiteralCallBack : public TNodeCallBack {
  private:
    TheoryArith* d_arith;
  public:
    SetupLiteralCallBack(TheoryArith* ta) : d_arith(ta){}
    void operator()(TNode lit){
      TNode atom = (lit.getKind() == kind::NOT) ? lit[0] : lit;
      if(!d_arith->isSetup(atom)){
        d_arith->setupAtom(atom);
      }
    }
  } d_setupLiteralCallback;

  /**
   * (For the moment) the type hierarchy goes as:
   * Integer <: Real
   * The type number of a variable is an integer representing the most specific
   * type of the variable. The possible values of type number are:
   */
  enum ArithType
    {
      ATReal = 0,
      ATInteger = 1
   };

  std::vector<ArithType> d_variableTypes;
  inline ArithType nodeToArithType(TNode x) const {
    return (x.getType().isInteger() ? ATInteger : ATReal);
  }

  /** Returns true if x is of type Integer. */
  inline bool isInteger(ArithVar x) const {
    return d_variableTypes[x] >= ATInteger;
  }

  /** This is the set of variables initially introduced as slack variables. */
  std::vector<bool> d_slackVars;

  /** Returns true if the variable was initially introduced as a slack variable. */
  inline bool isSlackVariable(ArithVar x) const{
    return d_slackVars[x];
  }

  /**
   * On full effort checks (after determining LA(Q) satisfiability), we
   * consider integer vars, but we make sure to do so fairly to avoid
   * nontermination (although this isn't a guarantee).  To do it fairly,
   * we consider variables in round-robin fashion.  This is the
   * round-robin index.
   */
  ArithVar d_nextIntegerCheckVar;

  /**
   * Queue of Integer variables that are known to be equal to a constant.
   */
  context::CDQueue<ArithVar> d_constantIntegerVariables;

  Node callDioSolver();
  Node dioCutting();

  Comparison mkIntegerEqualityFromAssignment(ArithVar v);

  /**
   * List of all of the disequalities asserted in the current context that are not known
   * to be satisfied.
   */
  context::CDQueue<Constraint> d_diseqQueue;

  /**
   * A queue of constraints to assert.
   * This lasts the duration of a check call.
   * This is always empty at the entry and exit of a check call.
   */
  std::deque<Constraint> d_toAssertQueue;

  /**
   * Constraints that have yet to be processed by proagation work list.
   * All of the elements have type of LowerBound, UpperBound, or
   * Equality.
   *
   * This is empty at the beginning of every check call.
   *
   * If head()->getType() == LowerBound or UpperBound,
   * then d_cPL[1] is the previous constraint in d_partialModel for the
   * corresponding bound.
   * If head()->getType() == Equality,
   * then d_cPL[1] is the previous lowerBound in d_partialModel,
   * and d_cPL[2] is the previous upperBound in d_partialModel.
   */
  std::deque<Constraint> d_unatePropagationList;

  /** Enqueues a unate propagtion for a lower bound or upperbound.
   */
  void enqueueUnatePropagation(Constraint curr, Constraint prev);

  /** Enqueues a unate propagtion for an equality. */
  void enqueueUnatePropagation(Constraint curr, Constraint plb, Constraint pub);
  void unatePropagation();


  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   */
  ArithPartialModel d_partialModel;

  /**
   * The tableau for all of the constraints seen thus far in the system.
   */
  Tableau d_tableau;

  /**
   * Maintains the relationship between the PartialModel and the Tableau.
   */
  LinearEqualityModule d_linEq;

  /**
   * A Diophantine equation solver.  Accesses the tableau and partial
   * model (each in a read-only fashion).
   */
  DioSolver d_diosolver;

  /**
   * Some integer variables can be replaced with pseudoboolean
   * variables internally.  This map is built up at static learning
   * time for top-level asserted expressions of the shape "x = 0 OR x
   * = 1".  This substitution map is then applied in preprocess().
   *
   * Note that expressions of the shape "x >= 0 AND x <= 1" are
   * already substituted for PB versions at solve() time and won't
   * appear here.
   */
  SubstitutionMap d_pbSubstitutions;

  /** Counts the number of notifyRestart() calls to the theory. */
  uint32_t d_restartsCounter;

  /**
   * Every number of restarts equal to s_TABLEAU_RESET_PERIOD,
   * the density of the tableau, d, is computed.
   * If d >= s_TABLEAU_RESET_DENSITY * d_initialDensity, the tableau
   * is set to d_initialTableau.
   */
  bool d_tableauSizeHasBeenModified;
  double d_tableauResetDensity;
  uint32_t d_tableauResetPeriod;
  static const uint32_t s_TABLEAU_RESET_INCREMENT = 5;


  /**
   * This is the queue of conflicts.
   */
  context::CDList<Node> d_conflicts;
  class PushCallBack : public NodeCallBack {
  private:
    context::CDList<Node>& d_list;
  public:
    PushCallBack(context::CDList<Node>& l)
    : d_list(l)
    {}
    void operator()(Node n){
      d_list.push_back(n);
    }
  } d_raiseConflict;

  /** Returns true iff a conflict has been raised. */
  inline bool inConflict() const {
    return !d_conflicts.empty();
  }
  /**
   * Outputs the contents of d_conflicts onto d_out.
   * Must be inConflict().
   */
  void outputConflicts();

  /**
   * A copy of the tableau immediately after removing variables
   * without bounds in presolve().
   */
  Tableau d_smallTableauCopy;

  /**
   * This keeps track of congruences for arithmetic.
   * Mostly for sharing.
   */
  ArithCongruenceManager d_congruenceManager;

  /** This implements the Simplex decision procedure. */
  SimplexDecisionProcedure d_simplex;


  /** The constraint database associated with the theory. */
  ConstraintDatabase d_constraintDatabase;

  /** Internal model value for the atom */
  bool getDeltaAtomValue(TNode n);

  /** Internal model value for the node */
  DeltaRational getDeltaValue(TNode n);

public:
  TheoryArith(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo);
  virtual ~TheoryArith();

  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n);

  void check(Effort e);
  void propagate(Effort e);
  Node explain(TNode n);

  Node getValue(TNode n);

  void shutdown(){ }

  void presolve();
  void notifyRestart();
  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);
  Node ppRewrite(TNode atom);
  void ppStaticLearn(TNode in, NodeBuilder<>& learned);

  std::string identify() const { return std::string("TheoryArith"); }

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  void addSharedTerm(TNode n);

private:

  class BasicVarModelUpdateCallBack : public ArithVarCallBack{
  private:
    SimplexDecisionProcedure& d_simplex;

  public:
    BasicVarModelUpdateCallBack(SimplexDecisionProcedure& s):
      d_simplex(s)
    {}

    void operator()(ArithVar x){
      d_simplex.updateBasic(x);
    }
  };

  BasicVarModelUpdateCallBack d_basicVarModelUpdateCallBack;

  /** The constant zero. */
  DeltaRational d_DELTA_ZERO;

  /** propagates an arithvar */
  void propagateArithVar(bool upperbound, ArithVar var );

  /**
   * Using the simpleKind return the ArithVar associated with the assertion.
   */
  ArithVar determineArithVar(const Polynomial& p) const;
  ArithVar determineArithVar(TNode assertion) const;


  /**
   * Splits the disequalities in d_diseq that are violated using lemmas on demand.
   * returns true if any lemmas were issued.
   * returns false if all disequalities are satisified in the current model.
   */
  bool splitDisequalities();

  /** A Difference variable is known to be 0.*/
  void zeroDifferenceDetected(ArithVar x);


  /** Converts the assertions coming in on the fact queue to
   * constraints and enqueues these on the to assert queue.
   */
  void enqueueFactQueueIntoConstraintQueue();

  /**
   * This heuristically infers constraints that can be asserted
   * internally.
   * Inferred constraints can be both propagated and
   * added to the toAssertQueue.
   */
  void inferConstraints();

  /**
   * This loop is responsible for:
   * 1) processing the queue of constraints to assert
   * 2) finding a QF_LRA model if one exists.
   * 3) inferring new constraints using the previously asserted constraints and the satisfying model + tableau
   * Returns true if it has discovered a conflict.
   */
  bool constraintAssertInferLoop();



  /**
   * Looks for the next integer variable without an integer assignment in a round robin fashion.
   * Changes the value of d_nextIntegerCheckVar.
   *
   * If this returns false, d_nextIntegerCheckVar does not have an integer assignment.
   * If this returns true, all integer variables have an integer assignment.
   */
  bool hasIntegerModel();

  /**
   * Issues branches for non-slack integer variables with non-integer assignments.
   * Returns a cut for a lemma.
   * If there is an integer model, this returns Node::null().
   */
  Node roundRobinBranch();

  /**
   * This requests a new unique ArithVar value for x.
   * This also does initial (not context dependent) set up for a variable,
   * except for setting up the initial.
   */
  ArithVar requestArithVar(TNode x, bool slack);

  /** Initial (not context dependent) sets up for a variable.*/
  void setupInitialValue(ArithVar x);

  /** Initial (not context dependent) sets up for a new slack variable.*/
  void setupSlack(TNode left);


  /**
   * Assert*(Constraint c) takes a constraint c.
   * If c is tighter than the current bounds,
   * then the assertion continues.
   * The partial model is updated if needed to get the basic
   * variables satisfied.
   *
   * c must have a proof.
   *
   * x is the variable getting the new bound,
   * c is the value of the new bound.
   *
   * If x is an integer variable, c must be an integer.
   *
   * If this new bound is in conflict with the other bound,
   * a conflict is raised and true is returned.
   * If this new bound is not in conflict, false is returned.
   */
  bool AssertLower(Constraint constraint);
  bool AssertUpper(Constraint constraint);
  bool AssertEquality(Constraint constraint);
  bool AssertDisequality(Constraint constraint);

  /**
   * This is a preproccessor for Assert*,
   * This ensures that the preconditions for Assert* are met.
   */
  bool assertionCases(Constraint c);

  /** Tracks the variables with bounds that were updated in the current round. */
  DenseSet d_updatedBounds;

  /** Tracks the rows variables where bound inference might be possible. */
  DenseSet d_candidateRows;

  bool hasAnyUpdates() { return !d_updatedBounds.empty(); }
  void clearUpdates();

  void revertOutOfConflict();

  void propagateCandidates();
  bool propagateCandidateRow(RowIndex ridx);
  bool propagateCandidateBound(ArithVar basic, bool upperBound);

  inline bool propagateCandidateLowerBound(ArithVar basic){
    return propagateCandidateBound(basic, false);
  }
  inline bool propagateCandidateUpperBound(ArithVar basic){
    return propagateCandidateBound(basic, true);
  }

  /**
   * Performs a check to see if it is definitely true that setup can be avoided.
   */
  bool canSafelyAvoidEqualitySetup(TNode equality);

  /**
   * Dequeues an assertion from the fact queue, and converts the
   * assertion from the fact queue to a constraint.
   * This has a few possibile outcomes:
   * - A conflict. return NullConstraint and raised a conflict
   * - An asserted literal. returns Nullconstraint
   * - Otherwise. Returns the constraint.
   */
  Constraint assertionToConstraint();

  /**
   * Returns the basic variable with the shorted row containg a non-basic variable.
   * If no such row exists, return ARITHVAR_SENTINEL.
   */
  ArithVar findShortestBasicRow(ArithVar variable);

  /**
   * Debugging only routine!
   * Returns true iff every variable is consistent in the partial model.
   */
  bool entireStateIsConsistent();

  bool isImpliedUpperBound(ArithVar var, Node exp);
  bool isImpliedLowerBound(ArithVar var, Node exp);

  void internalExplain(TNode n, NodeBuilder<>& explainBuilder);


  void asVectors(const Polynomial& p,
                 std::vector<Rational>& coeffs,
                 std::vector<ArithVar>& variables);

  /** Routine for debugging. Print the assertions the theory is aware of. */
  void debugPrintAssertions();
  /** Debugging only routine. Prints the model. */
  void debugPrintModel();

  inline bool canPerformUnateProp() const {
    return (Options::current()->arithPropagationMode == Options::UNATE_PROP ||
            Options::current()->arithPropagationMode == Options::BOTH_PROP);
  }

  inline bool canPerformBoundsInference() const {
    return (Options::current()->arithPropagationMode == Options::BOUND_INFERENCE_PROP ||
            Options::current()->arithPropagationMode == Options::BOTH_PROP);
  }

  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statAssertUpperConflicts, d_statAssertLowerConflicts;

    IntStat d_statUserVariables, d_statSlackVariables;
    IntStat d_statDisequalitySplits;
    IntStat d_statDisequalityConflicts;
    TimerStat d_simplifyTimer;
    TimerStat d_staticLearningTimer;

    TimerStat d_presolveTime;

    TimerStat d_unatePropTime;

    IntStat d_externalBranchAndBounds;

    IntStat d_initialTableauSize;
    IntStat d_currSetToSmaller;
    IntStat d_smallerSetToCurr;
    TimerStat d_restartTimer;

    TimerStat d_boundComputationTime;
    IntStat d_boundComputations, d_boundPropagations;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};/* class TheoryArith */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */

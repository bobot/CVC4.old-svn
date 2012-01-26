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
 **
 ** Arithmetic theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__THEORY_ARITH_H
#define __CVC4__THEORY__ARITH__THEORY_ARITH_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdset.h"
#include "expr/node.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_set.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/atom_database.h"
#include "theory/arith/simplex.h"
#include "theory/arith/arith_static_learner.h"
#include "theory/arith/arith_prop_manager.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/arith/dio_solver.h"
#include "theory/arith/difference_manager.h"

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

  /**
   * The set of atoms that are currently in the context.
   * This is exactly the union of preregistered atoms and
   * equalities from sharing.
   * This is used to reconstruct the rest of arithmetic.
   */
  CDNodeSet d_atomsInContext;
  bool inContextAtom(TNode atom){
    Assert(isRelationOperator(atom.getKind()));
    Assert(Comparison::isNormalAtom(atom));
    return d_atomsInContext.contains(atom);
  }
  void addToContext(TNode atom){
    Assert(isRelationOperator(atom.getKind()));
    Assert(Comparison::isNormalAtom(atom));
    d_atomsInContext.insert(atom);
  }

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
  void setupAtom(TNode atom, bool addToDatabase);


  /**
   * (For the moment) the type hierarchy goes as:
   * PsuedoBoolean <: Integer <: Real
   * The type number of a variable is an integer representing the most specific
   * type of the variable. The possible values of type number are:
   */
  enum ArithType
    {
      ATReal = 0,
      ATInteger = 1,
      ATPsuedoBoolean = 2
   };

  std::vector<ArithType> d_variableTypes;
  inline ArithType nodeToArithType(TNode x) const {
    return x.getType().isPseudoboolean() ? ATPsuedoBoolean :
      (x.getType().isInteger() ? ATInteger : ATReal);
  }

  /** Returns true if x is of type Integer or PsuedoBoolean. */
  inline bool isInteger(ArithVar x) const {
    return d_variableTypes[x] >= ATInteger;
  }
  /** Returns true if x is of type PsuedoBoolean. */
  inline bool isPsuedoBoolean(ArithVar x) const {
    return d_variableTypes[x] == ATPsuedoBoolean;
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
  context::CDList<ArithVar> d_constantIntegerVariables;
  /** Iterator over d_constantIntegerVariables. */
  context::CDO<unsigned int> d_CivIterator;

  Node callDioSolver();
  Comparison mkIntegerEqualityFromAssignment(ArithVar v);

  #warning "DO NOT COMMIT TO TRUNK, USE MORE EFFICIENT CHECK INSTEAD"
  CDArithVarSet d_varsInDioSolver;

  /**
   * If ArithVar v maps to the node n in d_removednode,
   * then n = (= asNode(v) rhs) where rhs is a term that
   * can be used to determine the value of n using getValue().
   */
  std::map<ArithVar, Node> d_removedRows;

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   */
  ArithPartialModel d_partialModel;

  /**
   * List of all of the inequalities asserted in the current context.
   */
  context::CDSet<Node, NodeHashFunction> d_diseq;

  /**
   * The tableau for all of the constraints seen thus far in the system.
   */
  Tableau d_tableau;

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
  bool d_rowHasBeenAdded;
  double d_tableauResetDensity;
  uint32_t d_tableauResetPeriod;
  static const uint32_t s_TABLEAU_RESET_INCREMENT = 5;

  /**
   * A copy of the tableau immediately after removing variables
   * without bounds in presolve().
   */
  Tableau d_smallTableauCopy;

  /**
   * The atom database keeps track of the atoms that have been preregistered.
   * Used to add unate propagations.
   */
  ArithAtomDatabase d_atomDatabase;

  /** This manager keeps track of information needed to propagate. */
  ArithPropManager d_propManager;

  /** This keeps track of difference equalities. Mostly for sharing. */
  DifferenceManager d_differenceManager;

  /** This implements the Simplex decision procedure. */
  SimplexDecisionProcedure d_simplex;
public:
  TheoryArith(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation);
  virtual ~TheoryArith();

  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n);

  void check(Effort e);
  void propagate(Effort e);
  Node explain(TNode n);

  void notifyEq(TNode lhs, TNode rhs);

  Node getValue(TNode n);

  void shutdown(){ }

  void presolve();
  void notifyRestart();
  SolveStatus solve(TNode in, SubstitutionMap& outSubstitutions);
  Node preprocess(TNode atom);
  void staticLearning(TNode in, NodeBuilder<>& learned);

  std::string identify() const { return std::string("TheoryArith"); }

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  void addSharedTerm(TNode n);

private:
  /** The constant zero. */
  DeltaRational d_DELTA_ZERO;

  /** propagates an arithvar */
  void propagateArithVar(bool upperbound, ArithVar var );

  /**
   * Using the simpleKind return the ArithVar associated with the
   * left hand side of assertion.
   */
  ArithVar determineLeftVariable(TNode assertion, Kind simpleKind);

  /** Splits the disequalities in d_diseq that are violated using lemmas on demand. */
  void splitDisequalities();

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
   * Performs *permanent* static setup for equalities that have not been
   * preregistered.
   * Currently these MUST be introduced by combination.
   */
  //void delayedSetupEquality(TNode equality);

  //void delayedSetupPolynomial(TNode polynomial);
  //void delayedSetupMonomial(const Monomial& mono);

  /**
   * Performs a check to see if it is definitely true that setup can be avoided.
   */
  bool canSafelyAvoidEqualitySetup(TNode equality);

  /**
   * Handles the case splitting for check() for a new assertion.
   * Returns a conflict if one was found.
   * Returns Node::null if no conflict was found.
   */
  Node assertionCases(TNode assertion);

  /**
   * This is used for reporting conflicts caused by disequalities during assertionCases.
   */
  Node disequalityConflict(TNode eq, TNode lb, TNode ub);

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

  /**
   * Permanently removes a variable from the problem.
   * The caller guarentees the saftey of this removal!
   */
  void permanentlyRemoveVariable(ArithVar v);

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

  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statUserVariables, d_statSlackVariables;
    IntStat d_statDisequalitySplits;
    IntStat d_statDisequalityConflicts;
    TimerStat d_simplifyTimer;
    TimerStat d_staticLearningTimer;

    IntStat d_permanentlyRemovedVariables;
    TimerStat d_presolveTime;

    IntStat d_externalBranchAndBounds;

    IntStat d_initialTableauSize;
    IntStat d_currSetToSmaller;
    IntStat d_smallerSetToCurr;
    TimerStat d_restartTimer;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;


};/* class TheoryArith */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */

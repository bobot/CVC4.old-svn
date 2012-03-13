/*********************                                                        */
/*! \file dio_solver.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Diophantine equation solver
 **
 ** A Diophantine equation solver for the theory of arithmetic.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__DIO_SOLVER_H
#define __CVC4__THEORY__ARITH__DIO_SOLVER_H

#include "expr/node.h"

#include "context/context.h"
#include "context/cdo.h"
#include "context/cdqueue.h"
#include "context/cdtrail_queue.h"
#include "context/cdlist.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"
#include "util/rational.h"

#include "util/stats.h"

#include <stdint.h>
#include <vector>
#include <utility>
#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

class DioSolver {
private:
  typedef size_t TrailIndex;
  typedef size_t InputConstraintIndex;
  typedef size_t SubIndex;

  /**
   * The set of input constraints is stored in a CDList.
   * Each constraint point to an element of the trail.
   */
  struct InputConstraint {
    Node d_reason;
    TrailIndex d_trailPos;
    InputConstraint(Node reason, TrailIndex pos) : d_reason(reason), d_trailPos(pos) {}
  };
  context::CDList<InputConstraint> d_inputConstraints;

  /**
   * This is the next input constraint to handle.
   */
  context::CDO<size_t> d_nextInputConstraintToEnqueue;


  /**
   * We maintain a map from the variables associated with proofs to an input constraint.
   * These variables can then be used in polynomial manipulations.
   */
  typedef std::hash_map<Node, InputConstraintIndex, NodeHashFunction> NodeToInputConstraintIndexMap;
  NodeToInputConstraintIndexMap d_varToInputConstraintMap;

  Node proofVariableToReason(const Variable& v) const{
    Assert(d_varToInputConstraintMap.find(v.getNode()) != d_varToInputConstraintMap.end());
    InputConstraintIndex pos = (*(d_varToInputConstraintMap.find(v.getNode()))).second;
    Assert(pos < d_inputConstraints.size());
    return d_inputConstraints[pos].d_reason;
  }

  /**
   * The main work horse of the algorithm, the trail of constraints.
   * Each constraint is a SumPair that implicitly represents an equality against 0.
   *   d_trail[i].d_eq = (+ c (+ [(* coeff var)])) representing (+ [(* coeff var)]) = -c
   * Each constraint has a proof in terms of a linear combination of the input constraints.
   *   d_trail[i].d_proof
   *
   * Each Constraint also a monomial in d_eq.getPolynomial()
   * of minimal absolute value by the coefficients.
   * d_trail[i].d_minimalMonomial
   *
   * See Alberto's paper for how linear proofs are maintained for the abstract
   * state machine in rules (7), (8) and (9).
   */
  struct Constraint {
    SumPair d_eq;
    Polynomial d_proof;
    Monomial d_minimalMonomial;
    Constraint(const SumPair& eq, const Polynomial& p) :
      d_eq(eq), d_proof(p), d_minimalMonomial(d_eq.getPolynomial().selectAbsMinimum())
    {}
  };
  context::CDList<Constraint> d_trail;

  /** Compare by d_minimal. */
  struct TrailMinimalCoefficientOrder {
    const context::CDList<Constraint>& d_trail;
    TrailMinimalCoefficientOrder(const context::CDList<Constraint>& trail):
      d_trail(trail)
    {}

    bool operator()(TrailIndex i, TrailIndex j){
      return d_trail[i].d_minimalMonomial.absLessThan(d_trail[j].d_minimalMonomial);
    }
  };

  /**
   * A substitution is stored as a constraint in the trail together with
   * the variable to be eliminated, and a fresh variable if one was introduced.
   * The variable d_subs[i].d_eliminated is substituted using the implicit equality in
   * d_trail[d_subs[i].d_constraint]
   *  - d_subs[i].d_eliminated is normalized to have coefficient -1 in
   *    d_trail[d_subs[i].d_constraint].
   *  - d_subs[i].d_fresh is either Node::null() or it is variable it is normalized
   *    to have coefficient 1 in d_trail[d_subs[i].d_constraint].
   *
   * Substitutions can also be seen as a context dependent queue.
   */
  struct Substitution {
    Node d_fresh;
    Variable d_eliminated;
    TrailIndex d_constraint;
    Substitution(Node f, const Variable& e, TrailIndex c) :
      d_fresh(f), d_eliminated(e), d_constraint(c)
    {}
  };
  context::CDTrailQueue<Substitution> d_subs;

  /**
   * This is the queue of constraints to be processed in the current context level.
   * This is to be empty upon entering solver and cleared upon leaving the solver.
   *
   * All elements in currentF:
   * - are fully substituted according to d_subs.
   * - !isConstant().
   * - If the element is (+ constant (+ [(* coeff var)] )), then the gcd(coeff) = 1
   */
  std::deque<TrailIndex> d_currentF;

  /**
   * This is the queue of constraints inbetween calls to the DioSolver.
   * This is also where constraints go if the constraint is deemed to be too expensive
   * in the current context.
   */
  context::CDQueue<TrailIndex> d_savedQueue;

  context::CDO<bool> d_conflictHasBeenRaised;
  TrailIndex d_conflictIndex;

  /**
   * Drop derived constraints with a coefficient length larger than
   * the maximum input constraints length than 2**MAX_GROWTH_RATE.
   */
  context::CDO<uint32_t> d_maxInputCoefficientLength;
  static const uint32_t MAX_GROWTH_RATE = 3;

  /** Returns true if the element on the trail should be dropped.*/
  bool anyCoefficientExceedsMaximum(TrailIndex j) const;

  /**
   * Is true if decomposeIndex has been used in this context.
   */
  context::CDO<bool> d_usedDecomposeIndex;

  std::queue<Node>& d_substitutionStream;
  Lookup<uint32_t>& d_cuttingDepth;
  RequestNodeCallback& d_requestNewVariable;

  /** Returns true if the substitutions use no new variables. */
  bool hasMoreSubstitutions() const{
    return !d_subs.empty();
  }
  Node nextSubstitution();

  void enqueueSubstitutions(){
    while(!d_subs.empty()){
      SubIndex curr = d_subs.frontIndex();
      d_subs.dequeue();

      if(d_subs[curr].d_fresh.isNull()){
        continue;
      }else{
        Variable v = d_subs[curr].d_eliminated;

        SumPair sp = d_trail[d_subs[curr].d_constraint].d_eq;

        SumPair polyV = SumPair(Polynomial::mkPolynomial(v));
        SumPair cancelV = polyV + sp;

        Node eq = (v.getNode()).eqNode(cancelV.getNode());

        d_substitutionStream.push(eq);
      }
    }
  }

public:

  /** Construct a Diophantine equation solver with the given context. */
  DioSolver(context::Context* ctxt, std::queue<Node>& substitutions, Lookup<uint32_t>& cuttingDepth, RequestNodeCallback&  requestNewVariable);



  /**
   * Adds an equality to the queue of the DioSolver.
   * orig is blamed in a conflict.
   * orig can either be of the form (= p c) or (and ub lb).
   * where ub is either (leq p c) or (not (> p [- c 1])), and
   * where lb is either (geq p c) or (not (< p [+ c 1]))
   */
  void pushInputConstraint(const Comparison& eq, Node reason);

  /**
   * Processes the queue looking for any conflict.
   * If a conflict is found, this returns conflict.
   * Otherwise, it returns null.
   * The conflict is guarenteed to be over literals given in addEquality.
   */
  Node processEquationsForConflict();

  /**
   * Processes the queue looking for an integer unsatisfiable cutting plane.
   * If such a plane is found this returns an entailed plane using no
   * fresh variables.
   */
  SumPair processEquationsForCut();

private:
  /** Returns true if the TrailIndex refers to a element in the trail. */
  bool inRange(TrailIndex i) const{
    return i < d_trail.size();
  }

  Node columnGcdIsOne() const;


  /**
   * Returns true if the context dependent flag for conflicts
   * has been raised.
   */
  bool inConflict() const{
    return d_conflictHasBeenRaised;
  }

  /** Raises a conflict at the index ti. */
  void raiseConflict(TrailIndex ti){
    Assert(!inConflict());
    d_conflictHasBeenRaised = true;
    d_conflictIndex = ti;
  }

  /** Returns the conflict index. */
  TrailIndex getConflictIndex() const{
    Assert(inConflict());
    return d_conflictIndex;
  }

  /**
   * Allocates a "unique" variables from the pool of integer variables.
   * This variable is fresh with respect to the context.
   * Returns index of the variable in d_variablePool;
   */
  //size_t allocateVariableInPool();

  /**
   * Returns true if the node can be accepted as a reason according to the
   * kinds.
   */
  bool acceptableOriginalNodes(Node n);

  /** Empties the unproccessed input constraints into the queue. */
  void enqueueInputConstraints();

  /**
   * Returns true if an input equality is in the map.
   * This is expensive and is only for debug assertions.
   */
  bool debugEqualityInInputEquations(Node eq);

  /** Applies the substitution at subIndex to currentF. */
  void subAndReduceCurrentFByIndex(SubIndex d_subIndex);

  /**
   * Takes as input a TrailIndex i and an integer that divides d_trail[i].d_eq, and
   * returns a TrailIndex j s.t.
   *   d_trail[j].d_eq = (1/g) d_trail[i].d_eq
   * and
   *   d_trail[j].d_proof = (1/g) d_trail[i].d_proof.
   *
   * g must be non-zero.
   *
   * This corresponds to an application of Alberto's rule (7).
   */
  TrailIndex scaleEqAtIndex(TrailIndex i, const Integer& g);


  /**
   * Takes as input TrailIndex's i and j and Integer's q and r and a TrailIndex k s.t.
   *   d_trail[k].d_eq == d_trail[i].d_eq * q + d_trail[j].d_eq * r
   * and
   *   d_trail[k].d_proof == d_trail[i].d_proof * q + d_trail[j].d_proof * r
   *
   * This corresponds to an application of Alberto's rule (8).
   */
  TrailIndex combineEqAtIndexes(TrailIndex i, const Integer& q, TrailIndex j, const Integer& r);

  /**
   * Decomposes the equation at index ti of trail by the variable
   * with the lowest coefficient.
   * This corresponds to an application of Alberto's rule (9).
   *
   * Returns a pair of a SubIndex and a TrailIndex.
   * The SubIndex is the index of a newly introduced substition.
   */
  std::pair<SubIndex, TrailIndex> decomposeIndex(TrailIndex ti);

  /** Solves the index at ti for the value in minimumMonomial. */
  std::pair<SubIndex, TrailIndex> solveIndex(TrailIndex ti);

  /** Prints the queue for debugging purposes to Debug("arith::dio"). */
  void printQueue();

  /**
   * Exhaustively applies all substitutions discovered to an element of the trail.
   * Returns a TrailIndex corresponding to the substitutions being applied.
   */
  TrailIndex applyAllSubstitutionsToIndex(TrailIndex i);

  /**
   * Applies a substitution to an element in the trail.
   */
  TrailIndex applySubstitution(SubIndex s, TrailIndex i);

  /**
   * Reduces the trail node at i by the gcd of the variables.
   * Returns the new trail element.
   *
   * This raises the conflict flag if unsat is detected.
   */
  TrailIndex reduceByGCD(TrailIndex i);

  /**
   * Returns true if i'th element in the trail is trivially true.
   * (0 = 0)
   */
  bool triviallySat(TrailIndex t);

  /**
   * Returns true if i'th element in the trail is trivially unsatisfiable.
   * (1 = 0)
   */
  bool triviallyUnsat(TrailIndex t);

  /** Returns true if the gcd of the i'th element of the trail is 1.*/
  bool gcdIsOne(TrailIndex t);

  bool debugAnySubstitionApplies(TrailIndex t);
  bool debugSubstitutionApplies(SubIndex si, TrailIndex ti);


  /** Returns true if the queue of nodes to process is empty. */
  bool queueEmpty() const;

  bool queueConditions(TrailIndex t){
    /* debugPrintTrail(t); */
    /* std::cout << !inConflict() << std::endl; */
    /* std::cout << gcdIsOne(t) << std::endl; */
    /* std::cout << !debugAnySubstitionApplies(t) << std::endl; */
    /* std::cout << !triviallySat(t) << std::endl; */
    /* std::cout << !triviallyUnsat(t) << std::endl; */

    return
      !inConflict() &&
      gcdIsOne(t) &&
      !debugAnySubstitionApplies(t) &&
      !triviallySat(t) &&
      !triviallyUnsat(t);
  }

  void pushToQueueBack(TrailIndex t){
    Assert(queueConditions(t));
    d_currentF.push_back(t);
  }

  void pushToQueueFront(TrailIndex t){
    Assert(queueConditions(t));
    d_currentF.push_front(t);
  }

  /**
   * Moves the minimum Constraint by absolute value of the minimum coefficient to
   * the front of the queue.
   */
  void moveMinimumByAbsToQueueFront();

  void saveQueue();

  TrailIndex impliedGcdOfOne();


  /**
   * Processing the current set of equations.
   *
   * decomposeIndex() rule is only applied if allowDecomposition is true.
   */
  bool processEquations(bool allowDecomposition);

  /**
   * Constructs a proof from any d_trail[i] in terms of input literals.
   */
  Node proveIndex(TrailIndex i);

  /**
   * Returns the SumPair in d_trail[i].d_eq with all of the fresh variables purified out.
   */
  //SumPair purifyIndex(TrailIndex i);


  void debugPrintTrail(TrailIndex i) const;

public:
  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:

    IntStat d_conflictCalls;
    IntStat d_cutCalls;

    IntStat d_cuts;
    IntStat d_conflicts;

    TimerStat d_conflictTimer;
    TimerStat d_cutTimer;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
};/* class DioSolver */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__DIO_SOLVER_H */

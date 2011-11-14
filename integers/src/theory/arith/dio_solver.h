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

#include "context/context.h"
#include "context/cdexplain_dag.h"

#include "theory/arith/tableau.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/arith_utilities.h"
#include "util/rational.h"

#include <vector>
#include <utility>

namespace CVC4 {
namespace theory {
namespace arith {



class DioSolver {
private:
  typedef size_t TrailIndex;
  typedef size_t InputConstraintIndex;
  typedef size_t SubIndex;

  std::vector<Variable> d_variablePool;
  context::CDO<size_t> d_lastUsedVariable;


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
   * Each constraints is a SumPair that implicitly represents an equality against 0.
   *   d_trail[i].d_eq = (+ c (+ [(* coeff var)])) representing (+ [(* coeff var)]) = -c
   * Each constraint has a proof in terms of a linear combination of the input constraints.
   *   d_trail[i].d_proof
   *
   * See Alberto's paper for how linear proofs are maintained for the abstract
   * state machine in rules (7), (8) and (9).
   */
  struct Constraint {
    SumPair d_eq;
    Polynomial d_proof;
    Constraint(const SumPair& eq, const Polynomial& p) : d_eq(eq), d_proof(p) {}
  };
  context::CDList<Constraint> d_trail;

  /**
   * A substitution is stored as a constraint in the trail together with
   * the variable to be eliminated, and a fresh variable if one was introduced.
   * The variable d_subs[i].d_eliminated is substituted using the implicit equality in
   * d_trail[d_subs[i].d_constraint]
   *  - d_subs[i].d_eliminated is normalized to have coefficient -1 in
   *    d_trail[d_subs[i].d_constraint].
   *  - d_subs[i].d_fresh is either Node::null() or it is variable it is normalized
   *    to have coefficient 1 in d_trail[d_subs[i].d_constraint].
   */
  struct Substitution {
    Node d_fresh;
    Variable d_eliminated;
    TrailIndex d_constraint;
    Substitution(Node f, const Variable& e, TrailIndex c) :
      d_fresh(f), d_eliminated(e), d_constraint(c)
    {}
  };
  context::CDList<Substitution> d_subs;

  /**
   * This is the queue of constraints to be processed in the current context level.
   * This is to be empty upon entering solver and cleared upon leaving the solver.
   *
   * All elements in currentF:
   * - are fully substituted according to d_subs.
   * - !isConstant().
   * - If the element is (+ constant (+ [(* coeff var)] )), then the gcd(coeff) = 1
   */
  std::queue<TrailIndex> d_currentF;

  context::CDO<bool> d_conflictHasBeenRaised;
  TrailIndex d_conflictIndex;

public:

  /** Construct a Diophantine equation solver with the given context. */
  DioSolver(context::Context* ctxt) :
    d_lastUsedVariable(ctxt,0),
    d_inputConstraints(ctxt),
    d_nextInputConstraintToEnqueue(ctxt, 0),
    d_trail(ctxt),
    d_subs(ctxt),
    d_conflictHasBeenRaised(ctxt, false)
  {}

  /**
   * Adds an equality to the queue of the DioSolver.
   * orig is blamed in a conflict.
   * orig can either be an (= p c) or an (and ub lb).
   * where ub is either (leq p c) or (not (> p [- c 1])), and
   * where lb is either (geq p c) or (not (< p [+ c 1]))
   */
  //void addEquality(const Comparison& newEq, Node orig);
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

  bool inConflict() const{
    return d_conflictHasBeenRaised;
  }
  void raiseConflict(TrailIndex ti){
    Assert(!inConflict());
    d_conflictHasBeenRaised = true;
    d_conflictIndex = ti;
  }
  TrailIndex getConflictIndex() const{
    Assert(inConflict());
    return d_conflictIndex;
  }

  bool inRange(TrailIndex i) const{
    return i < d_trail.size();
  }

  /**
   * Allocates a unique variables from the pool of integer variables.
   * Returns index of the variable in d_variablePool;
   */
  size_t allocateVariableInPool();


  bool acceptableOriginalNodes(Node n);

  /** Empties the unproccessed input constraints into the queue. */
  void enqueueInputConstraints();

  /**
   * Returns true if an input equality is in the map.
   * This is expensive and is only for debug assertions.
   */
  bool debugInInputEquations(Node eq);


  /**
   * Adds the node not in the current input equalities to the pool of variables.
   * Returns the variable associated with the equality in the variable pool.
   */
  //Node addToPool(Node newEq);

  void subAndReduceCurrentFByIndex(SubIndex subIndex);

  /**
   * Appends an equality to d_facts with the proof p.
   * This should not be exposed the user.
   */
  //void internalAppendEquality(const SumPair& sp, const Polynomial& p);

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
  //void scaleEqAtIndex(Index i, const Integer& g);

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
   *
   * Returns true if the abs of the coefficient was not 1.
   * If this is the true, next indicates the replacement for ti,
   * and si is the new substitution index.
   * If this is false, si is the new substitution index and next is unchanged.
   *
   * This corresponds to an application of Alberto's rule (9).
   */
  std::pair<SubIndex, TrailIndex> decomposeIndex(TrailIndex ti);
  void subAndReduceQueue(TrailIndex ti);

  void printQueue();

  /**
   * Exhaustively applies all substitutions discovered to an element of the trail.
   * Returns a TrailIndex corresponding to the substitutions being applied.
   */
  TrailIndex applyAllSubstitutionsToIndex(TrailIndex i);

  TrailIndex applySubstitution(SubIndex s, TrailIndex i);

  /**
   * Reduces the trail node at i by the gcd of the variables.
   * Returns the new trail element.
   *
   * This raises the conflict flag if unsat is detected.
   */
  TrailIndex reduceByGCD(TrailIndex i);

  bool triviallySat(TrailIndex t);
  bool triviallyUnsat(TrailIndex t);
  bool gcdIsOne(TrailIndex t);
  bool debugSubstitionsApply(TrailIndex t);

  void pushToQueue(TrailIndex t){
    Assert(!inConflict());
    Assert(gcdIsOne(t));
    Assert(!debugSubstitionsApply(t));
    Assert(!triviallySat(t));
    Assert(!triviallyUnsat(t));

    d_currentF.push(t);
  }

  bool processEquations(bool cuts);

  /**
   * Constructs a proof from any d_trail[i] in terms of input literals.
   */
  Node proveIndex(TrailIndex i);

  /**
   * Returns the SumPair in d_trail[i].d_eq with all of the fresh variables purified out.
   */
  SumPair purifyIndex(TrailIndex i);

  /**
   * Processes the front element of the queue.
   * This can look for either conflicts or cutting planes.
   * If a conflict or a cutting plane is found, this returns true.
   * This is expected to return true or pop the queue if it returns false.
   */
  //bool processFront(bool conlict);

  //Legacy
  void getSolution();

};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__DIO_SOLVER_H */

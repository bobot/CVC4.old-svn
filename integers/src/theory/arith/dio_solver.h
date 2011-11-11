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

  std::vector<Variable> d_variablePool;
  CDO<size_t> d_lastUsedVariable;


  /**
   * The set of input constraints is stored in a CDList.
   * Each constraint point to an element of the trail.
   */
  struct InputConstraint {
    Node d_reason;
    TrailIndex d_trailPos;
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
  struct Substituion {
    Node d_fresh;
    Variable d_eliminated;
    TrailIndex d_constraint;
  };
  context::CDList<Substition> d_subs;
  
  /**
   * This is the queue of constraints to be processed in the current context level.
   * This is to be empty upon entering solver and cleared upon leaving the solver.
   *
   * All elements in currentF:
   * - are fully substituted according to d_subs.
   * - !isConstant().
   * - If the element is (+ constant (+ [(* coeff var)] )), then the gcd(coeff) = 1
   */
  std::queue<Index> d_currentF;


public:

  /** Construct a Diophantine equation solver with the given context. */
  DioSolver(context::Context* ctxt) :
    d_inputConstraints(ctxt),
    d_facts(ctxt),
    d_proofs(ctxt),
    d_queueFront(ctxt, 0),
    d_queueBack(ctxt, 0),
    d_subEliminated(ctxt),
    d_subFresh(ctxt),
    d_subRange(ctxt)
  {}

  /**
   * Adds an equality to the queue of the DioSolver.
   * orig is blamed in a conflict.
   * orig can either be an (= p c) or an (and ub lb).
   * where ub is either (leq p c) or (not (> p [- c 1])), and
   * where lb is either (geq p c) or (not (< p [+ c 1]))
   */
  void addEquality(const Comparison& newEq, Node orig);

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

  CDO<bool> d_conflictHasHasBeenRaised;
  TrailIndex d_conflictIndex;

  bool inConflict(){
    return d_conflictHasBeenRaised;
  }
  void raiseConflict(TrailIndex ti){
    Assert(!inConflict);
    d_conflictHasHasBeenRaised = true;
    d_conflictIndex = ti;
  }
  TrailIndex getConflictIndex() const{
    Assert(inConflict())
    return d_conflictIndex;
  }

  /**
   * Allocates a unique variables from the pool of integer variables.
   * Returns index of the variable in d_variablePool;
   */
  size_t allocateVariableInPool();


  bool acceptableOriginalNodes(Node n);
  /** reason must pass acceptableOriginalNodes. */
  void pushInputConstraint(const Comparison& eq, Node reason);

  /** Empties the unproccessed input constraints into the queue. */
  void DioSolver::enqueueInputConstraints();

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
   * Updates d_fact[i] := d_fact[i] * q + d_fact[j] * r
   * and updates the proof accordingly.
   *
   * This corresponds to an application of Alberto's rule (8).
   */
  void combineEqAtIndexes(Index i, const Integer& q, Index j, const Integer& r);

  /**
   * Decomposes the equation at the front of queue by the variable
   * with the lowest coefficient.
   *
   * This corresponds to an application of Alberto's rule (9).
   */
  void decomposeFront();

  Index front() const{
    return d_queueFront;
  }

  Index back() const{
    return d_queueBack;
  }

  bool empty() const{
    return front() >= back();
  }

  bool hasProof(Index i) const {
    return i <= back();
  }

  bool inRange(Index i) const {
    return front() <= i && hasProof(i);
  }


  void popQueue() {
    d_queueFront = d_queueFront + 1;
  }
  void pushQueue() {
    d_queueBack = d_queueBack + 1;
  }

  /**
   * Exhaustively applies all substitutions discovered to the front of the queue.
   */
  void applySubstitutionsToFront();

  /**
   * Constructs a proof from any d_proof[i] in terms of input literals.
   * i <= end()
   */
  Node proveIndex(Index i);

  /**
   * Returns the SumPair in d_fact[i] with all of the fresh variables purified out
   */
  SumPair purifyIndex(Index i);

  /**
   * Processes the front element of the queue.
   * This can look for either conflicts or cutting planes.
   * If a conflict or a cutting plane is found, this returns true.
   * This is expected to return true or pop the queue if it returns false.
   */
  bool processFront(bool conlict);

  //Legacy
  void getSolution();

};

// class DioSolver {
// private:
//   context::Context* d_context;

//   typedef uint32_t EquationIndex;
//   typedef context::CDExplainDAG::ProofIndex ProofIndex;

//   context::CDExplainDAG d_dioProofs;

//   context::CDVector<Node> d_equations;
//   context::CDO<EquationIndex> d_equationsBegin;
//   context::CDO<EquationIndex> d_equationsEnd;

//   /* Each item should have the form (= int_var [integer sum])
//    * This represents a mapping of int_var to integer sum.
//    */
//   context::CDList<Node> d_substitutions;

//   std::pair<const Integer&,Node> minimumAbsCoefficient(Node sum);

//   std::pair<Node, Node> quotientSolve(Node sum, Node var, const Integer& a);

//   ProofIndex lookProofIndex(Node eq){
//     return d_dioProofs.getProofIndex(eq);
//   }

//   void processFrontEquation(){
//     Assert(d_equationsBegin < d_equationsEnd);
//     EquationIndex ei = d_equationsBegin;
//     Node eq = d_equations[ei];

//     Node sum = eq[0];
//     const Integer& c = eq[1].getConst<Integer>();

//     std::pair<const Integer&, Node> p = minimumAbsCoefficient(sum);
//     const Integer& a = p.first;
//     Node var = p.second;

//     std::pair<Node, Node> qr = quotientSolve(sum, var, a);
//     Node q = qr.first;
//     Node r = qr.second;

//     if(r.isNull()){
//       Assert(d_substitutions.size() == ei);
//       d_substitutions.push_back(q);
//     }else{
//       #warning "TODOTODOTODOTODOTODOTODOTODO"
//     }
//   }

//   void proccessRemainingEquations(){
//     while(d_equationsBegin < d_equationsEnd){
//       processFrontEquation();
//       d_equationsBegin = d_equationsBegin + 1;
//     }
//   }

//   void addEquation(Node eq){
//     Assert(Comparison::isNormalAtom(eq));
//     Comparison cmp = Comparison::parseNormalForm(eq);
//     Assert(cmp.isIntegral());

//     d_dioProofs.push_fact(eq);

//     EquationIndex eqIndex = d_equationsEnd;
//     d_equations.reserve(eqIndex + 1, Node::null());

//     d_dioProofs.push_fact(eq);
//     d_equationsEnd = d_equationsEnd + 1;
//     applyAllSubstitutions(eqIndex);
//   }

//   // var |-> poly + c
//   // var = poly + c
//   // -c = poly - var
//   // c = var - poly
//   static Node substituteIntoEq(Node eq, Node vln, Node subEq){
//     Assert(eq.getKind() == kind::EQUAL);
//     Assert(subEq.getKind() == kind::EQUAL);
//     Assert(VarList::normalForm(vln));

//     VarList vl = VarList::parseVarList(vln);

//     Comparison cmp = Comparison::parseNormalForm(eq);
//     const Polynomial& left = cmp.getLeft();
//     const Constant& right = cmp.getRight();

//     Constant coeff = left.findCoefficient(vl);

//     if(coeff.isZero()){
//       return eq;
//     }else{

//       Comparison sub = Comparison::parseNormalForm(eq);
//       Constant one = left.findCoefficient(vl);
//       // v = p + c
//       // 0 = p + c - v
//       // left = r
//       // left = q + d*v
//       // q + d*v = r
//       // q + d*v + d*0 = r + 0
//       // q + d*v + d*(p + c - v) = r + 0
//       // q + d*v + d*(p + c - v) = r
//       // q + d*v + d*p + d*c - d*v = r
//       // q + d*v + d*p - d*v = r - d*c
//       // left + d*p - d*v = r - d*c
//       // q + d*p = r - d*c
//       Comparison scaledSub = sub.multiplyByConstant(coeff.negate);
//       Comparison newEq = cmp.addEquality(scaledSub);
//       return newEq.getNode();
//     }
//   }

//   void substitute(EquationIndex ei, EquationIndex subid){
//     Assert(subid < ei);
//     Node currEq = d_equations[ei];
//     Node var2Sum =  d_substitutions[subid];
//     Node var = var2Sum[0];
//     Node sum = var2Sum[1];

//     Node newEq = substituteIntoEq(currEq, var, sum);

//     if(newEq != currEq){
//       d_equations[ei] = newEq;
//       ProofIndex currEqExp = lookProofIndex(currEq);
//       ProofIndex subIdExp = lookProofIndex(d_equations[subid]);

//       ProofIndex withSubExp = d_dioProofs.push_implication(newEq, currEqExp, subIdExp);

//       if(withSub.isBoolean() && !newEq.getConst<bool>()){
//         // This must be false. True cannot be derived... right?
//         d_conflict = d_dioProofs.explain(withSubExp);
//       }
//     }
//   }

//   void applyAllSubstitutions(EquationIndex ei){
//     for(uint32_t subid = 0, end = d_substitutions.size(); subid < end; subid++){
//       substitute(ei, subid);
//     }
//   }

//   const Tableau& d_tableau;
//   ArithPartialModel& d_partialModel;

// public:



//   /** Construct a Diophantine equation solver with the given context. */
//   DioSolver(context::Context* ctxt, const Tableau& tab, ArithPartialModel& pmod) :
//     d_context(ctxt),
//     d_dioProofs(ctxt),
//     d_equations(ctxt),
//     d_equationsBegin(ctxt, 0),
//     d_equationsEnd(ctxt, 0),
//     d_substitutions(ctxt),
//     d_tableau(tab),
//     d_partialModel(pmod) {
//   }

//   /**
//    * Solve the set of Diophantine equations in the tableau.
//    *
//    * @return true if the set of equations was solved; false if no
//    * solution
//    */
//   bool solve();

//   /**
//    * Get the parameterized solution to this set of Diophantine
//    * equations.  Must be preceded by a call to solve() that returned
//    * true. */
//   void getSolution();

// };/* class DioSolver */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__DIO_SOLVER_H */

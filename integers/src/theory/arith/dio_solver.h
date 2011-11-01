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
  typedef uint32_t EquationIndex;
  typedef context::CDExplainDAG::ProofIndex ProofIndex;

  context::CDExplainDAG d_dioProofs;

  context::CDVector<Node> d_equations;
  context::CDO<EquationIndex> d_equationsBegin;
  context::CDO<EquationIndex> d_equationsEnd;
  context::CDVector<ProofIndex> d_explanation;

  /* Each item should have the form (= int_var [integer sum])
   * This represents a mapping of int_var to integer sum.
   */
  context::CDList<Node> d_substitutions;

  std::pair<const Integer&,Node> minimumAbsCoefficient(Node sum);

  std::pair<Node, Node> quotientSolve(Node sum, Node var, const Integer& a);

  void processFrontEquation(){
    Assert(d_equationsBegin < d_equationsEnd);
    EquationIndex ei = d_equationsBegin;
    Node eq = d_equations[ei];

    Node sum = eq[0];
    const Integer& c = eq[1].getConst<Integer>();

    std::pair<const Integer&, Node> p = minimumAbsCoefficient(sum);
    const Integer& a = p.first;
    Node var = p.second;

    std::pair<Node, Node> qr = quotientSolve(sum, var, a);
    Node q = qr.first;
    Node r = qr.second;

    if(r.isNull()){
      Assert(d_substitutions.size() == ei);
      d_substitutions.push_back(q);
    }else{
      #warning "TODOTODOTODOTODOTODOTODOTODO"
    }
  }

  void proccessRemainingEquations(){
    while(d_equationsBegin < d_equationsEnd){
      processFrontEquation();
      d_equationsBegin = d_equationsBegin + 1;
    }
  }

  void addEquation(Node eq){
    Assert(Comparison::isNormalAtom(eq));
    Comparison cmp = Comparison::parseNormalForm(eq);

    d_dioProofs.push_fact(eq);

    IntegerEquality ie(cmp.getLeft(), cmp.getRight());
    if(!ie.leftGCDDividesRight()){
      d_conflict = eq;
    }else{

      EquationIndex eqIndex = d_equationsEnd;
      d_equations.reserve(eqIndex + 1);
      d_explanations.reserve(eqIndex + 1);

      Node newEq =  ie.getNode();

      d_explanations[eqIndex] = d_dioProofs.addFact(eq);
      d_equationsEnd = d_equationsEnd + 1;
      applyAllSubstiutions(eqIndex);
    }
  }

  void substitute(EquationIndex ei, EquationIndex subid){
    Assert(subid < ei);
    Node currEq = d_equations[ei];
    Node var2Sum =  d_substitutions[subid];
    Node var = var2Sum[0];
    Node sum = var2Sum[1];

    Node withSub = substituteIntoEq(currEq, var, sum);
    if(withSub != currEq){
      d_equations[ei] = withSub;
      ProofIndex currEqExp = d_explanation[ei];
      ProofIndex subIdExp = d_explanation[subid];


      Node divideByGCD=...;
      if(divideByGCD.isNull()){
        ProofIndex withSubExp = d_dioProofs.push_implication(withSub, currEqExp, subIdExp);
        d_explanations[ei] = withSubExp;
        d_conflict = d_dioProofs.explain(withSub);
      }else{
        ProofIndex dividedExp = d_dioProofs.push_implication(divideByGCD, currEqExp, subIdExp);
        d_explanations[ei] = withSubExp;
        d_conflict = d_dioProofs.explain(withSub);
      }
    }
  }

  void applyAllSubstitutions(EquationIndex ei){
    for(uint32_t subid = 0, end = d_substitutions.size(); subid < end; subid++){
      substitute(ei, subid);
    }
  }

  context::Context* d_context;
  const Tableau& d_tableau;
  ArithPartialModel& d_partialModel;

public:

  /** Construct a Diophantine equation solver with the given context. */
  DioSolver(context::Context* ctxt, const Tableau& tab, ArithPartialModel& pmod) :
    d_context(ctxt),
    d_tableau(tab),
    d_partialModel(pmod) {
  }

  /**
   * Solve the set of Diophantine equations in the tableau.
   *
   * @return true if the set of equations was solved; false if no
   * solution
   */
  bool solve();

  /**
   * Get the parameterized solution to this set of Diophantine
   * equations.  Must be preceded by a call to solve() that returned
   * true. */
  void getSolution();

};/* class DioSolver */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__DIO_SOLVER_H */

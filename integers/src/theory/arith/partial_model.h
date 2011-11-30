/*********************                                                        */
/*! \file partial_model.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
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

#include "context/context.h"
#include "context/cdvector.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/arithvar_set.h"
#include "expr/attribute.h"
#include "expr/node.h"

#include "theory/arith/difference_manager.h"

#include <deque>

#ifndef __CVC4__THEORY__ARITH__PARTIAL_MODEL_H
#define __CVC4__THEORY__ARITH__PARTIAL_MODEL_H

namespace CVC4 {
namespace theory {
namespace arith {

class ArithPartialModel {
private:

  unsigned d_mapSize;
  //Maps from ArithVar -> T

  std::vector<bool> d_hasHadABound;

  std::vector<bool> d_hasSafeAssignment;
  std::vector<DeltaRational> d_assignment;
  std::vector<DeltaRational> d_safeAssignment;

  context::CDVector<DeltaRational> d_upperBound;
  context::CDVector<DeltaRational> d_lowerBound;
  context::CDVector<Node> d_upperConstraint;
  context::CDVector<Node> d_lowerConstraint;


  bool d_deltaIsSafe;
  Rational d_delta;

  /**
   * List contains all of the variables that have an unsafe assignment.
   */
  typedef std::vector<ArithVar> HistoryList;
  HistoryList d_history;

  /**
   * List of the types of variables in the system.
   * "True" means integer, "false" means (non-integer) real.
   */
  std::vector<bool> d_varTypes;

  /** Set of all integer variables with rational assignments in the partial model. */
  ArithVarSet d_integerVarsWithRationalAssignment;

  /**
   * On full effort checks (after determining LA(Q) satisfiability), we
   * consider integer vars, but we make sure to do so fairly to avoid
   * nontermination (although this isn't a guarantee).  To do it fairly,
   * we consider variables in round-robin[ish] fashion.  This is the
   * round-robin[ish] index.
   */
  ArithVar d_nextIntegerIter;

  context::CDList<ArithVar> d_integerVarsWithEqualBounds;
  context::CDO<unsigned int> d_ivwebIterator;

  DifferenceManager& d_dm;

public:

  ArithPartialModel(context::Context* c, DifferenceManager& dm):
    d_mapSize(0),
    d_hasHadABound(),
    d_hasSafeAssignment(),
    d_assignment(),
    d_safeAssignment(),
    d_upperBound(c, true),
    d_lowerBound(c, true),
    d_upperConstraint(c,true),
    d_lowerConstraint(c,true),
    d_deltaIsSafe(false),
    d_delta(-1,1),
    d_history(),
    d_varTypes(),
    d_integerVarsWithRationalAssignment(),
    d_nextIntegerIter(0),
    d_integerVarsWithEqualBounds(c, false),
    d_ivwebIterator(c,0),
    d_dm(dm)
  { }

  void pushBackIntegerVarsWithEqualBounds(ArithVar x) {
    d_integerVarsWithEqualBounds.push_back(x);
  }

  bool hasMoreIntegerVarsWithEqualBounds() const{
    return d_ivwebIterator < d_integerVarsWithEqualBounds.size();
  }

  ArithVar nextIntegerVarsWithEqualBounds() {
    Assert(hasMoreIntegerVarsWithEqualBounds());
    ArithVar res = d_integerVarsWithEqualBounds[d_ivwebIterator];
    d_ivwebIterator = d_ivwebIterator + 1;
    return res;
  }

  TNode getLowerConstraint(ArithVar x);
  TNode getUpperConstraint(ArithVar x);


  /* Initializes a variable to a safe value.*/
  void initialize(ArithVar x, const DeltaRational& r, bool integer);

  /* Gets the last assignment to a variable that is known to be consistent. */
  const DeltaRational& getSafeAssignment(ArithVar x) const;
  const DeltaRational& getAssignment(ArithVar x, bool safe) const;

  /* Reverts all variable assignments to their safe values. */
  void revertAssignmentChanges();

  /* Commits all variables assignments as safe.*/
  void commitAssignmentChanges();


  inline bool lowerBoundIsZero(ArithVar x){
    return hasLowerBound(x) && getLowerBound(x).sgn() == 0;
  }

  inline bool upperBoundIsZero(ArithVar x){
    return hasUpperBound(x) && getUpperBound(x).sgn() == 0;
  }

private:
  void setLowerConstraint(ArithVar x, TNode constraint);
  void setUpperConstraint(ArithVar x, TNode constraint);

  void zeroDifferenceDetected(ArithVar x);


  void setUpperBound(ArithVar x, const DeltaRational& r);
  void setLowerBound(ArithVar x, const DeltaRational& r);



public:
  bool boundsAreEqual(ArithVar x);

  void setUpperBound(ArithVar x, const DeltaRational& r, TNode con);
  void setLowerBound(ArithVar x, const DeltaRational& r, TNode con);

  /* Sets an unsafe variable assignment */
  void setAssignment(ArithVar x, const DeltaRational& r);
  void setAssignment(ArithVar x, const DeltaRational& safe, const DeltaRational& r);


  /** Must know that the bound exists before calling this! */
  const DeltaRational& getUpperBound(ArithVar x);
  const DeltaRational& getLowerBound(ArithVar x);
  const DeltaRational& getAssignment(ArithVar x) const;



  /**
   * x >= l
   * ? c < l
   */
  bool belowLowerBound(ArithVar x, const DeltaRational& c, bool strict);

  /**
   * x <= u
   * ? c > u
   */
  bool aboveUpperBound(ArithVar x, const DeltaRational& c, bool strict);

  bool equalsLowerBound(ArithVar x, const DeltaRational& c);
  bool equalsUpperBound(ArithVar x, const DeltaRational& c);

  /**
   * x <= u
   * ? c < u
   */
  bool strictlyBelowUpperBound(ArithVar x, const DeltaRational& c);

  /**
   * x <= u
   * ? c < u
   */
  bool strictlyAboveLowerBound(ArithVar x, const DeltaRational& c);

  bool strictlyBelowUpperBound(ArithVar x);
  bool strictlyAboveLowerBound(ArithVar x);
  bool assignmentIsConsistent(ArithVar x);

  void printModel(ArithVar x);

  /** returns true iff x has both a lower and upper bound. */
  bool hasEitherBound(ArithVar x);
  inline bool hasLowerBound(ArithVar x){
    return !d_lowerConstraint[x].isNull();
  }
  inline bool hasUpperBound(ArithVar x){
    return !d_upperConstraint[x].isNull();
  }

  bool hasEverHadABound(ArithVar var){
    return d_hasHadABound[var];
  }

  const Rational& getDelta(){
    if(!d_deltaIsSafe){
      computeDelta();
    }
    return d_delta;
  }

  inline bool isInteger(ArithVar x) const {
    Assert(inMaps(x));
    return d_varTypes[x];
  }

  bool isReal(ArithVar x) const {
    return !isInteger(x);
  }

  bool hasIntegerAssignment(ArithVar x) const{
    Assert(isInteger(x));
    return d_integerVarsWithRationalAssignment.isMember(x);
  }

  bool allIntegerVariablesHaveIntegerAssignments() const {
    return d_integerVarsWithRationalAssignment.empty();
  }

  ArithVar nextIntegerVariableWithNonIntegerAssignment() {
    Assert(!allIntegerVariablesHaveIntegerAssignments());
    d_nextIntegerIter++;
    d_nextIntegerIter %= d_integerVarsWithRationalAssignment.size();
    return d_integerVarsWithRationalAssignment.get(d_nextIntegerIter);
  }

private:

  void computeDelta();
  void deltaIsSmallerThan(const DeltaRational& l, const DeltaRational& u);

  /**
   * This function implements the mostly identical:
   * revertAssignmentChanges() and commitAssignmentChanges().
   */
  void clearSafeAssignments(bool revert);

  bool equalSizes();

  bool inMaps(ArithVar x) const{
    return 0 <= x && x < d_mapSize;
  }

  void checkIntegerAssignment(ArithVar x);
};/* class ArithPartialModel */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#endif /* __CVC4__THEORY__ARITH__PARTIAL_MODEL_H */

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

#include "expr/node.h"

#include "context/context.h"
#include "context/cdvector.h"
#include "context/cdo.h"

#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/constraint.h"
#include "theory/arith/difference_manager.h"


#include <vector>

#ifndef __CVC4__THEORY__ARITH__PARTIAL_MODEL_H
#define __CVC4__THEORY__ARITH__PARTIAL_MODEL_H

namespace CVC4 {
namespace theory {
namespace arith {

class ArithPartialModel {
private:

  unsigned d_mapSize;

  //Maps from ArithVar -> T
  std::vector<bool> d_hasSafeAssignment;
  std::vector<DeltaRational> d_assignment;
  std::vector<DeltaRational> d_safeAssignment;

  context::CDVector<DeltaRational> d_upperBound;
  context::CDVector<DeltaRational> d_lowerBound;
  context::CDVector<Node> d_upperConstraint;
  context::CDVector<Node> d_lowerConstraint;

  context::CDVector<Constraint> d_ubc;
  context::CDVector<Constraint> d_lbc;

  bool d_deltaIsSafe;
  Rational d_delta;

  /**
   * List contains all of the variables that have an unsafe assignment.
   */
  typedef std::vector<ArithVar> HistoryList;
  HistoryList d_history;

  DifferenceManager& d_dm;


public:

  ArithPartialModel(context::Context* c, DifferenceManager& dm):
    d_mapSize(0),
    d_hasSafeAssignment(),
    d_assignment(),
    d_safeAssignment(),
    d_upperBound(c, true),
    d_lowerBound(c, true),
    d_upperConstraint(c,true),
    d_lowerConstraint(c,true),
    d_ubc(c),
    d_lbc(c),
    d_deltaIsSafe(false),
    d_delta(-1,1),
    d_history(),
    d_dm(dm)
  { }

  void setLowerConstraint(ArithVar x, TNode constraint, Constraint c);
  void setUpperConstraint(ArithVar x, TNode constraint, Constraint c);
  TNode getLowerConstraint(ArithVar x);
  TNode getUpperConstraint(ArithVar x);


  /* Initializes a variable to a safe value.*/
  void initialize(ArithVar x, const DeltaRational& r);

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
  void zeroDifferenceDetected(ArithVar x);

public:
  bool boundsAreEqual(ArithVar x);

  void setUpperBound(ArithVar x, const DeltaRational& r);
  void setLowerBound(ArithVar x, const DeltaRational& r);

  /* Sets an unsafe variable assignment */
  void setAssignment(ArithVar x, const DeltaRational& r);
  void setAssignment(ArithVar x, const DeltaRational& safe, const DeltaRational& r);


  /** Must know that the bound exists before calling this! */
  const DeltaRational& getUpperBound(ArithVar x);
  const DeltaRational& getLowerBound(ArithVar x);
  const DeltaRational& getAssignment(ArithVar x) const;


  bool equalsLowerBound(ArithVar x, const DeltaRational& c);
  bool equalsUpperBound(ArithVar x, const DeltaRational& c);

  /**
   * If lowerbound > - \infty:
   *   return getAssignment(x).cmp(getLowerBound(x))
   * If lowerbound = - \infty:
   *   return 1
   */
  int cmpToLowerBound(ArithVar x, const DeltaRational& c);

  inline bool strictlyLessThanLowerBound(ArithVar x, const DeltaRational& c){
    return cmpToLowerBound(x, c) < 0;
  }
  inline bool lessThanLowerBound(ArithVar x, const DeltaRational& c){
    return cmpToLowerBound(x, c) <= 0;
  }

  inline bool strictlyGreaterThanLowerBound(ArithVar x, const DeltaRational& c){
    return cmpToLowerBound(x, c) > 0;
  }

  /**
   * If upperbound < \infty:
   *   return getAssignment(x).cmp(getUpperBound(x))
   * If upperbound = \infty:
   *   return -1
   */
  int cmpToUpperBound(ArithVar x, const DeltaRational& c);

  inline bool strictlyLessThanUpperBound(ArithVar x, const DeltaRational& c){
    return cmpToUpperBound(x, c) < 0;
  }

  inline bool lessThanUpperBound(ArithVar x, const DeltaRational& c){
    return cmpToUpperBound(x, c) <= 0;
  }

  inline bool strictlyGreaterThanUpperBound(ArithVar x, const DeltaRational& c){
    return cmpToUpperBound(x, c) > 0;
  }

  inline bool greaterThanUpperBound(ArithVar x, const DeltaRational& c){
    return cmpToUpperBound(x, c) >= 0;
  }


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

  const Rational& getDelta(){
    if(!d_deltaIsSafe){
      computeDelta();
    }
    return d_delta;
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

};/* class ArithPartialModel */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#endif /* __CVC4__THEORY__ARITH__PARTIAL_MODEL_H */

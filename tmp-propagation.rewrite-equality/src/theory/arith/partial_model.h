/*********************                                                        */
/*! \file partial_model.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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


#include "context/context.h"
#include "context/cdvector.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "expr/attribute.h"
#include "expr/node.h"

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
  context::CDVector<TNode> d_upperConstraint;
  context::CDVector<TNode> d_lowerConstraint;

  bool d_deltaIsSafe;
  Rational d_delta;

  /**
   * List contains all of the variables that have an unsafe assignment.
   */
  typedef std::vector<ArithVar> HistoryList;
  HistoryList d_history;

public:

  ArithPartialModel(context::Context* c):
    d_mapSize(0),
    d_hasHadABound(),
    d_hasSafeAssignment(),
    d_assignment(),
    d_safeAssignment(),
    d_upperBound(c, false),
    d_lowerBound(c, false),
    d_upperConstraint(c,false),
    d_lowerConstraint(c,false),
    d_deltaIsSafe(false),
    d_delta(-1,1),
    d_history()
  { }

  void setLowerConstraint(ArithVar x, TNode constraint);
  void setUpperConstraint(ArithVar x, TNode constraint);
  TNode getLowerConstraint(ArithVar x);
  TNode getUpperConstraint(ArithVar x);


  /* Initializes a variable to a safe value.*/
  void initialize(ArithVar x, const DeltaRational& r);

  /* Gets the last assignment to a variable that is known to be conistent. */
  const DeltaRational& getSafeAssignment(ArithVar x) const;
  const DeltaRational& getAssignment(ArithVar x, bool safe) const;

  /* Reverts all variable assignments to their safe values. */
  void revertAssignmentChanges();

  /* Commits all variables assignments as safe.*/
  void commitAssignmentChanges();




  void setUpperBound(ArithVar x, const DeltaRational& r);
  void setLowerBound(ArithVar x, const DeltaRational& r);

  /* Sets an unsafe variable assignment */
  void setAssignment(ArithVar x, const DeltaRational& r);
  void setAssignment(ArithVar x, const DeltaRational& safe, const DeltaRational& r);


  /** Must know that the bound exists before calling this! */
  const DeltaRational& getUpperBound(ArithVar x);
  const DeltaRational& getLowerBound(ArithVar x);
  const DeltaRational& getAssignment(ArithVar x) const;


  bool betweenAssignmentAndUpperBound(ArithVar basic, const DeltaRational& c){
    if(hasUpperBound(basic)){
      return getAssignment(basic) <= c && c < getUpperBound(basic);
    }else{
      return getAssignment(basic) <= c;
    }
  }

  bool betweenAssignmentAndLowerBound(ArithVar basic, const DeltaRational& c){
    if(hasLowerBound(basic)){
      return getAssignment(basic) >= c && c > getLowerBound(basic);
    }else{
      return getAssignment(basic) >= c;
    }
  }

  /**
   * x <= l
   * ? c < l
   */
  bool belowLowerBound(ArithVar x, const DeltaRational& c, bool strict);

  /**
   * x <= u
   * ? c < u
   */
  bool aboveUpperBound(ArithVar x, const DeltaRational& c, bool strict);

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

};




}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */



#endif /* __CVC4__THEORY__ARITH__PARTIAL_MODEL_H */

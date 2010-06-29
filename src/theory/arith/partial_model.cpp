/*********************                                                        */
/*! \file partial_model.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
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


#include "theory/arith/partial_model.h"
#include "theory/arith/slack.h"
#include "util/output.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
using namespace CVC4::theory::arith::partial_model;

void ArithPartialModel::setUpperBound(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setUpperBound(" << x << "," << r << ")" << endl;

  d_UpperBoundMap[x] = r;
}

void ArithPartialModel::setLowerBound(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
  Debug("partial_model") << "setLowerBound(" << x << "," << r << ")" << endl;
  d_LowerBoundMap[x] = r;
}

void ArithPartialModel::setAssignment(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  d_assignmentMap[x] = r;
}

void ArithPartialModel::initialize(TNode x, const DeltaRational& r){
   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
   Assert(d_assignmentMap.find(x) == d_assignmentMap.end());

   d_assignmentMap.insertAtContextLevelZero(x, r);

   Debug("partial_model") << "pm: constructing an assignment for " << x
                          << " initially " << r <<endl;
}

/** Must know that the bound exists both calling this! */
DeltaRational ArithPartialModel::getUpperBound(TNode x) const {
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
  Assert(i != d_UpperBoundMap.end());

  return (*i).second;
}

DeltaRational ArithPartialModel::getLowerBound(TNode x) const{
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
  Assert(i != d_LowerBoundMap.end());

  return ((*i).second);
}

void ArithPartialModel::computeMult(TNode mult, DeltaRational& acc){
  Assert(mult.getKind() == kind::MULT);

  if(mult.getNumChildren() == 2){
    Assert(mult[0].getKind() == kind::CONST_RATIONAL);
    Assert(mult[1].getMetaKind() == kind::metakind::VARIABLE);

    DeltaRational d (getAssignment(mult[1]));
    d *= mult[0].getConst<Rational>();

    acc += d;
  }else{
    Unhandled();
  }
}
DeltaRational ArithPartialModel::computeSum(TNode sum){
  Assert(sum.getKind() == kind::PLUS);
  DeltaRational accumulator; // initially 0

  for(TNode::iterator i = sum.begin(); i != sum.end(); ++i){
    TNode mult = *i;
    Assert(mult.getKind() == kind::MULT);
    computeMult(mult, accumulator);
  }

  return accumulator;
}

DeltaRational ArithPartialModel::getAssignment(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  CDDRationalMap::iterator i = d_assignmentMap.find(x);
  if( i == d_assignmentMap.end()){
    Assert(x.hasAttribute(ReverseSlack()));
    TNode sum = x.getAttribute(ReverseSlack());

    DeltaRational compute = computeSum(sum);
    setAssignment(x, compute);

    i = d_assignmentMap.find(x);
    Assert(i != d_assignmentMap.end());
  }

  return ((*i).second);
}



void ArithPartialModel::setLowerConstraint(TNode x, TNode constraint){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setLowerConstraint("
                         << x << ":" << constraint << ")" << endl;

  x.setAttribute(partial_model::LowerConstraint(),constraint);
}

void ArithPartialModel::setUpperConstraint(TNode x, TNode constraint){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setUpperConstraint("
                         << x << ":" << constraint << ")" << endl;

  x.setAttribute(partial_model::UpperConstraint(),constraint);
}

TNode ArithPartialModel::getLowerConstraint(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  TNode ret;
  AlwaysAssert(x.getAttribute(partial_model::LowerConstraint(),ret));
  return ret;
}

TNode ArithPartialModel::getUpperConstraint(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  TNode ret;
  AlwaysAssert(x.getAttribute(partial_model::UpperConstraint(),ret));
  return ret;
}


bool ArithPartialModel::belowLowerBound(TNode x, const DeltaRational& c, bool strict){
  CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
  if(i == d_LowerBoundMap.end()){
    // l = -\intfy
    // ? c < -\infty |-  _|_
    return false;
  }

  const DeltaRational& l = (*i).second;

  if(strict){
    return c < l;
  }else{
    return c <= l;
  }
}

bool ArithPartialModel::aboveUpperBound(TNode x, const DeltaRational& c, bool strict){
  CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
  if(i == d_UpperBoundMap.end()){
    // u = -\intfy
    // ? u < -\infty |-  _|_
    return false;
  }
  const DeltaRational& u = (*i).second;

  if(strict){
    return c > u;
  }else{
    return c >= u;
  }
}

bool ArithPartialModel::strictlyBelowUpperBound(TNode x){
  const DeltaRational& assign = getAssignment(x);

  CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
  if(i == d_UpperBoundMap.end()){// u = \infty
    return true;
  }

  const DeltaRational& u = (*i).second;
  return assign < u;
}

bool ArithPartialModel::strictlyAboveLowerBound(TNode x){
  const DeltaRational& assign = getAssignment(x);

  CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
  if(i == d_LowerBoundMap.end()){// l = \infty
    return true;
  }

  const DeltaRational& l = (*i).second;
  return l < assign;
}

bool ArithPartialModel::assignmentIsConsistent(TNode x){
  const DeltaRational& beta = getAssignment(x);

  bool above_li = !belowLowerBound(x,beta,true);
  bool below_ui = !aboveUpperBound(x,beta,true);

  //l_i <= beta(x_i) <= u_i
  return  above_li && below_ui;
}


void ArithPartialModel::printModel(TNode x){

  Debug("model") << "model" << x << ":"<< getAssignment(x) << " ";

  CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
  if(i != d_LowerBoundMap.end()){
    DeltaRational l = (*i).second;
    Debug("model") << l << " ";
    Debug("model") << getLowerConstraint(x) << " ";
  }else{
    Debug("model") << "no lb ";
  }

  i = d_UpperBoundMap.find(x);
  if(i != d_UpperBoundMap.end()){
    DeltaRational u = (*i).second;
    Debug("model") << u << " ";
    Debug("model") << getUpperConstraint(x) << " ";
  }else{
    Debug("model") << "no ub ";
  }
  Debug("model") << endl;
}

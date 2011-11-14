/*********************                                                        */
/*! \file dio_solver.cpp
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

#include "theory/arith/dio_solver.h"

#include <iostream>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

size_t DioSolver::allocateVariableInPool() {
  Assert(d_lastUsedVariable <= d_variablePool.size());
  if(d_lastUsedVariable == d_variablePool.size()){
    Assert(d_lastUsedVariable == d_variablePool.size());
    Node intVar = makeIntegerVariable();
    d_variablePool.push_back(Variable(intVar));
  }

  d_lastUsedVariable = d_lastUsedVariable + 1;
  return d_lastUsedVariable;
}



bool DioSolver::debugInInputEquations(Node eq){
  typedef context::CDList<InputConstraint>::const_iterator const_iterator;
  const_iterator i=d_inputConstraints.begin(), end = d_inputConstraints.end();
  for(; i != end; ++i){
    Node reason_i = (*i).d_reason;
    if(eq == reason_i){
      return true;
    }
  }
  return false;
}

bool DioSolver::acceptableOriginalNodes(Node n){
  Kind k = n.getKind();
  if(k == kind::EQUAL){
    return true;
  }else if(k == kind::AND){
    Node ub = n[0];
    Node lb = n[1];
    Kind kub = simplifiedKind(ub);
    Kind klb = simplifiedKind(lb);
    return (kub == kind::LEQ || kub==kind::LT) && (klb == kind::GEQ || klb == kind::GT);
  }else{
    return false;
  }
}

void DioSolver::pushInputConstraint(const Comparison& eq, Node reason){
  Assert(!debugInInputEquations(reason));
  Assert(eq.isInteger());
  Assert(eq.getNode().getKind() == kind::EQUAL);
  Assert(acceptableOriginalNodes(reason));

  SumPair sp = comparisonToSumPair(eq);

  size_t varIndex = allocateVariableInPool();
  Variable proofVariable(d_variablePool[varIndex]);

  TrailIndex posInTrail = d_trail.size();
  d_trail.push_back(Constraint(sp,Polynomial(Monomial(VarList(proofVariable)))));

  size_t posInConstraintList = d_inputConstraints.size();
  d_inputConstraints.push_back(InputConstraint(reason, posInTrail));

  d_varToInputConstraintMap[proofVariable.getNode()] = posInConstraintList;
}

// Node DioSolver::addToPool(Node newEq){
//   Assert(!debugInInputEquations(newEq));

//   size_t pos = d_inputConstraints.size();
//   d_inputConstraints.push_back(newEq);

//   Node var = Node::null();
//   Assert(pos <= d_variablePool.size());
//   if(pos == d_variablePool.size()){
//     Assert(d_inputConstraints.size() == 1+d_variablePool.size());
//     var = makeIntegerVariable();
//     d_variablePool.push_back(var);
//   }else{
//     var = d_variablePool[pos];
//   }
//   Assert(!var.isNull());

//   //If it belongs to the map already or it is not in the map, update the address
//   d_nodeToPoolMap[var] = pos;

//   return var;
// }


// void DioSolver::internalAppendEquality(const SumPair& sp, const Polynomial& p){
//   Index last = back();

//   d_facts.reserve(last+1, SumPair::mkZero());
//   d_proofs.reserve(last+1, Polynomial::mkZero());

//   d_facts.set(last, sp);
//   d_proofs.set(last, p);

//   pushQueue();
// }


// void DioSolver::addEquality(const Comparison& eq, Node orig){
//   Assert(!debugInInputEquations(orig));
//   Assert(eq.isInteger());
//   Assert(acceptableOriginalNodes(orig));

//   SumPair sp = comparisonToSumPair(eq);

//   Node var = addToPool(orig);
//   Assert(Variable::isMember(var));
//   Polynomial pvar = Polynomial(Monomial(VarList(Variable(var))));
//   internalAppendEquality(sp, pvar);
// }


DioSolver::TrailIndex DioSolver::scaleEqAtIndex(DioSolver::TrailIndex i, const Integer& g){
  Assert(g != 0);
  Constant invg = Constant::mkConstant(Rational(Integer(1),g));
  const SumPair& sp = d_trail[i].d_eq;
  const Polynomial& proof = d_trail[i].d_proof;

  SumPair newSP = sp * invg;
  Polynomial newProof = proof * invg;

  Assert(newSP.isInteger());
  Assert(newSP.gcd() == 1);

  TrailIndex j = d_trail.size();

  d_trail.push_back(Constraint(newSP, newProof));

  Debug("arith::dio") << "scaleEqAtIndex(" << i <<","<<g<<")"<<endl;
  Debug("arith::dio") << "derived "<< newSP.getNode()
                      <<" with proof " << newProof.getNode() << endl;
  return j;
}

Node DioSolver::proveIndex(TrailIndex i){
  Assert(inRange(i));
  const Polynomial& proof = d_trail[i].d_proof;
  Assert(!proof.isConstant());

  NodeBuilder<> nb(kind::AND);
  for(Polynomial::iterator iter = proof.begin(), end = proof.end(); iter!= end; ++iter){
    Monomial m = (*iter);
    Assert(!m.isConstant());
    VarList vl = m.getVarList();
    Assert(vl.singleton());
    Variable v = vl.getHead();

    Node input = proofVariableToReason(v);
    Assert(acceptableOriginalNodes(input));
    if(input.getKind() == kind::AND){
      nb << input[0] << input[1];
    }else{
      nb << input;
    }
  }

  Node result = (nb.getNumChildren() == 1) ? nb[0] : (Node)nb;
  Debug("arith::dio") << "Proof at " << i << " is "
                      << d_trail[i].d_eq.getNode() << endl
                      << d_trail[i].d_proof.getNode() << endl
                      << " which becomes " << result << endl;
  return result;
}

// Node DioSolver::proveIndex(Index i){
//   Assert(hasProof(i));
//   const Polynomial& proof = d_proofs[i];
//   Assert(!proof.isConstant()); // Is it possible for a constant proof to be okay?

//   NodeBuilder<> nb(kind::AND);
//   for(Polynomial::iterator iter = proof.begin(), end = proof.end(); iter!= end; ++iter){
//     Monomial m = (*iter);
//     Assert(!m.isConstant());
//     VarList vl = m.getVarList();
//     Assert(vl.singleton());
//     Variable v = vl.getHead();
//     Assert(d_nodeToPoolMap.find(v.getNode()) != d_nodeToPoolMap.end());
//     size_t pos = (*(d_nodeToPoolMap.find(v.getNode()))).second;
//     Assert(pos < d_inputConstraints.size());

//     Node input = d_inputConstraints[pos];
//     Assert(acceptableOriginalNodes(input));
//     if(input.getKind() == kind::AND){
//       nb << input[0] << input[1];
//     }else{
//       nb << input;
//     }
//   }

//   Node result = (nb.getNumChildren() == 1) ? nb[0] : (Node)nb;
//   Debug("arith::dio") << "Proof at " << i << " is "
//                       << d_facts[i].getNode() << endl
//                       <<  d_proofs[i].getNode() << endl
//                       << " which becomes " << result << endl;
//   return result;
// }

void DioSolver::enqueueInputConstraints(){
  Assert(d_currentF.empty());
  while(d_nextInputConstraintToEnqueue < d_inputConstraints.size()  && !inConflict()){
    size_t curr = d_nextInputConstraintToEnqueue;
    d_nextInputConstraintToEnqueue = d_nextInputConstraintToEnqueue + 1;

    TrailIndex i = d_inputConstraints[curr].d_trailPos;
    TrailIndex j = applyAllSubstitutionsToIndex(i);
    TrailIndex k = reduceByGCD(j);

    if(!inConflict()){
      if(triviallyUnsat(k)){
        raiseConflict(k);
      }else if(!triviallySat(k)){
        pushToQueue(k);
      }
    }
  }
}

bool DioSolver::processEquations(bool cuts){
  Assert(!inConflict());

  enqueueInputConstraints();
  while(!d_currentF.empty() && !inConflict()){
    TrailIndex curr = d_currentF.front();
    d_currentF.pop();

    bool hasMore;
    do {
      Assert(inRange(curr));
      Assert(!inConflict());

      Assert(gcdIsOne(curr));
      Assert(!debugSubstitionsApply(curr));
      Assert(!triviallySat(curr));
      Assert(!triviallyUnsat(curr));

      const SumPair& sp = d_trail[curr].d_eq;
      Polynomial vsum = sp.getPolynomial();
      Constant c = sp.getConstant();


      //This is unclear whether this is true or not.
      //We need to identify cases where it is false if it is not true.
      //For now this is worth it in order to assume we know
      //why conflicts occur.
      Assert(!vsum.isConstant());

      std::pair<SubIndex, TrailIndex> p = decomposeIndex(curr);
      SubIndex subIndex = p.first;
      TrailIndex next = p.second;
      subAndReduceQueue(subIndex);

      hasMore = curr != next;
      if(hasMore){
        curr = reduceByGCD(next);
      }
    }while(hasMore && !inConflict());
  }

  #warning "Add clear"
  while(!d_currentF.empty()){
    d_currentF.pop();
  }
  return inConflict();
}

Node DioSolver::processEquationsForConflict(){
  if(processEquations(false)){
    return proveIndex(getConflictIndex());
  }else{
    return Node::null();
  }
}

SumPair DioSolver::processEquationsForCut(){
  if(processEquations(true)){
    return purifyIndex(getConflictIndex());
  }else{
    return SumPair::mkZero();
  }
}


SumPair DioSolver::purifyIndex(TrailIndex i){
#warning "This uses the substition trail to reverse the substitions from the sum term. Using the proof term should be more efficient."

  SumPair curr = d_trail[i].d_eq;

  Constant negOne = Constant::mkConstant(-1);

  for(uint32_t revIter = d_subs.size(); revIter > 0; --revIter){
    uint32_t i = revIter - 1;
    Node freshNode = d_subs[i].d_fresh;
    if(freshNode.isNull()){
      continue;
    }else{
      Variable var(freshNode);
      Polynomial vsum = curr.getPolynomial();

      Constant a = vsum.getCoefficient(VarList(var));
      if(!a.isZero()){
        const SumPair& sj = d_trail[d_subs[i].d_constraint].d_eq;
        Assert(sj.getPolynomial().getCoefficient(VarList(var)).isOne());
        SumPair newSi = (curr * negOne) + (sj * a);
        Assert(newSi.getPolynomial().getCoefficient(VarList(var)).isZero());
        curr = newSi;
      }
    }
  }
  return curr;
}

// void DioSolver::processElement(bool cuts, TrailIndex curr){
//   Assert(inRange(curr));
//   Assert(!inConflict());

//   const SumPair& sp = d_trail[curr].d_eq;
//   Polynomial vsum = sp.getPolynomial();
//   Constant c = sp.getConstant();

//   Assert(no substitions apply to sp);
//   Assert(vsum.gcd().divides(c.getIntegerValue()));


//   //This is unclear whether it is true or not.
//   //We need to identify cases where it is false if it is not true.
//   //For now this is worth it in order to assume we know
//   //why conflicts occur.
//   Assert(!vsum.isConstant());

//   if(vsum.isConstant()){
//     Assert(vsum.isZero());
//     if(c.isZero()){
//       // (+ 0 0) = 0, is trivially sat
//       Debug("arith::dio") << "Proof of 0 = 0 at index " << i << endl;
//       // Skip the index
//     }else{
//       Debug("arith::dio") << "Proof of c != 0 at index " << i << endl;
//       if(!cut){
//         raiseConflict(curr);
//       }
//     }
//   }else{
//     decomposeIndex(curr);
//   //   Assert(!vsum.isConstant());
//   //   Integer g = vsum.gcd();
//   //   if(g.divides(c.getIntegerValue())){
//   //     if(g > 1){
//   //       scaleEqAtIndex(i, g);
//   //     }
//   //     decomposeFront();
//   //     return false;
//   //   }else{
//   //     Debug("arith::dio") << "The gcd of the coefficients of the variables "
//   //                         << "does not divides the constant term in "
//   //                         << sp.getNode() << endl;
//   //     return true;
//   //   }
//   // }
// }

DioSolver::TrailIndex DioSolver::combineEqAtIndexes(DioSolver::TrailIndex i, const Integer& q, DioSolver::TrailIndex j, const Integer& r){
  Constant cq = Constant::mkConstant(q);
  Constant cr = Constant::mkConstant(r);

  const SumPair& si = d_trail[i].d_eq;
  const SumPair& sj = d_trail[j].d_eq;

  Debug("arith::dio") << "combineEqAtIndexes(" << i <<","<<q<<","<<j<<","<<r<<")"<<endl;
  Debug("arith::dio") << "d_facts[i] = " << si.getNode() << endl
                      << "d_facts[j] = " << sj.getNode() << endl;


  SumPair newSi = (si * cq) + (sj * cr);


  const Polynomial& pi = d_trail[i].d_proof;
  const Polynomial& pj = d_trail[j].d_proof;
  Polynomial newPi = (pi * cq) + (pj * cr);

  TrailIndex k = d_trail.size();
  d_trail.push_back(Constraint(newSi, newPi));


  Debug("arith::dio") << "derived "<< newSi.getNode()
                      <<" with proof " << newPi.getNode() << endl;

  return k;

}

void DioSolver::printQueue(){
  Debug("arith::dio") << "DioSolver::printQueue()" << endl;
  for(TrailIndex i = 0, last = d_trail.size(); i < last; ++i){
    Debug("arith::dio") << "d_trail[i].d_eq = " << d_trail[i].d_eq.getNode() << endl;
    Debug("arith::dio") << "d_trail[i].d_proof = " << d_trail[i].d_proof.getNode() << endl;
  }

  Debug("arith::dio") << "DioSolver::printSubs()" << endl;
  for(SubIndex si=0, sN=d_subs.size(); si < sN; ++si){
    Debug("arith::dio") << "d_subs[i] = {"
                        << "d_fresh="<< d_subs[si].d_fresh <<","
                        << "d_eliminated="<< d_subs[si].d_eliminated.getNode() <<","
                        << "d_constraint="<< d_subs[si].d_constraint <<"}" << endl;
    Debug("arith::dio") << "d_trail[d_subs[i].d_constraint].d_eq="
                        << d_trail[d_subs[si].d_constraint].d_eq.getNode() << endl;
  }
}

// void DioSolver::combineEqAtIndexes(Index i, const Integer& q, Index j, const Integer& r){
//   Constant cq = Constant::mkConstant(q);
//   Constant cr = Constant::mkConstant(r);

//   const SumPair& si = d_facts[i];
//   const SumPair& sj = d_facts[j];
//   SumPair newSi = (si * cq) + (sj * cr);
//   d_facts.set(i, newSi);
//   const Polynomial& pi = d_proofs[i];
//   const Polynomial& pj = d_proofs[j];
//   Polynomial newPi = (pi * cq) + (pj * cr);
//   d_proofs.set(i, newPi);

//   Debug("arith::dio") << "combineEqAtIndexes(" << i <<","<<q<<","<<j<<","<<r<<")"<<endl;
//   Debug("arith::dio") << "derived "<< newSi.getNode()
//                       <<" with proof " << newPi.getNode() << endl;
// }

DioSolver::TrailIndex DioSolver::applyAllSubstitutionsToIndex(DioSolver::TrailIndex trailIndex){
  TrailIndex currentIndex = trailIndex;
  for(SubIndex subIter = 0, siEnd = d_subs.size(); subIter < siEnd; ++subIter){
    currentIndex = applySubstitution(subIter, currentIndex);
  }
  return currentIndex;
}

std::pair<DioSolver::SubIndex, DioSolver::TrailIndex> DioSolver::decomposeIndex(DioSolver::TrailIndex i){
  const SumPair& si = d_trail[i].d_eq;

  Debug("arith::dio") << "before decomposeIndex("<<i<<":"<<si.getNode()<< ")" << endl;

  Polynomial p = si.getPolynomial();
  Monomial av = p.selectAbsMinimum();
  VarList vl = av.getVarList();
  Assert(vl.singleton());
  Variable var = vl.getHead();
  Constant a = av.getConstant();
  Integer a_abs = a.getIntegerValue().abs();

  Assert(a_abs >= 1);
  //It is not sufficient to reduce the case where abs(a) == 1 to abs(a) > 1.
  //We need to handle both cases seperately to ensure termination.
  if(a_abs > 1){

    Node qr = SumPair::computeQR(si, a.getIntegerValue());

    Assert(qr.getKind() == kind::PLUS);
    Assert(qr.getNumChildren() == 2);
    SumPair q = SumPair::parseSumPair(qr[0]);
    SumPair r = SumPair::parseSumPair(qr[1]);

    Assert(q.getPolynomial().getCoefficient(vl) == Constant::mkConstant(1));

    Assert(!r.isZero());
    Node freshNode = makeIntegerVariable();
    Variable fresh(freshNode);
    SumPair fresh_one=SumPair::mkSumPair(fresh);
    SumPair fresh_a = fresh_one * a;

    SumPair newSI = SumPair(fresh_one) - q;
    // this normalizes the coefficient of var to -1

    SumPair newFact = r + fresh_a;

    TrailIndex nextIndex = d_trail.size();
    d_trail.push_back(Constraint(newFact, d_trail[i].d_proof));

    TrailIndex ci = d_trail.size();
    d_trail.push_back(Constraint(newSI, Polynomial::mkZero()));

    Debug("arith::dio") << "after Decompose(" << i <<":" <<  d_trail[i].d_eq.getNode()
                        << ") for " << av.getNode() << endl;
    Assert(d_trail[i].d_eq.getPolynomial().getCoefficient(vl) == Constant::mkConstant(-1));

    SubIndex subBy = d_subs.size();
    d_subs.push_back(Substitution(freshNode, var, ci));

    Debug("arith::dio") << "after Decompose front " <<  d_trail[i].d_eq.getNode() << " for " << av.getNode() << endl;
    Assert(d_trail[i].d_eq.getPolynomial().getCoefficient(vl) == Constant::mkConstant(-1));

    return make_pair(subBy, nextIndex);
  }else{
    TrailIndex ci = !a.isNegative() ? scaleEqAtIndex(i, Integer(-1)) : i;

    SubIndex subBy = d_subs.size();
    d_subs.push_back(Substitution(Node::null(), var, ci));

    Debug("arith::dio") << "after Decompose front " <<  d_trail[i].d_eq.getNode() << " for " << av.getNode() << endl;
    Assert(d_trail[i].d_eq.getPolynomial().getCoefficient(vl) == Constant::mkConstant(-1));

    return make_pair(subBy, ci);
  }
}


DioSolver::TrailIndex DioSolver::applySubstitution(DioSolver::SubIndex si, DioSolver::TrailIndex ti){
  Variable var = d_subs[si].d_eliminated;
  TrailIndex subIndex = d_subs[si].d_constraint;

  const SumPair& curr = d_trail[ti].d_eq;
  Polynomial vsum = curr.getPolynomial();

  Constant a = vsum.getCoefficient(VarList(var));
  if(!a.isZero()){
    Integer one(1);
    TrailIndex afterSub = combineEqAtIndexes(ti, one, subIndex, a.getIntegerValue());
    Assert(d_trail[afterSub].d_eq.getPolynomial().getCoefficient(VarList(var)).isZero());
    return afterSub;
  }else{
    return ti;
  }

// #warning "This is not needed but I am added for debugging."
//   for(Index i =front(), last=back(); i < last; ++i){
//     applySubstitutionsToQueue(i);
//   }
//   printQueue();
}


DioSolver::TrailIndex DioSolver::reduceByGCD(DioSolver::TrailIndex ti){
  const SumPair& sp = d_trail[ti].d_eq;
  Polynomial vsum = sp.getPolynomial();
  Constant c = sp.getConstant();
  Assert(!vsum.isConstant());
  Integer g = vsum.gcd();
  Assert(g >= 1);
  if(g.divides(c.getIntegerValue())){
    if(g > 1){
      return scaleEqAtIndex(ti, g);
    }else{
      return ti;
    }
  }else{
    raiseConflict(ti);
    return ti;
  }
}

bool DioSolver::triviallySat(TrailIndex i){
  const SumPair& eq = d_trail[i].d_eq;
  if(eq.isConstant()){
    Assert(eq.getPolynomial().isZero());
    return eq.getConstant().isZero();
  }else{
    return false;
  }
}

void DioSolver::subAndReduceCurrentFByIndex(DioSolver::SubIndex subIndex){
  for(size_t remaining = d_currentF.size(); remaining > 0 && !inConflict(); --remaining){
    TrailIndex front = d_currentF.front();
    d_currentF.pop();

    TrailIndex nextTI = applySubstitution(subIndex, front);
    if(nextTI != front){
      front = reduceByGCD(nextTI); 
    }
    if(!triviallySat(front)){
      d_currentF.push(front);
    }
  }
}

// void DioSolver::decomposeFront(){
//   Index i = front();

//   Debug("arith::dio") << "before Decompose front " <<  d_facts[i].getNode() << endl;

//   const SumPair& si = d_facts[i];
//   Polynomial p = si.getPolynomial();
//   Monomial av = p.selectAbsMinimum();
//   VarList vl = av.getVarList();
//   Assert(vl.singleton());
//   Variable var = vl.getHead();
//   Constant a = av.getConstant();
//   Integer a_abs = a.getIntegerValue().abs();

//   Node freshNode = Node::null();

//   Assert(a_abs >= 1);
//   //It is not sufficient to reduce the case where abs(a) == 1 to abs(a) > 1.
//   //We need to handle both cases seperately to ensure termination.
//   if(a_abs > 1){

//     Node qr = SumPair::computeQR(si, a_abs);
//     Assert(qr.getKind() == kind::PLUS);
//     Assert(qr.getNumChildren() == 2);
//     SumPair q = SumPair::parseSumPair(qr[0]);
//     SumPair r = SumPair::parseSumPair(qr[1]);

//     Constant c_a_abs = Constant::mkConstant(a_abs);

//     Assert(!r.isZero());
//     freshNode = makeIntegerVariable();
//     Variable fresh(freshNode);
//     SumPair fresh_one=SumPair::mkSumPair(fresh);
//     SumPair fresh_a = fresh_one * c_a_abs;

//     SumPair newSI = a.isNegative() ? SumPair(fresh_one) + q: SumPair(fresh_one) - q;
//     // this normalizes the coefficient of var to -1

//     SumPair newFact = r + fresh_a;
//     internalAppendEquality(newFact, d_proofs[i]);

//     #warning "Not sure this is what we want, but following the paper"
//     d_facts.set(i, newSI);
//     d_proofs.set(i, Polynomial::mkZero());
//   }else if(!a.isNegative()){
//     Assert(a.isOne());
//     scaleEqAtIndex(i, Integer(-1));
//   }
//   Debug("arith::dio") << "after Decompose front " <<  d_facts[i].getNode() << " for " << av.getNode() << endl;
//   Assert(d_facts[i].getPolynomial().getCoefficient(vl) == Constant::mkConstant(-1));

//   d_subEliminated.push_back(var);
//   d_subFresh.push_back(freshNode);
//   d_subRange.push_back(i);

//   popQueue();
// }
// /*
// static void printEquation(vector<Rational>& coeffs,
//                           vector<ArithVar>& variables,
//                           ostream& out) {
//   Assert(coeffs.size() == variables.size());
//   vector<Rational>::const_iterator i = coeffs.begin();
//   vector<ArithVar>::const_iterator j = variables.begin();
//   while(i != coeffs.end()) {
//     out << *i << "*" << *j;
//     ++i;
//     ++j;
//     if(i != coeffs.end()) {
//       out << " + ";
//     }
//   }
//   out << " = 0";
// }
// */

// bool DioSolver::solve() {
//   Trace("integers") << "DioSolver::solve()" << endl;
//   if(Debug.isOn("integers")) {
//     ScopedDebug dtab("tableau");
//     d_tableau.printTableau();
//   }
//   for(ArithVarSet::const_iterator i = d_tableau.beginBasic();
//       i != d_tableau.endBasic();
//       ++i) {
//     Debug("integers") << "going through row " << *i << endl;

//     Integer m = 1;
//     for(Tableau::RowIterator j = d_tableau.rowIterator(*i); !j.atEnd(); ++j) {
//       Debug("integers") << "  column " << (*j).getCoefficient() << " * " << (*j).getColVar() << endl;
//       m *= (*j).getCoefficient().getDenominator();
//     }
//     Assert(m >= 1);
//     Debug("integers") << "final multiplier is " << m << endl;

//     Integer gcd = 0;
//     Rational c = 0;
//     Debug("integers") << "going throw row " << *i << " to find gcd" << endl;
//     for(Tableau::RowIterator j = d_tableau.rowIterator(*i); !j.atEnd(); ++j) {
//       Rational r = (*j).getCoefficient();
//       ArithVar v = (*j).getColVar();
//       r *= m;
//       Debug("integers") << "  column " << r << " * " << v << endl;
//       Assert(r.getDenominator() == 1);
//       bool foundConstant = false;
//       // The tableau doesn't store constants.  Constants int he input
//       // are mapped to slack variables that are constrained with
//       // bounds in the partial model.  So we detect and accumulate all
//       // variables whose upper bound equals their lower bound, which
//       // catches these input constants as well as any (contextually)
//       // eliminated variables.
//       if(d_partialModel.hasUpperBound(v) && d_partialModel.hasLowerBound(v)) {
//         DeltaRational b = d_partialModel.getLowerBound(v);
//         if(b.getInfinitesimalPart() == 0 && b == d_partialModel.getUpperBound(v)) {
//           r *= b.getNoninfinitesimalPart();
//           Debug("integers") << "    var " << v << " == [" << b << "], so found a constant part " << r << endl;
//           c += r;
//           foundConstant = true;
//         }
//       }
//       if(!foundConstant) {
//         // calculate gcd of all (NON-constant) coefficients
//         gcd = (gcd == 0) ? r.getNumerator().abs() : gcd.gcd(r.getNumerator());
//         Debug("integers") << "    gcd now " << gcd << endl;
//       }
//     }
//     Debug("integers") << "addEquation: gcd is " << gcd << ", c is " << c << endl;
//     // The gcd must divide c for this equation to be satisfiable.
//     // If c is not an integer, there's no way it can.
//     if(c.getDenominator() == 1 && gcd == gcd.gcd(c.getNumerator())) {
//       Trace("integers") << "addEquation: this eqn is fine" << endl;
//     } else {
//       Trace("integers") << "addEquation: eqn not satisfiable, returning false" << endl;
//       return false;
//     }
//   }

//   return true;
// }

void DioSolver::getSolution() {
  Unimplemented();
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

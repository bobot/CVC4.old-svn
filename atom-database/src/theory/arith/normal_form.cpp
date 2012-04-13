/*********************                                                        */
/*! \file normal_form.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
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

#include "theory/arith/normal_form.h"
#include <list>

using namespace std;

namespace CVC4 {
namespace theory{
namespace arith {

bool VarList::isSorted(iterator start, iterator end) {
  return __gnu_cxx::is_sorted(start, end);
}

bool VarList::isMember(Node n) {
  if(Variable::isMember(n)) {
    return true;
  }
  if(n.getKind() == kind::MULT) {
    Node::iterator curr = n.begin(), end = n.end();
    Node prev = *curr;
    if(!Variable::isMember(prev)) return false;

    while( (++curr) != end) {
      if(!Variable::isMember(*curr)) return false;
      if(!(prev <= *curr)) return false;
      prev = *curr;
    }
    return true;
  } else {
    return false;
  }
}
int VarList::cmp(const VarList& vl) const {
  int dif = this->size() - vl.size();
  if (dif == 0) {
    return this->getNode().getId() - vl.getNode().getId();
  } else if(dif < 0) {
    return -1;
  } else {
    return 1;
  }
}

VarList VarList::parseVarList(Node n) {
  if(Variable::isMember(n)) {
    return VarList(Variable(n));
  } else {
    Assert(n.getKind() == kind::MULT);
    for(Node::iterator i=n.begin(), end = n.end(); i!=end; ++i) {
      Assert(Variable::isMember(*i));
    }
    return VarList(n);
  }
}

VarList VarList::operator*(const VarList& other) const {
  if(this->empty()) {
    return other;
  } else if(other.empty()) {
    return *this;
  } else {
    vector<Node> result;

    internal_iterator
      thisBegin = this->internalBegin(),
      thisEnd = this->internalEnd(),
      otherBegin = other.internalBegin(),
      otherEnd = other.internalEnd();

    merge_ranges(thisBegin, thisEnd, otherBegin, otherEnd, result);

    Assert(result.size() >= 2);
    Node mult = NodeManager::currentNM()->mkNode(kind::MULT, result);
    return VarList::parseVarList(mult);
  }
}

bool Monomial::isMember(TNode n){
  if(n.getKind() == kind::CONST_RATIONAL) {
    return true;
  } else if(multStructured(n)) {
    return VarList::isMember(n[1]);
  } else {
    return VarList::isMember(n);
  }
}

Monomial Monomial::mkMonomial(const Constant& c, const VarList& vl) {
  if(c.isZero() || vl.empty() ) {
    return Monomial(c);
  } else if(c.isOne()) {
    return Monomial(vl);
  } else {
    return Monomial(c, vl);
  }
}
Monomial Monomial::parseMonomial(Node n) {
  if(n.getKind() == kind::CONST_RATIONAL) {
    return Monomial(Constant(n));
  } else if(multStructured(n)) {
    return Monomial::mkMonomial(Constant(n[0]),VarList::parseVarList(n[1]));
  } else {
    return Monomial(VarList::parseVarList(n));
  }
}
Monomial Monomial::operator*(const Constant& c) const {
  if(c.isZero()){
    return mkZero();
  }else{
    Constant newConstant = this->getConstant() * c;
    return Monomial::mkMonomial(newConstant, getVarList());
  }
}

Monomial Monomial::operator*(const Monomial& mono) const {
  Constant newConstant = this->getConstant() * mono.getConstant();
  VarList newVL = this->getVarList() * mono.getVarList();

  return Monomial::mkMonomial(newConstant, newVL);
}

vector<Monomial> Monomial::sumLikeTerms(const std::vector<Monomial> & monos) {
  Assert(isSorted(monos));
  vector<Monomial> outMonomials;
  typedef vector<Monomial>::const_iterator iterator;
  for(iterator rangeIter = monos.begin(), end=monos.end(); rangeIter != end;) {
    Rational constant = (*rangeIter).getConstant().getValue();
    VarList varList  = (*rangeIter).getVarList();
    ++rangeIter;
    while(rangeIter != end && varList == (*rangeIter).getVarList()) {
      constant += (*rangeIter).getConstant().getValue();
      ++rangeIter;
    }
    if(constant != 0) {
      Constant asConstant = Constant::mkConstant(constant);
      Monomial nonZero = Monomial::mkMonomial(asConstant, varList);
      outMonomials.push_back(nonZero);
    }
  }

  Assert(isStrictlySorted(outMonomials));
  return outMonomials;
}

void Monomial::print() const {
  Debug("normal-form") <<  getNode() << std::endl;
}

void Monomial::printList(const std::vector<Monomial>& list) {
  for(vector<Monomial>::const_iterator i = list.begin(), end = list.end(); i != end; ++i) {
    const Monomial& m =*i;
    m.print();
  }
}
Polynomial Polynomial::operator+(const Polynomial& vl) const {

  std::vector<Monomial> sortedMonos;
  merge_ranges(begin(), end(), vl.begin(), vl.end(), sortedMonos);

  std::vector<Monomial> combined = Monomial::sumLikeTerms(sortedMonos);

  Polynomial result = mkPolynomial(combined);
  return result;
}

Polynomial Polynomial::operator-(const Polynomial& vl) const {
  Constant negOne = Constant::mkConstant(Rational(-1));

  return *this + (vl*negOne);
}

Polynomial Polynomial::operator*(const Constant& c) const{
  if(c.isZero()){
    return Polynomial::mkZero();
  }else if(c.isOne()){
    return *this;
  }else{
    std::vector<Monomial> newMonos;
    for(iterator i = this->begin(), end = this->end(); i != end; ++i) {
      newMonos.push_back((*i)*c);
    }

    Assert(Monomial::isStrictlySorted(newMonos));
    return Polynomial::mkPolynomial(newMonos);
  }
}

Polynomial Polynomial::operator*(const Monomial& mono) const {
  if(mono.isZero()) {
    return Polynomial(mono); //Don't multiply by zero
  } else {
    std::vector<Monomial> newMonos;
    for(iterator i = this->begin(), end = this->end(); i != end; ++i) {
      newMonos.push_back(mono * (*i));
    }

    // We may need to sort newMonos.
    // Suppose this = (+ x y), mono = x, (* x y).getId() < (* x x).getId()
    // newMonos = <(* x x), (* x y)> after this loop.
    // This is not sorted according to the current VarList order.
    std::sort(newMonos.begin(), newMonos.end());
    return Polynomial::mkPolynomial(newMonos);
  }
}

Polynomial Polynomial::operator*(const Polynomial& poly) const {
  Polynomial res = Polynomial::mkZero();
  for(iterator i = this->begin(), end = this->end(); i != end; ++i) {
    Monomial curr = *i;
    Polynomial prod = poly * curr;
    Polynomial sum  = res + prod;
    res = sum;
  }
  return res;
}

Monomial Polynomial::selectAbsMinimum() const {
  iterator iter = begin(), myend = end();
  Assert(iter != myend);

  Monomial min = *iter;
  ++iter;
  for(; iter != end(); ++iter){
    Monomial curr = *iter;
    if(curr.absLessThan(min)){
      min = curr;
    }
  }
  return min;
}

Integer Polynomial::gcd() const {
  //We'll use the standardization that gcd(0, 0) = 0
  //So that the gcd of the zero polynomial is gcd{0} = 0
  Assert(isIntegral());
  iterator i=begin(), e=end();
  Assert(i!=e);

  Integer d = (*i).getConstant().getValue().getNumerator().abs();
  ++i;
  for(; i!=e; ++i){
    Integer c = (*i).getConstant().getValue().getNumerator();
    d = d.gcd(c);
  }
  return d;
}

Integer Polynomial::denominatorLCM() const {
  Integer tmp(1);
  for(iterator i=begin(), e=end(); i!=e; ++i){
    const Constant& c = (*i).getConstant();
    tmp = tmp.lcm(c.getValue().getDenominator());
  }
  return tmp;
}


Constant Polynomial::getCoefficient(const VarList& vl) const{
  //TODO improve to binary search...
  for(iterator iter=begin(), myend=end(); iter != myend; ++iter){
    Monomial m = *iter;
    VarList curr = m.getVarList();
    if(curr == vl){
      return m.getConstant();
    }
  }
  return Constant::mkConstant(0);
}

Node Polynomial::computeQR(const Polynomial& p, const Integer& div){
  Assert(p.isIntegral());
  std::vector<Monomial> q_vec, r_vec;
  Integer tmp_q, tmp_r;
  for(iterator iter = p.begin(), pend = p.end(); iter != pend; ++iter){
    Monomial curr = *iter;
    VarList vl = curr.getVarList();
    Constant c = curr.getConstant();

    const Integer& a = c.getValue().getNumerator();
    Integer::floorQR(tmp_q, tmp_r, a, div);
    Constant q=Constant::mkConstant(tmp_q);
    Constant r=Constant::mkConstant(tmp_r);
    if(!q.isZero()){
      q_vec.push_back(Monomial::mkMonomial(q, vl));
    }
    if(!r.isZero()){
      r_vec.push_back(Monomial::mkMonomial(r, vl));
    }
  }

  Polynomial p_q = Polynomial::mkPolynomial(q_vec);
  Polynomial p_r = Polynomial::mkPolynomial(r_vec);

  return NodeManager::currentNM()->mkNode(kind::PLUS, p_q.getNode(), p_r.getNode());
}

Node SumPair::computeQR(const SumPair& sp, const Integer& div){
  Assert(sp.isIntegral());

  const Integer& constant = sp.getConstant().getValue().getNumerator();

  Integer constant_q, constant_r;
  Integer::floorQR(constant_q, constant_r, constant, div);

  Node p_qr = Polynomial::computeQR(sp.getPolynomial(), div);
  Assert(p_qr.getKind() == kind::PLUS);
  Assert(p_qr.getNumChildren() == 2);

  Polynomial p_q = Polynomial::parsePolynomial(p_qr[0]);
  Polynomial p_r = Polynomial::parsePolynomial(p_qr[1]);

  SumPair sp_q(p_q, Constant::mkConstant(constant_q));
  SumPair sp_r(p_r, Constant::mkConstant(constant_r));

  return NodeManager::currentNM()->mkNode(kind::PLUS, sp_q.getNode(), sp_r.getNode());
}

Comparison Comparison::parseNormalForm(TNode n) {
  Comparison result(n);
  Assert(result.isNormalForm());
  return result;
}

Node Comparison::toNode(Kind k, const Polynomial& l, const Polynomial& r) {
  Assert(isRelationOperator(k));
  switch(k) {
  case kind::GEQ:
  case kind::EQUAL:
  case kind::GT:
    return NodeManager::currentNM()->mkNode(k, l.getNode(), r.getNode());
  case kind::LEQ:
    return toNode(kind::GEQ, r, l).notNode();
  case kind::LT:
    return toNode(kind::GT, r, l).notNode();
  default:
    Unreachable();
  }
}

bool Comparison::rightIsConstant() const {
  return getNode()[1].getKind() == kind::CONST_RATIONAL;
}

Polynomial Comparison::getLeft() const {
  Node n = getNode();
  Node left = (n.getKind() == kind::NOT ? n[0]: n)[0];
  return Polynomial::parsePolynomial(left);
}

Polynomial Comparison::getRight() const {
  Node n = getNode();
  Node right = (n.getKind() == kind::NOT ? n[0]: n)[1];
  return Polynomial::parsePolynomial(right);
}

bool Comparison::isNormalForm() const {
  switch(comparisonKind(getNode())){
  case kind::CONST_BOOLEAN:
    return true;
  case kind::GT:
    return isNormalGT();
  case kind::GEQ:
    return isNormalGEQ();
  case kind::EQUAL:
    return isNormalEquals();
  case kind::LT:
    return isNormalLT();
  case kind::LEQ:
    return isNormalLEQ();
  case kind::DISTINCT:
    return isNormalDistinct();
  default:
    return false;
  }
}

/** This must be (> qpolynomial constant) */
bool Comparison::isNormalGT() const {
  Node n = getNode();
  Assert(n.getKind() == kind::GT);
  if(!rightIsConstant()){
    return false;
  }else{
    Polynomial left = getLeft();
    if(left.containsConstant()){
      return false;
    }else if(!left.leadingCoefficientIsAbsOne()){
      return false;
    }else{
      return !left.isIntegral();
    }
  }
}

/** This must be (not (> qpolynomial constant)) */
bool Comparison::isNormalLEQ() const {
  Node n = getNode();
  Assert(n.getKind() == kind::NOT);
  Assert(n[0].getKind() == kind::GT);
  if(!rightIsConstant()){
    return false;
  }else{
    Polynomial left = getLeft();
    if(left.containsConstant()){
      return false;
    }else if(!left.leadingCoefficientIsAbsOne()){
      return false;
    }else{
      return !left.isIntegral();
    }
  }
}


/** This must be (>= qpolynomial constant) or  (>= zpolynomial constant) */
bool Comparison::isNormalGEQ() const {
  Node n = getNode();
  Assert(n.getKind() == kind::GEQ);

  if(!rightIsConstant()){
    return false;
  }else{
    Polynomial left = getLeft();
    if(left.containsConstant()){
      return false;
    }else{
      if(left.isIntegral()){
        return left.denominatorGCDisOne() && left.numeratorGCDIsOne();
      }else{
        return left.leadingCoefficientIsAbsOne();
      }
    }
  }
}

/** This must be (not (>= qpolynomial constant)) or (not (>= zpolynomial constant)) */
bool Comparison::isNormalLT() const {
  Node n = getNode();
  Assert(n.getKind() == kind::NOT);
  Assert(n[0].getKind() == kind::GEQ);

  if(!rightIsConstant()){
    return false;
  }else{
    Polynomial left = getLeft();
    if(left.containsConstant()){
      return false;
    }else{
      if(left.isIntegral()){
        return left.denominatorGCDisOne() && left.numeratorGCDIsOne();
      }else{
        return left.leadingCoefficientIsAbsOne();
      }
    }
  }
}


bool Comparison::isNormalEqualityOrDisequality() const {
  Polynomial pleft = getLeft();

  if(pleft.hasExactlyOneMonomial()){
    Monomial mleft = head();
    if(mleft.isConstant()){
      return false;
    }else{
      Polynomial pright = getRight();
      if(isIntegral()){
        if(!mleft.getConstant().positive()){
          return false;
        }else if(!pright.denominatorGCDisOne()){
          return false;
        }else if(!right.numeratorGCDIsOne()){
          return false;
        }else{
          return pright.variableMonomialAreStrictlyGreater(mleft);
        }
      }else{
        if(mleft.coefficientIsOne()){
          return pright.variableMonomialAreStrictlyGreater(mleft);
        }else{
          return false;
        }
      }
    }
  }else{
    return false;
  }
}

/** This must be (= qvarlist qpolynomial) or (= zmonomial zpolynomial)*/
bool Comparison::isNormalEquality() const {
  Node n = getNode();
  Assert(n.getKind() == kind::EQUAL);

  return isNormalEqualityOrDisequality();
}

/** This must be (not (= qvarlist qpolynomial)) or (not (= zmonomial zpolynomial))*/
bool Comparison::isNormalDisequality() const {
  Node n = getNode();
  Assert(n.getKind() == kind::NOT);
  Assert(n[0].getKind() == kind::EQUAL);

  return isNormalEqualityOrDisequality();
}

static Comparison Comparison::mkRatEqualOrDistinct(Kind k, const Polynomial& p){
  Assert(k == EQUAL || k == DISTINCT);

  if(diff.isConstant()){
    return evaluatePredicate(k, diff, Polynomial::mkZero());
  }else{
    Monomial minimalVList = diff.minimalVariableMonomial();
    Constant coeffInv = minimalVList.getCoefficient().inverse();

    Polynomial diffTimes = diff * coeffInv;

    Polynomial newLeft(minimalVList.getVarList());
    Polynomial newRight = diffTimes - minimalVList;

    return Comparison(toNode(k, newLeft, newRight));
  }
}

static Comparison Comparison::mkRatIneq(Kind k, const Polynomial& p){
  Assert( k == LT || k == LEQ || k == GEQ || k == GT);
  Assert(!p.isConstant());

  Monomial minimalVList = diff.minimalVariableMonomial();
  Constant coeffInv = minimalVList.getCoefficient().inverse();
  Polynomial diffTimes = diff * coeffInv;

  Polynomial newRight = - Polynomial(diffTimes.constantMonomial());
  Polynomial newLeft = diffTimes + constantMonomial;

  return Comparison(toNode(k, newLeft, newRight));
}

static Comparison Comparison::mkIntIneq(Kind k, const Polynomial& p){
  Assert(!p.isConstant());
  Assert(p.allIntegerVariables());
  Comparison c0 = c.constantInLefthand() ? c.cancelLefthandConstant() : c;
  Comparison c1 = c0.normalizeLeadingCoefficientPositive();

  Comparison integer0 = c1.multiplyByDenominatorLCM();
  Comparison integer1 = integer0.divideByLefthandGCD();
  Comparison integer2 = integer1.tightenIntegralConstraint();
  Assert(integer2.isBoolean() || integer2.isIntegerNormalForm());
  return integer2;
}

static Comparison Comparison::mkIntEqualityOrDisequality(Kind k, const Polynomial& p){
  Assert(!p.isConstant());
  Assert(p.allIntegerVariables());
  Assert(k == EQUAL || k == DISTINCT);

  Comparison c0 = c.constantInLefthand() ? c.cancelLefthandConstant() : c;
  Comparison c1 = c0.normalizeLeadingCoefficientPositive();

  Comparison integer0 = c1.multiplyByDenominatorLCM();
  Comparison integer1 = integer0.divideByLefthandGCD();
  Comparison integer2 = integer1.tightenIntegralConstraint();
  Assert(integer2.isBoolean() || integer2.isIntegerNormalForm());
  return integer2;
}
// Comparison Comparison::normalize(Comparison c) {
//   if(c.isConstant()){
//     return c.evaluateConstant();
//   }else{
//     Comparison c0 = c.constantInLefthand() ? c.cancelLefthandConstant() : c;
//     Comparison c1 = c0.normalizeLeadingCoefficientPositive();
//     if(c1.allIntegralVariables()){
//       //All Integer Variable Case
//       Comparison integer0 = c1.multiplyByDenominatorLCM();
//       Comparison integer1 = integer0.divideByLefthandGCD();
//       Comparison integer2 = integer1.tightenIntegralConstraint();
//       Assert(integer2.isBoolean() || integer2.isIntegerNormalForm());
//       return integer2;
//     }else{
//       //Mixed case
//       Comparison mixed = c1.divideByLeadingCoefficient();
//       Assert(mixed.isMixedNormalForm());
//       return mixed;
//     }
//   }
// }

// Comparison Comparison::mkComparison(Kind k, const Polynomial& left, const Constant& right) {
//   Assert(isRelationOperator(k));
//   if(left.isConstant()) {
//     const Rational& lConst =  left.getNode().getConst<Rational>();
//     const Rational& rConst = right.getNode().getConst<Rational>();
//     bool res = evaluateConstantPredicate(k, lConst, rConst);
//     return Comparison(res);
//   }

//   if(left.getNode().getType().isPseudoboolean()) {
//     bool result;
//     if(pbComparison(k, left.getNode(), right.getNode().getConst<Rational>(), result)) {
//       return Comparison(result);
//     }
//   }

//   return Comparison(toNode(k, left, right), k, left, right);
// }

// Comparison Comparison::mkComparison(Kind k, const Polynomial& left, const Polynomial& right) {
//   Assert(isRelationOperator(k));
//   return Comparison(toNode(k, left, right), k, left, right);
// }


// bool Comparison::constantInLefthand() const{
//   return getLeft().containsConstant();
// }

// Comparison Comparison::cancelLefthandConstant() const {
//   if(constantInLefthand()){
//     Monomial constantHead = getLeft().getHead();
//     Assert(constantHead.isConstant());

//     Constant constant = constantHead.getConstant();
//     Constant negativeConstantHead = -constant;
//     return addConstant(negativeConstantHead);
//   }else{
//     return *this;
//   }
// }

Integer OrderedPolynomialPair::denominatorLCM() const {
  // Get the coefficients to be all integers.
  Integer firstDenominatorLCM = getFirst().denominatorLCM();
  Integer secondDenominatorLCM = getSecond().denominatorLCM();
  Integer denominatorLCM = secondDenominatorLCM.lcm(secondDenominatorLCM);
  Assert(denominatorLCM.sgn() > 0);
  return denominatorLCM;
}

bool Comparison::isIntegral() const {
  return getRight().isIntegral() && getLeft().isIntegral();
}

bool OrderedPolynomialPair::isConstant() const {
  return getFirst().isConstant() && getSecond().isConstant();
}

bool OrderedPolynomialPair::evaluateConstant(Kind k) const {
  Assert(getFirst().isConstant());
  Assert(getSecond().isConstant());

  const Rational& firstConst = getFirst().asConstant();
  const Rational& secondConst = getSecond().asConstant();

  return evaluateConstantPredicate(k, firstConst, secondConst);
}

OrderedPolynomialPair OrderedPolynomialPair::divideByGCD() const {
  Assert(isIntegral());

  Integer fGcd = getFirst().gcd();
  Integer sGcd = getSecond().gcd();

  Integer gcd = fGcd.gcd(sGcd);
  Polynomial newFirst = getFirst().exactDivide(gcd);
  Polynomial newSecond = getSecond().exactDivide(gcd);

  return OrderedPolynomialPair(newFirst, newSecond);
}

OrderedPolynomialPair OrderedPolynomialPair::divideByLeadingFirstCoefficient() const {
  //Handle the rational/mixed case
  Monomial head = getFirst().getHead();
  Constant leadingCoefficient = head.getConstant();
  Assert(!leadingCoefficient.isZero());

  Constant inverse = leadingCoefficient.inverse();

  return multiplyConstant(inverse);
}

OrderedPolynomialPair OrderedPolynomialPair::multiplyConstant(const Constant& c) const {
  return OrderedPolynomialPair(getFirst() * c, getSecond() * c);
}

// Comparison Comparison::divideByLeadingCoefficient() const {
//   //Handle the rational/mixed case
//   Monomial head = getLeft().getHead();
//   Constant leadingCoefficient = head.getConstant();
//   Assert(!leadingCoefficient.isZero());

//   Constant inverse = leadingCoefficient.inverse();

//   return multiplyConstant(inverse);
// }



// Comparison Comparison::tightenIntegralConstraint() const {
//   Assert(getLeft().isIntegral());

//   if(getRight().isIntegral()){
//     return *this;
//   }else{
//     switch(getKind()){
//     case kind::EQUAL:
//       //If the gcd of the left hand side does not cleanly divide the right hand side,
//       //this is unsatisfiable in the theory of Integers.
//       return Comparison(false);
//     case kind::GEQ:
//     case kind::GT:
//       {
//         //(>= l (/ n d))
//         //(>= l (ceil (/ n d)))
//         //This also hold for GT as (ceil (/ n d)) > (/ n d)
//         Integer ceilr = getRight().getValue().ceiling();
//         Constant newRight = Constant::mkConstant(ceilr);
//         return Comparison(toNode(kind::GEQ, getLeft(), newRight),kind::GEQ, getLeft(),newRight);
//       }
//     case kind::LEQ:
//     case kind::LT:
//       {
//         //(<= l (/ n d))
//         //(<= l (floor (/ n d)))
//         //This also hold for LT as (floor (/ n d)) < (/ n d)
//         Integer floor = getRight().getValue().floor();
//         Constant newRight = Constant::mkConstant(floor);
//         return Comparison(toNode(kind::LEQ, getLeft(), newRight),kind::LEQ, getLeft(),newRight);
//       }
//     default:
//       Unreachable();
//     }
//   }
// }

// bool Comparison::isIntegerNormalForm() const{
//   if(constantInLefthand()){ return false; }
//   else if(getLeft().getHead().getConstant().isNegative()){ return false; }
//   else if(!isIntegral()){ return false; }
//   else {
//     return getLeft().gcd() == 1;
//   }
// }
// bool Comparison::isMixedNormalForm() const {
//   if(constantInLefthand()){ return false; }
//   else if(allIntegralVariables()) { return false; }
//   else{
//     return getLeft().getHead().getConstant().getValue() == 1;
//   }
// }

// Comparison Comparison::normalize(Comparison c) {
//   if(c.isConstant()){
//     return c.evaluateConstant();
//   }else{
//     Comparison c0 = c.constantInLefthand() ? c.cancelLefthandConstant() : c;
//     Comparison c1 = c0.normalizeLeadingCoefficientPositive();
//     if(c1.allIntegralVariables()){
//       //All Integer Variable Case
//       Comparison integer0 = c1.multiplyByDenominatorLCM();
//       Comparison integer1 = integer0.divideByLefthandGCD();
//       Comparison integer2 = integer1.tightenIntegralConstraint();
//       Assert(integer2.isBoolean() || integer2.isIntegerNormalForm());
//       return integer2;
//     }else{
//       //Mixed case
//       Comparison mixed = c1.divideByLeadingCoefficient();
//       Assert(mixed.isMixedNormalForm());
//       return mixed;
//     }
//   }
// }

// Comparison Comparison::mkNormalComparison(Kind k, const Polynomial& left, const Constant& right) {
//   Comparison cmp = mkComparison(k,left,right);
//   Comparison normalized = cmp.normalize(cmp);
//   Assert(normalized.isNormalForm());
//   return normalized;
// }


Kind Comparison::comparisonKind(TNode literal){
  switch(literal.getKind()){
  case kind::CONST_BOOLEAN:
  case kind::GT:
  case kind::GEQ:
  case kind::EQUAL:
    return literal.getKind();
  case  kind::NOT:
    {
      TNode negatedAtom = literal[0];
      switch(negatedAtom.getKind()){
      case kind::GT: //(not (GT x c)) <=> (LEQ x c)
        return kind::LEQ;
      case kind::GEQ: //(not (GEQ x c)) <=> (LT x c)
        return kind::LT;
      case kind::EQUAL:
        return kind::DISTINCT;
      default:
        return  kind::UNDEFINED_KIND;
      }
    }
  default:
    return kind::UNDEFINED_KIND;
  }
}

} //namespace arith
} //namespace theory
} //namespace CVC4

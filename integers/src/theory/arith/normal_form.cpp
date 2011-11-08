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
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

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

Monomial Monomial::operator*(const Monomial& mono) const {
  Constant newConstant = this->getConstant() * mono.getConstant();
  VarList newVL = this->getVarList() * mono.getVarList();

  return Monomial::mkMonomial(newConstant, newVL);
}

vector<Monomial> Monomial::sumLikeTerms(const std::vector<Monomial> & monos) {
  Assert(isSorted(monos));

  Debug("blah") << "start sumLikeTerms" << std::endl;
  printList(monos);
  vector<Monomial> outMonomials;
  typedef vector<Monomial>::const_iterator iterator;
  for(iterator rangeIter = monos.begin(), end=monos.end(); rangeIter != end;) {
    Rational constant = (*rangeIter).getConstant().coerceToRational();
    VarList varList  = (*rangeIter).getVarList();
    ++rangeIter;
    while(rangeIter != end && varList == (*rangeIter).getVarList()) {
      constant += (*rangeIter).getConstant().coerceToRational();
      ++rangeIter;
    }
    if(constant != 0) {
      Constant asConstant = Constant::mkConstant(constant);
      Monomial nonZero = Monomial::mkMonomial(asConstant, varList);
      outMonomials.push_back(nonZero);
    }
  }
  Debug("blah") << "outmonomials" << std::endl;
  printList(monos);
  Debug("blah") << "end sumLikeTerms" << std::endl;

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
  this->printList();
  vl.printList();

  std::vector<Monomial> sortedMonos;
  merge_ranges(begin(), end(), vl.begin(), vl.end(), sortedMonos);

  std::vector<Monomial> combined = Monomial::sumLikeTerms(sortedMonos);

  Polynomial result = mkPolynomial(combined);
  result.printList();
  return result;
}

Polynomial Polynomial::operator*(const Monomial& mono) const {
  if(mono.isZero()) {
    return Polynomial(mono); //Don't multiply by zero
  } else if(mono.isOne()){
    return Polynomial(*this);
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


Node Comparison::toNode(Kind k, const Polynomial& l, const Constant& r) {
  Assert(!l.isConstant());
  Assert(isRelationOperator(k));
  switch(k) {
  case kind::GEQ:
  case kind::EQUAL:
  case kind::LEQ:
    return NodeManager::currentNM()->mkNode(k, l.getNode(),r.getNode());
  case kind::LT:
    return NodeManager::currentNM()->mkNode(kind::NOT, toNode(kind::GEQ,l,r));
  case kind::GT:
    return NodeManager::currentNM()->mkNode(kind::NOT, toNode(kind::LEQ,l,r));
  default:
    Unreachable();
  }
}

Comparison Comparison::parseNormalForm(TNode n) {
  if(n.getKind() == kind::CONST_BOOLEAN) {
    return Comparison(n.getConst<bool>());
  } else {
    bool negated = n.getKind() == kind::NOT;
    Node relation = negated ? n[0] : n;
    Assert( !negated ||
            relation.getKind() == kind::LEQ ||
            relation.getKind() == kind::GEQ);

    Polynomial left = Polynomial::parsePolynomial(relation[0]);
    Constant right(relation[1]);

    Kind newOperator = relation.getKind();
    if(negated) {
      if(newOperator == kind::LEQ) {
        newOperator = kind::GT;
      } else {
        newOperator = kind::LT;
      }
    }
    return Comparison(n, newOperator, left, right);
  }
}

// bool Comparison::pbComparison(Kind k, TNode left, const Rational& right, bool& result) {
//   AssertArgument(left.getType().isPseudoboolean(), left);
//   switch(k) {
//   case kind::LT:
//     if(right > 1) {
//       result = true;
//       return true;
//     } else if(right <= 0) {
//       result = false;
//       return true;
//     }
//     break;
//   case kind::LEQ:
//     if(right >= 1) {
//       result = true;
//       return true;
//     } else if(right < 0) {
//       result = false;
//       return true;
//     }
//     break;
//   case kind::EQUAL:
//     if(right != 0 && right != 1) {
//       result = false;
//       return true;
//     }
//     break;
//   case kind::GEQ:
//     if(right > 1) {
//       result = false;
//       return true;
//     } else if(right <= 0) {
//       result = true;
//       return true;
//     }
//     break;
//   case kind::GT:
//     if(right >= 1) {
//       result = false;
//       return true;
//     } else if(right < 0) {
//       result = true;
//       return true;
//     }
//     break;
//   default:
//     CheckArgument(false, k, "Bad comparison operator ?!");
//   }

//   return false;
// }

Comparison Comparison::mkComparison(Kind k, const Polynomial& left, const Constant& right) {
  Assert(isRelationOperator(k));
  if(left.isConstant()) {
    const Rational& lConst =  left.getNode().getConst<Rational>();
    const Rational& rConst = right.getNode().getConst<Rational>();
    bool res = evaluateConstantPredicate(k, lConst, rConst);
    return Comparison(res);
  }else if(left.isIntegral()){
    // Get the coefficients to be all integers.
    Integer dlcm = left.denominatorLCM().lcm(right.coerceDenominator());

    if(left.getHead().getConstant().isNegative()){
      dlcm *= -1;
    }

    Constant cdlcm = Constant::mkConstant(dlcm);
    Polynomial zLeft = left * cdlcm;
    Constant zRight = right * cdlcm;
    Assert(zLeft.isInteger());
    Assert(zRight.isInteger());


    Integer zr = zRight.getIntegerValue();

    Integer gcd = zLeft.gcd();
    // Divide rhs by the GCD of the coefficients of the polynomial.
    // If it divides the rhs great!
    // Otherwise, tighten inequalities and equalities are unsatisfiable.
    if(gcd.divides(zr)){
      Constant newRight = Constant::mkConstant(zr.exactQuotient(gcd));
      return Comparison(toNode(k, zLeft, newRight), k, zLeft, newRight);
    }else{
      switch(k){
      case kind::EQUAL:
        //If the gcd of the left hand side does not cleanly divide the right hand side,
        //this is unsatisfiable in the theory of Integers.
        return Comparison(false);
      case kind::GEQ:
      case kind::GT:
        {
          //(>= (* g l) r)
          //(>= l (/ r g))
          //(>= l (ceil (/ r g)))
          //This also hold for GT as (ceil (/ r g)) > (/ r g)
          Integer cdiv = zr.floorDivideQuotient(gcd);
          Constant newRight = Constant::mkConstant(cdiv);
          return Comparison(toNode(kind::GEQ, zLeft, newRight),kind::GEQ,zLeft,newRight);
        }
      case kind::LEQ:
      case kind::LT:
        {
          //(<= (* g l) r)
          //(<= l (/ r g))
          //(<= l (ceil (/ r g)))
          //This also hold for LT as (floor (/ r g)) < (/ r g)
          Integer fdiv = zr.floorDivideQuotient(gcd);
          Constant newRight = Constant::mkConstant(fdiv);
          return Comparison(toNode(kind::LEQ, zLeft, newRight),kind::LEQ,zLeft,newRight);
        }
      default:
        Unreachable();
      }
    }
  }else{
    return Comparison(toNode(k, left, right), k, left, right);
  }
}

Comparison Comparison::addConstant(const Constant& constant) const {
  Assert(!isBoolean());
  Monomial mono(constant);
  Polynomial constAsPoly( mono );
  Polynomial newLeft =  getLeft() + constAsPoly;
  Constant newRight = getRight() + constant;
  return mkComparison(oper, newLeft, newRight);
}

Comparison Comparison::multiplyConstant(const Constant& constant) const {
  Assert(!isBoolean());
  Kind newOper = constant.isNegative() ? reverseRelationKind(oper) : oper;

  return mkComparison(newOper, left*Monomial(constant), right*constant);
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
  Assert(div.sgn() >= 0);
  std::vector<Monomial> q_vec, r_vec;
  Integer tmp_q, tmp_r;
  for(iterator iter = p.begin(), pend = p.end(); iter != pend; ++iter){
    Monomial curr = *iter;
    VarList vl = curr.getVarList();
    Constant c = curr.getConstant();

    const Integer& a = c.getIntegerValue();
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

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

bool LeafList::isSorted(iterator start, iterator end) {
  return __gnu_cxx::is_sorted(start, end);
}

bool LeafList::isMember(Node n) {
  if(Leaf::isMember(n)) {
    return true;
  }
  if(n.getKind() == kind::MULT) {
    Node::iterator curr = n.begin(), end = n.end();
    Node prev = *curr;
    if(!Leaf::isMember(prev)) return false;

    while( (++curr) != end) {
      if(!Leaf::isMember(*curr)) return false;
      if(!(prev <= *curr)) return false;
      prev = *curr;
    }
    return true;
  } else {
    return false;
  }
}
int LeafList::cmp(const LeafList& ll) const {
  int dif = this->size() - ll.size();
  if (dif == 0) {
    return this->getNode().getId() - ll.getNode().getId();
  } else if(dif < 0) {
    return -1;
  } else {
    return 1;
  }
}

LeafList LeafList::parseLeafList(Node n) {
  if(Leaf::isMember(n)) {
    return LeafList(Leaf(n));
  } else {
    Assert(n.getKind() == kind::MULT);
    for(Node::iterator i=n.begin(), end = n.end(); i!=end; ++i) {
      Assert(Leaf::isMember(*i));
    }
    return LeafList(n);
  }
}

LeafList LeafList::operator*(const LeafList& other) const {
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
    return LeafList::parseLeafList(mult);
  }
}

bool Monomial::isMember(TNode n){
  if(n.getKind() == kind::CONST_RATIONAL) {
    return true;
  } else if(multStructured(n)) {
    return LeafList::isMember(n[1]);
  } else {
    return LeafList::isMember(n);
  }
}

Monomial Monomial::mkMonomial(const Constant& c, const LeafList& ll) {
  if(c.isZero() || ll.empty() ) {
    return Monomial(c);
  } else if(c.isOne()) {
    return Monomial(ll);
  } else {
    return Monomial(c, ll);
  }
}
Monomial Monomial::parseMonomial(Node n) {
  if(n.getKind() == kind::CONST_RATIONAL) {
    return Monomial(Constant(n));
  } else if(multStructured(n)) {
    return Monomial::mkMonomial(Constant(n[0]),LeafList::parseLeafList(n[1]));
  } else {
    return Monomial(LeafList::parseLeafList(n));
  }
}

Monomial Monomial::operator*(const Monomial& mono) const {
  Constant newConstant = this->getConstant() * mono.getConstant();
  LeafList newLL = this->getLeafList() * mono.getLeafList();

  return Monomial::mkMonomial(newConstant, newLL);
}

vector<Monomial> Monomial::sumLikeTerms(const std::vector<Monomial> & monos) {
  Assert(isSorted(monos));

  Debug("blah") << "start sumLikeTerms" << std::endl;
  printList(monos);
  vector<Monomial> outMonomials;
  typedef vector<Monomial>::const_iterator iterator;
  for(iterator rangeIter = monos.begin(), end=monos.end(); rangeIter != end;) {
    Rational constant = (*rangeIter).getConstant().getValue();
    LeafList varList  = (*rangeIter).getLeafList();
    ++rangeIter;
    while(rangeIter != end && varList == (*rangeIter).getLeafList()) {
      constant += (*rangeIter).getConstant().getValue();
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
Polynomial Polynomial::operator+(const Polynomial& ll) const {
  this->printList();
  ll.printList();

  std::vector<Monomial> sortedMonos;
  merge_ranges(begin(), end(), ll.begin(), ll.end(), sortedMonos);

  std::vector<Monomial> combined = Monomial::sumLikeTerms(sortedMonos);

  Polynomial result = mkPolynomial(combined);
  result.printList();
  return result;
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
    // This is not sorted according to the current LeafList order.
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

bool Comparison::pbComparison(Kind k, TNode left, const Rational& right, bool& result) {
  AssertArgument(left.getType().isPseudoboolean(), left);
  switch(k) {
  case kind::LT:
    if(right > 1) {
      result = true;
      return true;
    } else if(right <= 0) {
      result = false;
      return true;
    }
    break;
  case kind::LEQ:
    if(right >= 1) {
      result = true;
      return true;
    } else if(right < 0) {
      result = false;
      return true;
    }
    break;
  case kind::EQUAL:
    if(right != 0 && right != 1) {
      result = false;
      return true;
    }
    break;
  case kind::GEQ:
    if(right > 1) {
      result = false;
      return true;
    } else if(right <= 0) {
      result = true;
      return true;
    }
    break;
  case kind::GT:
    if(right >= 1) {
      result = false;
      return true;
    } else if(right < 0) {
      result = true;
      return true;
    }
    break;
  default:
    CheckArgument(false, k, "Bad comparison operator ?!");
  }

  return false;
}

Comparison Comparison::mkComparison(Kind k, const Polynomial& left, const Constant& right) {
  Assert(isRelationOperator(k));
  if(left.isConstant()) {
    const Rational& lConst =  left.getNode().getConst<Rational>();
    const Rational& rConst = right.getNode().getConst<Rational>();
    bool res = evaluateConstantPredicate(k, lConst, rConst);
    return Comparison(res);
  }

  if(left.getNode().getType().isPseudoboolean()) {
    bool result;
    if(pbComparison(k, left.getNode(), right.getNode().getConst<Rational>(), result)) {
      return Comparison(result);
    }
  }

  return Comparison(toNode(k, left, right), k, left, right);
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
  Kind newOper = (constant.getValue() < 0) ? reverseRelationKind(oper) : oper;

  return mkComparison(newOper, left*Monomial(constant), right*constant);
}



bool InterpretedFunction::isMember(Node n) {
  if (n.getKind() == kind::INTS_DIVISION || n.getKind() == kind::INTS_MODULUS){
    return Polynomial::isMember(n[0]) &&  Polynomial::isMember(n[1]);
  }
  return false;
}

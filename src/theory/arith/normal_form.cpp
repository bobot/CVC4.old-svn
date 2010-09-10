
#include "theory/arith/normal_form.h"
#include <list>

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;


bool VarList::isMember(Node n){
  if(n.getNumChildren() == 0){
    return Variable::isMember(n);
  }else if(n.getKind() == kind::MULT){
    Node::iterator curr = n.begin(), end = n.end();
    Node prev = *curr;
    if(!Variable::isMember(prev)) return false;

    while( (++curr) != end){
      if(!Variable::isMember(*curr)) return false;
      if(!(prev <= *curr)) return false;
      prev = *curr;
    }
    return true;
  }else{
    return false;
  }
}
int VarList::cmp(const VarList& vl) const{
  int dif = this->size() - vl.size();
  if (dif == 0){
    return this->getNode().getId() - vl.getNode().getId();
  }else if(dif < 0){
    return -1;
  }else{
    return 1;
  }
}

VarList VarList::parseVarList(Node n){
  std::list<Variable> list;
  if(n.getNumChildren() == 0){
    list.push_back(Variable(n));
  }else{
    Assert(n.getKind() == kind::MULT);
    for(Node::iterator i=n.begin(), end = n.end(); i!=end; ++i){
      list.push_back(Variable(*i));
    }
  }
  return VarList(n, list);
}

VarList VarList::operator*(const VarList& vl) const{
  std::list<Variable> result;
  std::back_insert_iterator<std::list<Variable> > bii(result);

  std::merge(list.begin(), list.end(), vl.list.begin(), vl.list.end(), bii);

  return VarList::mkVarList(result);
}

Monomial Monomial::operator*(const Monomial& mono) const {
  Constant newConstant = this->getConstant() * mono.getConstant();
  VarList newVL = this->getVarList() * mono.getVarList();

  return Monomial::mkMonomial(newConstant, newVL);
}

void Monomial::sumLikeTerms(list<Monomial> & monos){
  Assert(isSorted(monos));

  Debug("blah") << "start sumLikeTerms" << std::endl;
  printList(monos);
  typedef list<Monomial>::iterator iterator;
  for(iterator rangeIter = monos.begin(), end = monos.end(); rangeIter != end; ){
    Rational constant = (*rangeIter).getConstant().getValue();
    VarList varList  = (*rangeIter).getVarList();
    rangeIter = monos.erase(rangeIter);
    while(rangeIter != end && varList == (*rangeIter).getVarList()){
      constant += (*rangeIter).getConstant().getValue();
      rangeIter = monos.erase(rangeIter);
    }
    if(constant != 0){
      Monomial nonZero = Monomial::mkMonomial(Constant::mkConstant(constant), varList);
      monos.insert(rangeIter, nonZero);
    }
  }
  Debug("blah") << "outmonomials" << std::endl;
  printList(monos);
  Debug("blah") << "end sumLikeTerms" << std::endl;

  Assert(isStrictlySorted(monos));
}

Polynomial Polynomial::operator+(const Polynomial& vl) const{
  this->printList();
  vl.printList();

  std::list<Monomial> sortedMonos;
  std::back_insert_iterator<std::list<Monomial> > bii(sortedMonos);
  std::merge(monos.begin(), monos.end(), vl.monos.begin(), vl.monos.end(), bii);

  Monomial::sumLikeTerms(sortedMonos);

  Polynomial result = mkPolynomial(sortedMonos);
  result.printList();
  return result;
}

Polynomial Polynomial::operator*(const Monomial& mono) const{
  if(mono.isZero()){
    return Polynomial(mono); //Don't multiply by zero
  }else{
    std::list<Monomial> newMonos;
    for(iterator i = monos.begin(), end = monos.end(); i != end; ++i){
      newMonos.push_back(mono * (*i));
    }
    return Polynomial::mkPolynomial(newMonos);
  }
}

Polynomial Polynomial::operator*(const Polynomial& poly) const{

  Polynomial res = Polynomial::mkZero();
  for(iterator i = monos.begin(), end = monos.end(); i != end; ++i){
    Monomial curr = *i;
    Polynomial prod = poly * curr;
    Polynomial sum  = res + prod;
    res = sum;
  }
  return res;
}


Node Comparison::toNode(Kind k, const Polynomial& l, const Constant& r){
  Assert(!l.isConstant());
  Assert(isRelationOperator(k));
  switch(k){
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

Comparison Comparison::parseNormalForm(TNode n){
  if(n.getKind() == kind::CONST_BOOLEAN){
    return Comparison(n.getConst<bool>());
  }else{
    bool negated = n.getKind() == kind::NOT;
    Node relation = negated ? n[0] : n;
    Assert( !negated ||
            relation.getKind() == kind::LEQ ||
            relation.getKind() == kind::GEQ);

    Polynomial left = Polynomial::parsePolynomial(relation[0]);
    Constant right(relation[1]);

    Kind newOperator = relation.getKind();
    if(negated){
      if(newOperator == kind::LEQ){
        newOperator = kind::GT;
      }else{
        newOperator = kind::LT;
      }
    }
    return Comparison(n, newOperator, left, right);
  }
}

Comparison Comparison::mkComparison(Kind k, const Polynomial& left, const Constant& right){
  Assert(isRelationOperator(k));
  if(left.isConstant()){
    const Rational& rConst =  left.getNode().getConst<Rational>();
    const Rational& lConst = right.getNode().getConst<Rational>();
    bool res = evaluateConstantPredicate(k, lConst, rConst);
    return Comparison(res);
  }else{
    return Comparison(toNode(k, left, right), k, left, right);
  }
}

Comparison Comparison::addConstant(const Constant& constant) const{
  Assert(!isBoolean());
  Monomial mono(constant);
  Polynomial constAsPoly( mono );
  Polynomial newLeft =  getLeft() + constAsPoly;
  Constant newRight = getRight() + constant;
  return mkComparison(oper, newLeft, newRight);
}

Comparison Comparison::multiplyConstant(const Constant& constant) const{
  Assert(!isBoolean());
  Kind newOper = (constant.getValue() < 0) ? negateRelationKind(oper) : oper;

  return mkComparison(newOper, left*Monomial(constant), right*constant);
}

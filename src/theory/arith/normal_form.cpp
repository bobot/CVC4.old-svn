
#include "theory/arith/normal_form.h"
#include <list>

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

bool VarList::isSorted(iterator start, iterator end){
  return __gnu_cxx::is_sorted(start, end);
}

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
  if(n.getNumChildren() == 0){
    return VarList(Variable(n));
  }else{
    Assert(n.getKind() == kind::MULT);
    for(Node::iterator i=n.begin(), end = n.end(); i!=end; ++i){
      Assert(Variable::isMember(*i));
    }
    return VarList(n);
  }
}

VarList VarList::operator*(const VarList& vl) const{
  vector<Variable> result;
  vector<Variable> thisAsVec = this->asList();
  vector<Variable> vlAsVec = vl.asList();
  back_insert_iterator<vector<Variable> > bii(result);

  merge(thisAsVec.begin(), thisAsVec.end(), vlAsVec.begin(), vlAsVec.end(), bii);

  return VarList::mkVarList(result);
}

std::vector<Variable> VarList::asList() const {
  vector<Variable> res;
  for(iterator i = begin(), e = end(); i != e; ++i){
    res.push_back(*i);
  }
  return res;
}

Monomial Monomial::mkMonomial(const Constant& c, const VarList& vl){
  if(c.isZero() || vl.empty() ){
    return Monomial(c);
  }else if(c.isOne()){
    return Monomial(vl);
  }else{
    return Monomial(c, vl);
  }
}
Monomial Monomial::parseMonomial(Node n){
  if(n.getKind() == kind::CONST_RATIONAL){
    return Monomial(Constant(n));
  }else if(multStructured(n)){
    return Monomial::mkMonomial(Constant(n[0]),VarList::parseVarList(n[1]));
  }else{
    return Monomial(VarList::parseVarList(n));
  }
}

Monomial Monomial::operator*(const Monomial& mono) const {
  Constant newConstant = this->getConstant() * mono.getConstant();
  VarList newVL = this->getVarList() * mono.getVarList();

  return Monomial::mkMonomial(newConstant, newVL);
}

vector<Monomial> Monomial::sumLikeTerms(const vector<Monomial> & monos){
  Assert(isSorted(monos));

  Debug("blah") << "start sumLikeTerms" << std::endl;
  printList(monos);
  vector<Monomial> outMonomials;
  typedef vector<Monomial>::const_iterator iterator;
  for(iterator rangeIter = monos.begin(), end=monos.end(); rangeIter != end;){
    Rational constant = (*rangeIter).getConstant().getValue();
    VarList varList  = (*rangeIter).getVarList();
    ++rangeIter;
    while(rangeIter != end && varList == (*rangeIter).getVarList()){
      constant += (*rangeIter).getConstant().getValue();
      ++rangeIter;
    }
    if(constant != 0){
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

void Monomial::printList(const std::vector<Monomial>& monos){
  typedef std::vector<Monomial>::const_iterator iterator;
  for(iterator i = monos.begin(), end = monos.end(); i != end; ++i){
    Debug("blah") <<  ((*i).getNode()) << std::endl;
  }
}

Polynomial Polynomial::operator+(const Polynomial& vl) const{
  this->printList();
  vl.printList();

  std::vector<Monomial> sortedMonos;
  std::back_insert_iterator<std::vector<Monomial> > bii(sortedMonos);
  std::merge(begin(), end(), vl.begin(), vl.end(), bii);

  std::vector<Monomial> combined = Monomial::sumLikeTerms(sortedMonos);

  Polynomial result = mkPolynomial(combined);
  result.printList();
  return result;
}

Polynomial Polynomial::operator*(const Monomial& mono) const{
  if(mono.isZero()){
    return Polynomial(mono); //Don't multiply by zero
  }else{
    std::vector<Monomial> newMonos;
    for(iterator i = this->begin(), end = this->end(); i != end; ++i){
      newMonos.push_back(mono * (*i));
    }
    return Polynomial::mkPolynomial(newMonos);
  }
}

Polynomial Polynomial::operator*(const Polynomial& poly) const{

  Polynomial res = Polynomial::mkZero();
  for(iterator i = this->begin(), end = this->end(); i != end; ++i){
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


#include "expr/node.h"
#include "util/rational.h"
#include "theory/arith/arith_constants.h"
#include "theory/arith/arith_utilities.h"

#include <list>
#include <algorithm>
#include <ext/algorithm>

#ifndef __CVC4__THEORY__ARITH__NORMAL_FORM_H
#define __CVC4__THEORY__ARITH__NORMAL_FORM_H

namespace CVC4 {
namespace theory {
namespace arith {

/***********************************************/
/***************** Normal Form *****************/
/***********************************************/
/***********************************************/

/**
 * The normal form is defined by the following BNFs with guards:
 *
 * variable := n
 *   where
 *     n.getMetaKind() == metakind::VARIABLE

 * var_list := variable | (* [variable])
 *   where
 *     len [variable] >= 2

 * monomial := constant | var_list | (* constant' var_list')
 *   where
 *     constant' \not\in {0,1}

 * polynomial := monomial | (+ [monomial])

 * comparison := (|><| polynomial constant)
 *   guards
 *     |><| is GEQ, EQ, LEQ
 *     not (exists constantMonomial (monomialList polynomial))
 *     monomialCoefficient (head [monomial]) == 1

 * Normal Form for terms := polynomial
 * Normal Form for atoms := TRUE | FALSE | comparison | (not comparison)
 */

class NodeWrapper {
private:
  Node node;
public:
  NodeWrapper(Node n) : node(n) {}
  const Node& getNode() const { return node; }
protected:
  NodeWrapper() : node(Node::null()){}
  void setNode(Node n){ node = n; }
};

class Variable : public NodeWrapper {
public:
  Variable(Node n) : NodeWrapper() {
    Assert(n.getMetaKind() == kind::metakind::VARIABLE);
    setNode(n);
  }

  bool operator<(const Variable& v) const{ return getNode() < v.getNode();}
  bool operator==(const Variable& v) const{ return getNode() == v.getNode();}

};

class Constant : public NodeWrapper {
public:
  Constant(Node n) : NodeWrapper(coerceToRationalNode(n)) { }
  Constant(const Rational& rat) : NodeWrapper(mkRationalNode(rat)) {}

  const Rational& getValue() const {
    return getNode().getConst<Rational>();
  }

  bool isZero() const{ return getValue() == 0; }
  bool isOne() const{ return getValue() == 1; }

  Constant operator*(const Constant& other) const{
    return Constant(getValue() * other.getValue());
  }
  Constant operator+(const Constant& other) const{
    return Constant(getValue() + other.getValue());
  }
  Constant operator-() const{
    return Constant(-getValue());
  }
};

class VarList : public NodeWrapper {
private:
  std::list<Variable> list;

  static Node toNode(const std::list<Variable>& list){
    Assert(!list.empty());

    if(list.size() == 1){
      return (*(list.begin())).getNode();
    }else{
      NodeBuilder<> nb(kind::MULT);
      for(std::list<Variable>::const_iterator i=list.begin(), end = list.end(); i!=end; ++i){
        nb << (*i).getNode();
      }
      return Node(nb);
    }
  }

  static bool isSorted(const std::list<Variable>& l){
    return __gnu_cxx::is_sorted(l.begin(), l.end());
  }

  VarList() : NodeWrapper(Node::null()), list() {}

  VarList(Node n, const std::list<Variable>& l) : NodeWrapper(n), list(l) {
    Assert(isSorted(list));
  }

public:
  VarList(const std::list<Variable>& l) : NodeWrapper(toNode(l)), list(l) {
    Assert(isSorted(list));
  }

  int size() const{ return list.size(); }
  bool empty() const { return list.empty(); }

  static VarList parseVarList(Node n){
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

  VarList operator*(const VarList& vl) const{
    if(this->empty()) return vl; //If both are empty, vl is fine to return
    if(vl.empty()) return *this;

    std::list<Variable> result;
    std::back_insert_iterator<std::list<Variable> > bii(result);

    std::merge(this->list.begin(), this->list.end(), vl.list.begin(), vl.list.end(), bii);
    return VarList(result);
  }

  int cmp(const VarList& vl) const{
    int dif = this->size() - vl.size();
    if (dif == 0){
      return this->getNode().getId() - vl.getNode().getId();
    }else if(dif < 0){
      return -1;
    }else{
      return 1;
    }
  }

  bool operator<(const VarList& vl) const{
    return cmp(vl) < 0;
  }

  bool operator==(const VarList& vl) const{
    return cmp(vl) == 0;
  }

private:
  friend class Monomial;
};

class Monomial : public NodeWrapper {
private:
  Constant constant;
  VarList varList;
  Monomial(Node n, const Constant& c, const VarList& vl):
    NodeWrapper(n), constant(c), varList(vl)
  {
    Assert(!c.isZero() ||  vl.empty() );
    Assert( c.isZero() || !vl.empty() );

    Assert(!c.isOne() || !monomialStructured(n));
  }

  static Node toNode(const Constant& c, const VarList& vl){
    Assert(!c.isZero());
    Assert(!c.isOne());
    return NodeManager::currentNM()->mkNode(kind::MULT, c.getNode(), vl.getNode());
  }

  static bool monomialStructured(Node n){
    return n.getKind() ==  kind::MULT && n[0].getKind() == kind::CONST_RATIONAL && n.getNumChildren() == 2;
  }

public:

  Monomial(const Constant& c):
    NodeWrapper(c.getNode()), constant(c), varList()
  { }

  Monomial(const VarList& vl):
    NodeWrapper(vl.getNode()), constant(Rational(1)), varList(vl)
  {
    Assert( !varList.empty() );
  }

  Monomial(const Constant& c, const VarList& vl):
    NodeWrapper(toNode(c,vl)), constant(c), varList(vl)
  {
    Assert( !c.isZero() );
    Assert( !c.isOne() );
    Assert( !varList.empty() );

    Assert(monomialStructured(getNode()));
  }

  static Monomial safeConstruct(const Constant& c, const VarList& vl){
    if(c.isZero() || vl.empty() ){
      return Monomial(c);
    }else if(c.isOne()){
      return Monomial(vl);
    }else{
      return Monomial(c, vl);
    }
  }


  static Monomial parseMonomial(Node n){
    if(n.getKind() == kind::CONST_RATIONAL){
      return Monomial(Constant(n));
    }else if(monomialStructured(n)){
      return Monomial::safeConstruct(Constant(n[0]),VarList::parseVarList(n[1]));
    }else{
      return Monomial(VarList::parseVarList(n));
    }
  }

  static Monomial mkZero(){
    return Monomial(Constant(0));
  }
  static Monomial mkOne(){
    return Monomial(Constant(1));
  }
  const Constant& getConstant() const{ return constant; }
  const VarList& getVarList() const{ return varList; }

  bool isConstant() const{
    return varList.empty();
  }

  bool isZero() const{
    return constant.isZero();
  }

  bool coefficientIsOne() const {
    return constant.isOne();
  }

  Monomial operator*(const Monomial& mono) const {
    if(this->getConstant().isZero()){
      return *this;
    }else if (mono.getConstant().isZero()){
      return mono;
    }else{
      Constant newConstant = this->getConstant() * mono.getConstant();
      VarList newVL = this->getVarList() * mono.getVarList();

      return Monomial::safeConstruct(newConstant, newVL);
    }
  }


  int cmp(const Monomial& mono) const{
    return getVarList().cmp(mono.getVarList());
  }

  bool operator<(const Monomial& vl) const{
    return cmp(vl) < 0;
  }

  bool operator==(const Monomial& vl) const{
    return cmp(vl) == 0;
  }
};

class Polynomial : public NodeWrapper {
private:
  std::list<Monomial> monos;

  Polynomial(Node n, const std::list<Monomial>& m):
    NodeWrapper(n), monos(m)
  {
    Assert( !monos.empty() );
    Assert( isStrictlySorted(monos) );
  }

  static bool isSorted(const std::list<Monomial>& m){
    return __gnu_cxx::is_sorted(m.begin(), m.end());
  }

  static bool isStrictlySorted(const std::list<Monomial>& m){
    return isSorted(m) && std::adjacent_find(m.begin(),m.end()) == m.end();
  }

  static Node toNode(const std::list<Monomial>& m){
    Assert(m.size() >= 1);
    if(m.size() == 1){
      return (*m.begin()).getNode();
    }else{
      NodeBuilder<> nb(kind::PLUS);
      for(std::list<Monomial>::const_iterator i = m.begin(), end = m.end(); i != end; ++i){
        nb << (*i).getNode();
      }
      return Node(nb);
    }
  }

public:
  typedef std::list<Monomial>::const_iterator iterator;

  iterator begin() const{ return monos.begin(); }
  iterator end() const{ return monos.end(); }

  Polynomial(const Monomial& m):
    NodeWrapper(m.getNode()), monos()
  {
    monos.push_back(m);
  }
  Polynomial(const std::list<Monomial>& m):
    NodeWrapper(), monos(m)
  {
    if(monos.empty()){
      monos.push_back(Monomial::mkZero());
    }
    setNode(toNode(monos));

    Assert( !monos.empty());
    Assert( isStrictlySorted(monos) );
  }

  static Polynomial parsePolynomial(Node n){
    std::list<Monomial> monos;
    if(n.getKind() == kind::PLUS){
      for(Node::iterator i=n.begin(), end=n.end(); i != end; ++i){
        monos.push_back(Monomial::parseMonomial(*i));
      }
    }else{
      monos.push_back(Monomial::parseMonomial(n));
    }
    return Polynomial(n,monos);
  }

  /**
   * Given a sorted list of monomials,
   * returns a strictly sorted list of monomials that does not contain zero.
   * Both lists can be be empty.
   */
  static std::list<Monomial> combineLikeTerms(const std::list<Monomial> & monos){
    Assert(isSorted(monos));
    std::list<Monomial> outMonomials;

    Debug("blah") << "start combineLikeTerms" << std::endl;
    printList(monos);

    for(std::list<Monomial>::const_iterator rangeIter = monos.begin(), end = monos.end(); rangeIter != end; ){
      Rational constant = (*rangeIter).getConstant().getValue();
      VarList varList  = (*rangeIter).getVarList();
      ++rangeIter;
      while(rangeIter != end && varList == (*rangeIter).getVarList()){
        constant += (*rangeIter).getConstant().getValue();
        ++rangeIter;
      }
      if(constant != 0){
        outMonomials.push_back(Monomial::safeConstruct(constant,varList));
      }
    }
    Debug("blah") << "outmonomials" << std::endl;
    printList(outMonomials);
    Debug("blah") << "end combineLikeTerms" << std::endl;

    Assert(isStrictlySorted(outMonomials));
    return outMonomials;
  }

  static Polynomial mkZero(){
    return Polynomial(Monomial::mkZero());
  }
  static Polynomial mkOne(){
    return Polynomial(Monomial::mkOne());
  }
  bool isZero() const{
    return (monos.size() == 1) && (getHead().isZero());
  }

  bool isConstant() const{
    return (monos.size() == 1) && (getHead().isConstant());
  }

  bool containsConstant() const{
    return getHead().isConstant();
  }

  Monomial getHead() const{
    return *(monos.begin());
  }

  Polynomial getTail() const{
    Assert(monos.size() >= 1);

    std::list<Monomial>::const_iterator start = monos.begin();
    ++start;
    std::list<Monomial> subrange(start, monos.end());
    return Polynomial(subrange);
  }

  static void printList(const std::list<Monomial>& monos){
    for(std::list<Monomial>::const_iterator i = monos.begin(), end = monos.end(); i != end; ++i){
      Debug("blah") <<  ((*i).getNode()) << std::endl;
    }
  }

  void printList() const{
    Debug("blah") << "start list" << std::endl;
    printList(monos);
    Debug("blah") << "end list" << std::endl;
  }

  Polynomial operator+(const Polynomial& vl) const{
    this->printList();
    vl.printList();

    std::list<Monomial> sortedMonos;
    std::back_insert_iterator<std::list<Monomial> > bii(sortedMonos);
    std::merge(monos.begin(), monos.end(), vl.monos.begin(), vl.monos.end(), bii);

    std::list<Monomial> combinedMonos = combineLikeTerms(sortedMonos);

    Polynomial result(combinedMonos);
    result.printList();
    return result;
  }

  Polynomial operator*(const Monomial& mono) const{
    if(mono.isZero()){
      return Polynomial(mono); //Don't multiply by zero
    }else{
      std::list<Monomial> newMonos;
      for(std::list<Monomial>::const_iterator i = monos.begin(), end = monos.end(); i != end; ++i){
        newMonos.push_back(mono * (*i));
      }
      return Polynomial(newMonos);
    }
  }
  Polynomial operator*(const Polynomial& poly) const{

    Polynomial res = Polynomial::mkZero();
    for(std::list<Monomial>::const_iterator i = monos.begin(), end = monos.end(); i != end; ++i){
      Monomial curr = *i;
      Polynomial prod = poly * curr;
      Polynomial sum  = res + prod;
      res = sum;
    }
    return res;
  }

};

class Comparison : public NodeWrapper {
private:
  Kind oper;
  Polynomial left;
  Constant right;

  static Node toNode(Kind k, const Polynomial& l, const Constant& r){
    Assert(!l.isConstant());
    Assert(isRelationOperator(k));
    switch(k){
    case kind::GEQ:
    case kind::EQUAL:
    case kind::LEQ:
      return NodeManager::currentNM()->mkNode(k, l.getNode(),r.getNode());
    case kind::LT:
      return NodeManager::currentNM()->mkNode(kind::NOT, NodeManager::currentNM()->mkNode(kind::GEQ, l.getNode(), r.getNode()));
    case kind::GT:
      return NodeManager::currentNM()->mkNode(kind::NOT, NodeManager::currentNM()->mkNode(kind::LEQ, l.getNode(), r.getNode()));
    default:
      Unreachable();
    }
  }
  Comparison(TNode n, Kind k, const Polynomial& l, const Constant& r):
    NodeWrapper(n), oper(k), left(l), right(r)
  { }
public:
  Comparison(Kind k, const Polynomial& l, const Constant& r):
    NodeWrapper(Node::null()), oper(k), left(l), right(r)
  {
    Assert(isRelationOperator(oper));
    if(left.isConstant()){
      const Rational& rConst =  left.getNode().getConst<Rational>();
      const Rational& lConst = right.getNode().getConst<Rational>();
      bool res = evaluateConstantPredicate(oper, lConst, rConst);
      oper = kind::CONST_BOOLEAN;
      setNode(NodeManager::currentNM()->mkConst(res));
    }else{
      setNode(toNode(k, l, r));
    }
  }

  bool isBoolean() const{
    return (oper == kind::CONST_BOOLEAN);
  }

  bool isNormalForm() const{
    if(isBoolean()){
      return true;
    }else if(left.containsConstant()){
      return false;
    }else if(left.getHead().getConstant().isOne()){
      return true;
    }else{
      return false;
    }
  }

  const Polynomial& getLeft() const { return left; }
  const Constant& getRight() const { return right; }

  Comparison addConstant(const Constant& constant) const{
    Assert(!isBoolean());
    Monomial mono(constant);
    Polynomial constAsPoly( mono );
    Polynomial newLeft =  getLeft() + constAsPoly;
    Constant newRight = getRight() + constant;
    return Comparison(oper, newLeft, newRight);
  }
  Comparison multiplyConstant(const Constant& constant) const{
    Assert(!isBoolean());
    Kind newOper = (constant.getValue() < 0) ? negateRelationKind(oper) : oper;

    return Comparison(newOper, left*Monomial(constant), right*constant);
  }

  static Comparison parseNormalForm(TNode n){
    if(n.getKind() == kind::CONST_BOOLEAN){
      return Comparison(n, kind::CONST_BOOLEAN, Polynomial::mkZero(), Constant(0));
    }else{
      bool negated = n.getKind() == kind::NOT;
      Node relation = negated ? n[0] : n;
      Assert( !negated || relation.getKind() == kind::LEQ || relation.getKind() == kind::GEQ);

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
};



}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__NORMAL_FORM_H */

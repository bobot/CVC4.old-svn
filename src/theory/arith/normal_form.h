
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
 * Section 1: Languages
 * The normal form for arithmetic nodes is defined by the language
 * accepted by the following BNFs with some guard conditions.
 * (The guard conditions are in Section 3 for completeness.)
 *
 * variable := n
 *   where
 *     n.getMetaKind() == metakind::VARIABLE

 * constant := n
 *   where
 *     n.getKind() == kind::CONST_RATIONAL

 * var_list := variable | (* [variable])
 *   where
 *     len [variable] >= 2
 *     isSorted varOrder [variable]

 * monomial := constant | var_list | (* constant' var_list')
 *   where
 *     constant' \not\in {0,1}

 * polynomial := monomial | (+ [monomial])
 *   where
 *     len [monomial] >= 2
 *     isStrictlySorted monoOrder [monomial]

 * restricted_cmp := (|><| polynomial constant)
 *   where
 *     |><| is GEQ, EQ, or EQ
 *     not (exists constantMonomial (monomialList polynomial))
 *     monomialCoefficient (head (monomialList polynomial)) == 1

 * comparison := TRUE | FALSE | restricted_cmp | (not restricted_cmp)

 * Normal Form for terms := polynomial
 * Normal Form for atoms := comparison
 */

/**
 * Section 2: Helper Classes
 * The langauges accepted by each of these defintions
 * roughly corresponds to one of the following helper classes:
 *  Variable
 *  Constant
 *  VarList
 *  Monomial
 *  Polynomial
 *  Comparison
 *
 * Each of the classes obeys the following contracts/design decisions:
 * -Calling isMember(Node node) on a node returns true iff that node is a
 *  a member of the language. Note: isMember is O(n).
 * -Calling isNormalForm() on a helper class object returns true iff that
 *  helper class currently represents a normal form object.
 * -If isNormalForm() is false, then this object must have been made
 *  using a mk*() factory function.
 * -If isNormalForm() is true, calling getNode() on all of these classes
 *  returns a node that would be accepted by the corresponding language.
 *  And if isNormalForm() is false, returns Node::null().
 * -Each of the classes is immutable.
 * -Public facing constuctors have a 1-to-1 correspondence with one of
 *  production rules in the above grammar.
 * -Public facing constuctors are required to fail in debug mode when the
 *  guards of the production rule are not strictly met.
 *  For example: Monomial(Constant(1),VarList(Variable(x))) must fail.
 * -When a class has a Class parseClass(Node node) function,
 *  if isMember(node) is true, the function is required to return an instance
 *  of the helper class, instance, s.t. instance.getNode() == node.
 *  And if isMember(node) is false, this throws an assertion failure in debug
 *  mode and has undefined behaviour if not in debug mode.
 * -Only public facing constructors, parseClass(node), and mk*() functions are
 *  considered privledged functions for the helper class.
 * -Only privledged functions may use private constructors, and access
 *  private data members.
 * -All non-privledges functions are considered utility functions and
 *  must use a privledged function in order to create an instance of the class.
 */

/**
 * Section 3: Guard Conditions Misc.
 *
 *
 *  var_list_len vl =
 *    match vl with
 *       variable -> 1
 *     | (* [variable]) -> len [variable]
 *
 *  order res =
 *    match res with
 *       Empty -> (0,Node::null())
 *     | NonEmpty(vl) -> (var_list_len vl, vl)
 *
 *  var_listOrder a b = tuple_cmp (order a) (order b)
 *
 *  monomialVarList monomial =
 *    match monomial with
 *        constant -> Empty
 *      | var_list -> NonEmpty(var_list)
 *      | (* constant' var_list') -> NonEmpty(var_list')
 *
 *  monoOrder m0 m1 = var_listOrder (monomialVarList m0) (monomialVarList m1)
 *
 *  constantMonomial monomial =
 *    match monomial with
 *        constant -> true
 *      | var_list -> false
 *      | (* constant' var_list') -> false
 *
 *  monomialCoefficient monomial =
 *    match monomial with
 *        constant -> constant
 *      | var_list -> Constant(1)
 *      | (* constant' var_list') -> constant'
 *
 *  monomialList polynomial =
 *    match polynomial with
 *        monomial -> monomial::[]
 *      | (+ [monomial]) -> [monomial]
 */

/**
 * A NodeWrapper is a class that is a thinly veiled container of a Node object.
 */
class NodeWrapper {
private:
  Node node;
public:
  NodeWrapper(Node n) : node(n) {}
  const Node& getNode() const { return node; }
};

class Variable : public NodeWrapper {
public:
  Variable(Node n) : NodeWrapper(n) {
    Assert(isMember(getNode()));
  }

  static bool isMember(Node n) {
    return n.getMetaKind() == kind::metakind::VARIABLE;
  }

  bool isNormalForm() { return isMember(getNode()); }

  bool operator<(const Variable& v) const{ return getNode() < v.getNode();}
  bool operator==(const Variable& v) const{ return getNode() == v.getNode();}

};

class Constant : public NodeWrapper {
public:
  Constant(Node n) : NodeWrapper(n) {
    Assert(isMember(getNode()));
  }

  static bool isMember(Node n) {
    return n.getKind() == kind::CONST_RATIONAL;
  }

  bool isNormalForm() { return isMember(getNode()); }

  static Constant mkConstant(Node n) {
    return Constant(coerceToRationalNode(n));
  }

  static Constant mkConstant(const Rational& rat){
    return Constant(mkRationalNode(rat));
  }

  const Rational& getValue() const {
    return getNode().getConst<Rational>();
  }

  bool isZero() const{ return getValue() == 0; }
  bool isOne() const{ return getValue() == 1; }

  Constant operator*(const Constant& other) const{
    return mkConstant(getValue() * other.getValue());
  }
  Constant operator+(const Constant& other) const{
    return mkConstant(getValue() + other.getValue());
  }
  Constant operator-() const{
    return mkConstant(-getValue());
  }
};

/**
 * A VarList is a sorted list of variables representing a product.
 * If the VarList is empty, it represents an empty product or 1.
 * If the VarList has size 1, it represents a single variable.
 *
 * A non-sorted VarList can never be successfully made in debug mode.
 */
class VarList : public NodeWrapper {
private:
  std::list<Variable> list;

  static Node multList(const std::list<Variable>& list){
    Assert(list.size() >= 2);

    NodeBuilder<> nb(kind::MULT);
    for(std::list<Variable>::const_iterator i=list.begin(), end = list.end(); i!=end; ++i){
      nb << (*i).getNode();
    }
    return Node(nb);
  }

  static bool isSorted(const std::list<Variable>& l){
    return __gnu_cxx::is_sorted(l.begin(), l.end());
  }

  VarList() : NodeWrapper(Node::null()), list() {}

  VarList(Node n, const std::list<Variable>& l) : NodeWrapper(n), list(l) {
    Assert(isSorted(list));
  }

public:
  //typedef Node::const_iterator iterator;
  typedef std::list<Variable>::const_iterator iterator;
  VarList(Variable v) : NodeWrapper(v.getNode()), list(){
    list.push_back(v);
    Assert(isSorted(list));
  }
  VarList(const std::list<Variable>& l) : NodeWrapper(multList(l)), list(l) {
    Assert(list.size() >= 2);
    Assert(isSorted(list));
  }

  static bool isMember(Node n);

  bool isNormalForm() const{
    return !empty();
  }

  static VarList mkEmptyVarList(){
    return VarList();
  }


  /** There are no restrictions on the size of l */
  static VarList mkVarList(const std::list<Variable>& l){
    if(l.size() == 0){
      return mkEmptyVarList();
    }else if(l.size() == 1){
      return VarList((*l.begin()).getNode(), l);
    }else{
      return VarList(l);
    }
  }

  int size() const{ return list.size(); }
  bool empty() const { return list.empty(); }

  static VarList parseVarList(Node n);

  VarList operator*(const VarList& vl) const;

  int cmp(const VarList& vl) const;

  bool operator<(const VarList& vl) const{ return cmp(vl) < 0; }

  bool operator==(const VarList& vl) const{ return cmp(vl) == 0; }
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

    Assert(!c.isOne() || !multStructured(n));
  }

  static Node makeMultNode(const Constant& c, const VarList& vl){
    Assert(!c.isZero());
    Assert(!c.isOne());
    Assert(!vl.empty());
    return NodeManager::currentNM()->mkNode(kind::MULT, c.getNode(), vl.getNode());
  }

  static bool multStructured(Node n){
    return n.getKind() ==  kind::MULT &&
      n[0].getKind() == kind::CONST_RATIONAL &&
      n.getNumChildren() == 2;
  }

public:

  Monomial(const Constant& c):
    NodeWrapper(c.getNode()), constant(c), varList(VarList::mkEmptyVarList())
  { }

  Monomial(const VarList& vl):
    NodeWrapper(vl.getNode()), constant(Constant::mkConstant(1)), varList(vl)
  {
    Assert( !varList.empty() );
  }

  Monomial(const Constant& c, const VarList& vl):
    NodeWrapper(makeMultNode(c,vl)), constant(c), varList(vl)
  {
    Assert( !c.isZero() );
    Assert( !c.isOne() );
    Assert( !varList.empty() );

    Assert(multStructured(getNode()));
  }

  /** Makes a monomial with no restrictions on c and vl. */
  static Monomial mkMonomial(const Constant& c, const VarList& vl){
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
    }else if(multStructured(n)){
      return Monomial::mkMonomial(Constant(n[0]),VarList::parseVarList(n[1]));
    }else{
      return Monomial(VarList::parseVarList(n));
    }
  }

  static Monomial mkZero(){
    return Monomial(Constant::mkConstant(0));
  }
  static Monomial mkOne(){
    return Monomial(Constant::mkConstant(1));
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

  Monomial operator*(const Monomial& mono) const;


  int cmp(const Monomial& mono) const{
    return getVarList().cmp(mono.getVarList());
  }

  bool operator<(const Monomial& vl) const{
    return cmp(vl) < 0;
  }

  bool operator==(const Monomial& vl) const{
    return cmp(vl) == 0;
  }

  static bool isSorted(const std::list<Monomial>& m){
    return __gnu_cxx::is_sorted(m.begin(), m.end());
  }

  static bool isStrictlySorted(const std::list<Monomial>& m){
    return isSorted(m) && std::adjacent_find(m.begin(),m.end()) == m.end();
  }

  /**
   * Given a sorted list of monomials, this function transforms this
   * into a strictly sorted list of monomials that does not contain zero.
   */
  static void sumLikeTerms(std::list<Monomial> & monos);

  static void printList(const std::list<Monomial>& monos){
    for(std::list<Monomial>::const_iterator i = monos.begin(), end = monos.end(); i != end; ++i){
      Debug("blah") <<  ((*i).getNode()) << std::endl;
    }
  }
};

class Polynomial : public NodeWrapper {
private:
  std::list<Monomial> monos;

  Polynomial(Node n, const std::list<Monomial>& m):
    NodeWrapper(n), monos(m)
  {
    Assert( !monos.empty() );
    Assert( Monomial::isStrictlySorted(monos) );
  }

  static Node makePlusNode(const std::list<Monomial>& m){
    Assert(m.size() >= 2);
    NodeBuilder<> nb(kind::PLUS);
    for(iterator i = m.begin(), end = m.end(); i != end; ++i){
      nb << (*i).getNode();
    }
    return Node(nb);
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
    NodeWrapper(makePlusNode(m)), monos(m)
  {
    Assert( monos.size() >= 2);
    Assert( Monomial::isStrictlySorted(monos) );
  }

  static Polynomial mkPolynomial(const std::list<Monomial>& m){
    if(m.size() == 0){
      return Polynomial(Monomial::mkZero());
    }else if(m.size() == 1){
      return Polynomial((*m.begin()));
    }else{
      return Polynomial(m);
    }
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
    return mkPolynomial(subrange);
  }

  void printList() const{
    Debug("blah") << "start list" << std::endl;
    Monomial::printList(monos);
    Debug("blah") << "end list" << std::endl;
  }

  Polynomial operator+(const Polynomial& vl) const;

  Polynomial operator*(const Monomial& mono) const;

  Polynomial operator*(const Polynomial& poly) const;

};

class Comparison : public NodeWrapper {
private:
  Kind oper;
  Polynomial left;
  Constant right;

  static Node toNode(Kind k, const Polynomial& l, const Constant& r);

  Comparison(TNode n, Kind k, const Polynomial& l, const Constant& r):
    NodeWrapper(n), oper(k), left(l), right(r)
  { }
public:
  Comparison(bool val) :
    NodeWrapper(NodeManager::currentNM()->mkConst(val)),
    oper(kind::CONST_BOOLEAN),
    left(Polynomial::mkZero()),
    right(Constant::mkConstant(0))
  { }

  Comparison(Kind k, const Polynomial& l, const Constant& r):
    NodeWrapper(toNode(k, l, r)), oper(k), left(l), right(r)
  {
    Assert(isRelationOperator(oper));
    Assert(!left.containsConstant());
    Assert(left.getHead().getConstant().isOne());
  }

  static Comparison mkComparison(Kind k, const Polynomial& left, const Constant& right);

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

  Comparison addConstant(const Constant& constant) const;
  Comparison multiplyConstant(const Constant& constant) const;

  static Comparison parseNormalForm(TNode n);
};



}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__NORMAL_FORM_H */

/*********************                                                        */
/*! \file normal_form.h
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
 ** \brief Classes for handling Nodes in arithmetic in a more consistent form.
 **
 ** The normal form describes a series of inter related classes for handling Nodes
 ** in the arithmetic theory in a more consistent form. The rewriter should always
 ** return nodes in one of these forms.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__NORMAL_FORM_H
#define __CVC4__THEORY__ARITH__NORMAL_FORM_H

#include "expr/node.h"
#include "expr/node_self_iterator.h"
#include "util/rational.h"
#include "theory/theory.h"
#include "theory/arith/arith_utilities.h"

#include <list>
#include <algorithm>
#include <ext/algorithm>

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
 *
 * constant := q | z
 *   where
 *     q.getKind() == kind::CONST_RATIONAL and q.getDenominator() != 1
 *     z.getKind() == kind::CONST_INTEGER
 *
 * var_list := variable | (* [variable])
 *   where
 *     len [variable] >= 2
 *     isSorted varOrder [variable]
 *
 * monomial := constant | var_list | (* constant' var_list')
 *   where
 *     \f$ constant' \not\in {0,1} \f$
 *
 * polynomial := monomial' | (+ [monomial])
 *   where
 *     len [monomial] >= 2
 *     isStrictlySorted monoOrder [monomial]
 *     forall (\x -> x != 0) [monomial]
 *
 * restricted_cmp := (|><| qp c) | (|><| zp d)
 *   where
 *     |><| is GEQ, EQ, or EQ
 *     c and d are constants.
 *
 *     qp is not integral
 *     not (exists constantMonomial (monomialList qp))
 *     monomialCoefficient (head (monomialList qp)) == 1
 *
 *     zp is integral
 *     forall integerMonomial (monomialList zp)
 *     d is an integer.
 *     not (exists constantMonomial (monomialList zp))
 *     gcd (coefficientList zp) == 1
 *     monomialCoefficient (head (monomialList qp)) >= 0
 *
 * comparison := TRUE | FALSE | restricted_cmp | (not restricted_cmp)
 *
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
 *  considered privileged functions for the helper class.
 * -Only privileged functions may use private constructors, and access
 *  private data members.
 * -All non-privileged functions are considered utility functions and
 *  must use a privileged function in order to create an instance of the class.
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
};/* class NodeWrapper */


class Variable : public NodeWrapper {
public:
  Variable(Node n) : NodeWrapper(n) {
    Assert(isMember(getNode()));
  }

  // TODO: check if it's a theory leaf also
  static bool isMember(Node n) {
    if (n.getKind() == kind::CONST_INTEGER) return false;
    if (n.getKind() == kind::CONST_RATIONAL) return false;
    if (isRelationOperator(n.getKind())) return false;
    return Theory::isLeafOf(n, theory::THEORY_ARITH);
  }

  bool isNormalForm() { return isMember(getNode()); }

  bool isIntegral() const {
    return getNode().getType().isInteger();
  }

  bool operator<(const Variable& v) const { return getNode() < v.getNode();}
  bool operator==(const Variable& v) const { return getNode() == v.getNode();}

};/* class Variable */


class Constant : public NodeWrapper {
public:
  Constant(Node n) : NodeWrapper(n) {
    Assert(isMember(getNode()));
  }

  static bool isMember(Node n) {
    if(n.getKind() == kind::CONST_RATIONAL){
      return !n.getConst<Rational>().rationalIsIntegral();
    }else{
      return n.getKind() == kind::CONST_INTEGER;
    }
  }

  bool isNormalForm() { return isMember(getNode()); }

  static Constant mkConstant(Node n) {
    return Constant(coerceToRationalNode(n));
  }

  static Constant mkConstant(int z) {
    return Constant(mkIntegerNode(z));
  }

  static Constant mkConstant(const Integer& rat) {
    return Constant(mkIntegerNode(rat));
  }


  static Constant mkConstant(const Rational& rat) {
    if(rat.getDenominator() == 1){
      return Constant(mkIntegerNode(rat.getNumerator()));
    }else{
      return Constant(mkRationalNode(rat));
    }
  }

  bool isInteger() const{
    return getNode().getKind() == kind::CONST_INTEGER;
  }
  bool isRational() const{
    return getNode().getKind() == kind::CONST_RATIONAL;
  }

  const Integer& getIntegerValue() const {
    Assert(isInteger());
    return getNode().getConst<Integer>();
  }

  const Rational& getRationalValue() const {
    Assert(isRational());
    return getNode().getConst<Rational>();
  }

  Rational integerToRational() const {
    Assert(isInteger());
    return Rational(getIntegerValue());
  }

  Rational coerceToRational() const {
    return isInteger() ? integerToRational() : Rational(getRationalValue());
  }

  Integer coerceDenominator() const {
    return isInteger() ? Integer(1) : getRationalValue().getDenominator();
  }

  bool isZero() const { return isInteger() && (getIntegerValue() == 0); }
  bool isOne() const { return isInteger() && (getIntegerValue() == 1); }

  Constant operator*(const Constant& other) const {
    if(isInteger()){
      const Integer& tz = getIntegerValue();
      if(other.isInteger()){
        return mkConstant(tz * other.getIntegerValue());
      }else{
        return mkConstant(Rational(tz) * other.getRationalValue());
      }
    }else{
      const Rational& tq = getRationalValue();
      if(other.isInteger()){
        return mkConstant(tq * other.integerToRational());
      }else{
        return mkConstant(tq * other.getRationalValue());
      }
    }
  }

  Constant operator+(const Constant& other) const {
    if(isInteger()){
      const Integer& tz = getIntegerValue();
      if(other.isInteger()){
        return mkConstant(tz + other.getIntegerValue());
      }else{
        return mkConstant(Rational(tz) + other.getRationalValue());
      }
    }else{
      const Rational& tq = getRationalValue();
      if(other.isInteger()){
        return mkConstant(tq + other.integerToRational());
      }else{
        return mkConstant(tq + other.getRationalValue());
      }
    }
  }

  bool operator<(const Constant& other) const {
    if(isInteger()){
      const Integer& tz = getIntegerValue();
      if(other.isInteger()){
        return tz < other.getIntegerValue();
      }else{
        return Rational(tz) < other.getRationalValue();
      }
    }else{
      const Rational& tq = getRationalValue();
      if(other.isInteger()){
        return tq < other.integerToRational();
      }else{
        return tq < other.getRationalValue();
      }
    }
  }

  bool operator==(const Constant& other) const {
    //Rely on node uniqueness.
    return getNode() == other.getNode();
  }

  Constant operator-() const {
    if(isInteger()){
      return mkConstant(-getIntegerValue());
    }else{
      return mkConstant(-getRationalValue());
    }
  }

  bool isNegative() const {
    if(isInteger()){
      return getIntegerValue().sgn() < 0;
    }else{
      return getRationalValue().sgn() < 0;
    }
  }

  Constant inverse() const {
    if(isInteger()){
      return mkConstant(Rational(1,getIntegerValue()));
    }else{
      return mkConstant(getRationalValue().inverse());
    }
  }

  Constant abs() const {
    if(isNegative()){
      return -(*this);
    }else{
      return (*this);
    }
  }
};/* class Constant */


template <class GetNodeIterator>
inline Node makeNode(Kind k, GetNodeIterator start, GetNodeIterator end) {
  NodeBuilder<> nb(k);

  while(start != end) {
    nb << (*start).getNode();
    ++start;
  }

  return Node(nb);
}/* makeNode<GetNodeIterator>(Kind, iterator, iterator) */


template <class GetNodeIterator, class T>
static void copy_range(GetNodeIterator begin, GetNodeIterator end, std::vector<T>& result){
  while(begin != end){
    result.push_back(*begin);
    ++begin;
  }
}

template <class GetNodeIterator, class T>
static void merge_ranges(GetNodeIterator first1,
                  GetNodeIterator last1,
                  GetNodeIterator first2,
                  GetNodeIterator last2,
                  std::vector<T>& result) {

  while(first1 != last1 && first2 != last2){
    if( (*first1) < (*first2) ){
      result.push_back(*first1);
      ++ first1;
    }else{
      result.push_back(*first2);
      ++ first2;
    }
  }
  copy_range(first1, last1, result);
  copy_range(first2, last2, result);
}

/**
 * A VarList is a sorted list of variables representing a product.
 * If the VarList is empty, it represents an empty product or 1.
 * If the VarList has size 1, it represents a single variable.
 *
 * A non-sorted VarList can never be successfully made in debug mode.
 */
class VarList : public NodeWrapper {
private:

  static Node multList(const std::vector<Variable>& list) {
    Assert(list.size() >= 2);

    return makeNode(kind::MULT, list.begin(), list.end());
  }

  VarList() : NodeWrapper(Node::null()) {}

  VarList(Node n) : NodeWrapper(n) {
    Assert(isSorted(begin(), end()));
  }

  typedef expr::NodeSelfIterator internal_iterator;

  internal_iterator internalBegin() const {
    if(singleton()){
      return expr::NodeSelfIterator::self(getNode());
    }else{
      return getNode().begin();
    }
  }

  internal_iterator internalEnd() const {
    if(singleton()){
      return expr::NodeSelfIterator::selfEnd(getNode());
    }else{
      return getNode().end();
    }
  }

public:

  class iterator {
  private:
    internal_iterator d_iter;

  public:
    explicit iterator(internal_iterator i) : d_iter(i) {}

    inline Variable operator*() {
      return Variable(*d_iter);
    }

    bool operator==(const iterator& i) {
      return d_iter == i.d_iter;
    }

    bool operator!=(const iterator& i) {
      return d_iter != i.d_iter;
    }

    iterator operator++() {
      ++d_iter;
      return *this;
    }

    iterator operator++(int) {
      return iterator(d_iter++);
    }
  };

  iterator begin() const {
    return iterator(internalBegin());
  }

  iterator end() const {
    return iterator(internalEnd());
  }

  VarList(Variable v) : NodeWrapper(v.getNode()) {
    Assert(isSorted(begin(), end()));
  }

  VarList(const std::vector<Variable>& l) : NodeWrapper(multList(l)) {
    Assert(l.size() >= 2);
    Assert(isSorted(begin(), end()));
  }

  static bool isMember(Node n);

  bool isNormalForm() const {
    return !empty();
  }

  static VarList mkEmptyVarList() {
    return VarList();
  }


  /** There are no restrictions on the size of l */
  static VarList mkVarList(const std::vector<Variable>& l) {
    if(l.size() == 0) {
      return mkEmptyVarList();
    } else if(l.size() == 1) {
      return VarList((*l.begin()).getNode());
    } else {
      return VarList(l);
    }
  }

  bool empty() const { return getNode().isNull(); }
  bool singleton() const {
    return !empty() && getNode().getKind() != kind::MULT;
  }

  int size() const {
    if(singleton())
      return 1;
    else
      return getNode().getNumChildren();
  }

  Variable getHead() const {
    Assert(!empty());
    return *(begin());
  }

  static VarList parseVarList(Node n);

  VarList operator*(const VarList& vl) const;

  int cmp(const VarList& vl) const;

  bool operator<(const VarList& vl) const { return cmp(vl) < 0; }

  bool operator==(const VarList& vl) const { return cmp(vl) == 0; }

  bool isIntegral() const {
    for(iterator i = begin(), e=end(); i != e; ++i ){
      Variable var = *i;
      if(!var.isIntegral()){
        return false;
      }
    }
    return true;
  }

private:
  bool isSorted(iterator start, iterator end);

};/* class VarList */


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

  static Node makeMultNode(const Constant& c, const VarList& vl) {
    Assert(!c.isZero());
    Assert(!c.isOne());
    Assert(!vl.empty());
    return NodeManager::currentNM()->mkNode(kind::MULT, c.getNode(), vl.getNode());
  }

  static bool multStructured(Node n) {
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

  static bool isMember(TNode n);

  /** Makes a monomial with no restrictions on c and vl. */
  static Monomial mkMonomial(const Constant& c, const VarList& vl);


  static Monomial mkMonomial(const Variable& v){
    return Monomial(VarList(v));
  }

  static Monomial parseMonomial(Node n);

  static Monomial mkZero() {
    return Monomial(Constant::mkConstant(0));
  }
  static Monomial mkOne() {
    return Monomial(Constant::mkConstant(1));
  }
  const Constant& getConstant() const { return constant; }
  const VarList& getVarList() const { return varList; }

  bool isConstant() const {
    return varList.empty();
  }

  bool isZero() const {
    return constant.isZero();
  }

  bool isOne() const {
    return isConstant() && coefficientIsOne();
  }

  bool coefficientIsOne() const {
    return constant.isOne();
  }

  Monomial operator*(const Monomial& mono) const;


  int cmp(const Monomial& mono) const {
    return getVarList().cmp(mono.getVarList());
  }

  bool operator<(const Monomial& vl) const {
    return cmp(vl) < 0;
  }

  bool operator==(const Monomial& vl) const {
    return cmp(vl) == 0;
  }

  static bool isSorted(const std::vector<Monomial>& m) {
    return __gnu_cxx::is_sorted(m.begin(), m.end());
  }

  static bool isStrictlySorted(const std::vector<Monomial>& m) {
    return isSorted(m) && std::adjacent_find(m.begin(),m.end()) == m.end();
  }

  /**
   * A Monomial is an "integral" monomial if all of the variables in the
   * VarList are integral.
   */
  bool isIntegral() const {
    return getVarList().isIntegral();
  }

  /**
   * A Monomial is an "integer" monomial if both the constant is integer and
   * all of the variables in the VarList are integer.
   */
  bool isInteger() const {
    return getConstant().isInteger() && getVarList().isIntegral();
  }

  /**
   * Given a sorted list of monomials, this function transforms this
   * into a strictly sorted list of monomials that does not contain zero.
   */
  static std::vector<Monomial> sumLikeTerms(const std::vector<Monomial>& monos);

  void print() const;
  static void printList(const std::vector<Monomial>& list);

};/* class Monomial */


class Polynomial : public NodeWrapper {
private:
  bool d_singleton;

  Polynomial(TNode n) : NodeWrapper(n), d_singleton(Monomial::isMember(n)) {
    Assert(isMember(getNode()));
  }

  static Node makePlusNode(const std::vector<Monomial>& m) {
    Assert(m.size() >= 2);

    return makeNode(kind::PLUS, m.begin(), m.end());
  }

  typedef expr::NodeSelfIterator internal_iterator;

  internal_iterator internalBegin() const {
    if(singleton()){
      return expr::NodeSelfIterator::self(getNode());
    }else{
      return getNode().begin();
    }
  }

  internal_iterator internalEnd() const {
    if(singleton()){
      return expr::NodeSelfIterator::selfEnd(getNode());
    }else{
      return getNode().end();
    }
  }

  bool singleton() const { return d_singleton; }

public:
  static bool isMember(TNode n) {
    if(Monomial::isMember(n)){
      return true;
    }else if(n.getKind() == kind::PLUS){
      Assert(n.getNumChildren() >= 2);
      Node::iterator currIter = n.begin(), end = n.end();
      Node prev = *currIter;
      if(!Monomial::isMember(prev)){
        return false;
      }

      Monomial mprev = Monomial::parseMonomial(prev);
      ++currIter;
      for(; currIter != end; ++currIter){
        Node curr = *currIter;
        if(!Monomial::isMember(curr)){
          return false;
        }
        Monomial mcurr = Monomial::parseMonomial(curr);
        if(!(mprev < mcurr)){
          return false;
        }
        mprev = mcurr;
      }
      return true;
    } else {
      return false;
    }
  }

  class iterator {
  private:
    internal_iterator d_iter;

  public:
    explicit iterator(internal_iterator i) : d_iter(i) {}

    inline Monomial operator*() {
      return Monomial::parseMonomial(*d_iter);
    }

    bool operator==(const iterator& i) {
      return d_iter == i.d_iter;
    }

    bool operator!=(const iterator& i) {
      return d_iter != i.d_iter;
    }

    iterator operator++() {
      ++d_iter;
      return *this;
    }

    iterator operator++(int) {
      return iterator(d_iter++);
    }
  };

  iterator begin() const { return iterator(internalBegin()); }
  iterator end() const {  return iterator(internalEnd()); }

  Polynomial(const Monomial& m):
    NodeWrapper(m.getNode()), d_singleton(true)
  {}

  Polynomial(const std::vector<Monomial>& m):
    NodeWrapper(makePlusNode(m)), d_singleton(false)
  {
    Assert( m.size() >= 2);
    Assert( Monomial::isStrictlySorted(m) );
  }

  static Polynomial mkPolynomial(const Variable& v){
    return Monomial::mkMonomial(v);
  }

  static Polynomial mkPolynomial(const std::vector<Monomial>& m) {
    if(m.size() == 0) {
      return Polynomial(Monomial::mkZero());
    } else if(m.size() == 1) {
      return Polynomial((*m.begin()));
    } else {
      return Polynomial(m);
    }
  }

  static Polynomial parsePolynomial(Node n) {
    return Polynomial(n);
  }

  static Polynomial mkZero() {
    return Polynomial(Monomial::mkZero());
  }
  static Polynomial mkOne() {
    return Polynomial(Monomial::mkOne());
  }
  bool isZero() const {
    return singleton() && (getHead().isZero());
  }

  bool isConstant() const {
    return singleton() && (getHead().isConstant());
  }

  bool containsConstant() const {
    return getHead().isConstant();
  }

  Monomial getHead() const {
    return *(begin());
  }

  Polynomial getTail() const {
    Assert(! singleton());

    iterator tailStart = begin();
    ++tailStart;
    std::vector<Monomial> subrange;
    copy_range(tailStart, end(), subrange);
    return mkPolynomial(subrange);
  }

  void printList() const {
    if(Debug.isOn("normal-form")){
      Debug("normal-form") << "start list" << std::endl;
      for(iterator i = begin(), oend = end(); i != oend; ++i) {
        const Monomial& m =*i;
        m.print();
      }
      Debug("normal-form") << "end list" << std::endl;
    }
  }

  Polynomial operator+(const Polynomial& vl) const;

  Polynomial operator*(const Monomial& mono) const;

  Polynomial operator*(const Polynomial& poly) const;


  /** A Polynomial is an "integral" polynomial if all of the monomials are integral. */
  bool isIntegral() const {
    for(iterator i = begin(), e=end(); i!=e; ++i){
      if(!(*i).isIntegral()){
        return false;
      }
    }
    return true;
  }

  /** A Polynomial is an "integer" polynomial if all of the monomials are integer. */
  bool isInteger() const {
    for(iterator i = begin(), e=end(); i!=e; ++i){
      if(!(*i).isInteger()){
        return false;
      }
    }
    return true;
  }

  /**
   * Returns the Least Common Multiple of the denominators of the coefficients
   * of the monomials.
   */
  Integer denominatorLCM() const {
    Integer tmp(1);
    for(iterator i=begin(), e=end(); i!=e; ++i){
      const Constant& c = (*i).getConstant();
      if(c.isRational()){
        tmp = tmp.lcm(c.getRationalValue().getDenominator());
      }
    }
    return tmp;
  }

  /**
   * Returns the GCD of the coefficients of the monomials.
   * Requires this to be an isInteger() polynomial.
   */
  Integer gcd() const {
    #warning "If this is 0, is 0 the correct answer..."
    Assert(isInteger());
    iterator i=begin(), e=end();
    Assert(i!=e);

    Integer d = (*i).getConstant().getIntegerValue();
    ++i;
    for(; i!=e; ++i){
      const Integer& c = (*i).getConstant().getIntegerValue();
      d = d.gcd(c);
    }
    return d;
  }

  Monomial selectAbsMinimum() const {
    iterator iter = begin(), myend = end();
    Assert(iter != myend);

    Monomial min = *iter;
    ++iter;
    for(; iter != end(); ++iter){
      Monomial curr = *iter;
      if(min.getConstant().abs() < curr.getConstant().abs()){
        min = curr;
      }
    }
    return min;
  }

  Constant getCoefficient(const VarList& vl) const;

  static Node computeQR(const Polynomial& p, const Integer& z);

};/* class Polynomial */


class Comparison : public NodeWrapper {
private:
  Kind oper;
  Polynomial left;
  Constant right;

  static Node toNode(Kind k, const Polynomial& l, const Constant& r);

  Comparison(TNode n, Kind k, const Polynomial& l, const Constant& r):
    NodeWrapper(n), oper(k), left(l), right(r)
  { }

  /**
   * Possibly simplify a comparison with a pseudoboolean-typed LHS.  k
   * is one of LT, LEQ, EQUAL, GEQ, GT, and left must be PB-typed.  If
   * possible, "left k right" is fully evaluated, "true" is returned,
   * and the result of the evaluation is returned in "result".  If no
   * evaluation is possible, false is returned and "result" is
   * untouched.
   *
   * For example, pbComparison(kind::EQUAL, "x", 0.5, result) returns
   * true, and updates "result" to false, since pseudoboolean variable
   * "x" can never equal 0.5.  pbComparison(kind::GEQ, "x", 1, result)
   * returns false, since "x" can be >= 1, but could also be less.
   */
  //static bool pbComparison(Kind k, TNode left, const Rational& right, bool& result);

  static bool integerNormalFormCheck(const Polynomial& p, const Constant& c){
    Assert(!p.containsConstant());
    Assert(p.isIntegral());
    if(p.isInteger() && c.isInteger()){
      if(!p.getHead().getConstant().isNegative()){
        Integer gcd = p.gcd();
        return gcd == 1;
      }else{
        return false;
      }
    }else{
      return false;
    }
  }
  static bool rationalNormalFormCheck(const Polynomial& p){
    Assert(!p.containsConstant());
    Assert(!p.isIntegral());

    return p.getHead().getConstant().isOne();
  }

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
    Assert(isNormalForm());
    Assert(!left.containsConstant());
    Assert(left.getHead().getConstant().isOne());
  }

  static Comparison mkComparison(Kind k, const Polynomial& left, const Constant& right);

  bool isBoolean() const {
    return (oper == kind::CONST_BOOLEAN);
  }
  bool isEquality() const {
    return oper == kind::EQUAL;
  }

  bool isNormalForm() const {
    if(isBoolean()) {
      return true;
    } else if(left.containsConstant()) {
      return false;
    } else if(isIntegral()){
      return integerNormalFormCheck(left,right);
    } else{
      return rationalNormalFormCheck(left);
    }
  }

  const Polynomial& getLeft() const { return left; }
  const Constant& getRight() const { return right; }

  Comparison addConstant(const Constant& constant) const;
  Comparison multiplyConstant(const Constant& constant) const;

  static Comparison parseNormalForm(TNode n);

  bool isIntegral() const{
    return getLeft().isIntegral();
  }

  bool isInteger() const{
    return getRight().isInteger() && getLeft().isInteger();
  }

  inline static bool isNormalAtom(TNode n){
    Comparison parse = Comparison::parseNormalForm(n);
    return parse.isNormalForm();
  }

};/* class Comparison */

class SumPair : public NodeWrapper {
private:
  static Node toNode(const Polynomial& p, const Constant& c){
    return NodeManager::currentNM()->mkNode(kind::PLUS, p.getNode(), c.getNode());
  }

  SumPair(TNode n) :
    NodeWrapper(n)
  {
    Assert(isNormalForm());
  }

public:

  // SumPair() :
  //   NodeWrapper(toNode(Polynomial::mkZero(), Constant::mkZero()))
  // {
  //   Assert(isNormalForm());
  // }

  SumPair(const Polynomial& p):
          NodeWrapper(toNode(p, Constant::mkConstant(0)))
  {
    Assert(isNormalForm());
  }

  SumPair(const Polynomial& p, const Constant& c):
    NodeWrapper(toNode(p, c))
  {
    Assert(isNormalForm());
  }

  static bool isMember(TNode n) {
    if(n.getKind() == kind::PLUS && n.getNumChildren() == 2){
      return Constant::isMember(n[1]) && Polynomial::isMember(n[0]);
    }else{
      return 0;
    }
  }

  bool isNormalForm() const {
    return isMember(getNode());
  }

  Polynomial getPolynomial() const {
    return Polynomial::parsePolynomial(getNode()[0]);
  }

  Constant getConstant() const {
    return Constant((getNode())[1]);
  }

  SumPair operator+(const SumPair& other) const {
    return SumPair(getPolynomial() + other.getPolynomial(),
                   getConstant() + other.getConstant());
  }

  SumPair operator*(const Constant& c) const {
    return SumPair(getPolynomial() * c, getConstant() * c);
  }

  SumPair operator-(const SumPair& other) const {
    return (*this) + (other * Constant::mkConstant(-1));
  }

  Comparison addConstant(const Constant& constant) const;
  Comparison multiplyConstant(const Constant& constant) const;

  static SumPair mkSumPair(const Variable& var){
    return SumPair(Polynomial::mkPolynomial(var));
  }

  static SumPair parseSumPair(TNode n){
    return SumPair(n);
  }

  bool isIntegral() const{
    return getPolynomial().isIntegral();
  }

  bool isInteger() const{
    return getConstant().isInteger() && getPolynomial().isInteger();
  }

  bool isZero() const {
    return getConstant().isZero() && getPolynomial().isZero();
  }

  Integer gcd() const {
    Assert(isInteger());
    return (getPolynomial().gcd()).gcd(getConstant().getIntegerValue());
  }

  static SumPair mkZero() {
    return SumPair(Polynomial::mkZero(), Constant::mkConstant(0));
  }

  static Node computeQR(const SumPair& sp, const Integer& div){
    Assert(sp.isInteger());
    Assert(div >= 0);

    const Integer& constant = sp.getConstant().getIntegerValue();

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
};/* class SumPair */


inline SumPair comparisonToSumPair(const Comparison& cmp){
  return SumPair(cmp.getLeft(), - cmp.getRight());
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__NORMAL_FORM_H */

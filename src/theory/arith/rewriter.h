
#include <vector>
#include <set>
#include <stack>

#include "theory/arith/arith_utilities.h"

#ifndef __CVC4__THEORY__ARITH__REWRITER_H
#define __CVC4__THEORY__ARITH__REWRITER_H

namespace CVC4 {
namespace theory {
namespace arith {


/***********************************************/
/***************** Normal Form *****************/
/***********************************************/
/***********************************************/

/**
 * Normal form for predicates:
 *    TRUE
 *    FALSE
 *    v |><| b
 *    p |><| b
 *    (+ p_1 .. p_N)  |><| b
 *  where
 *   1) b is of type CONST_RATIONAL
 *   2) |><| is of kind <, <=, =, >= or >
 *   3) p, p_i is in PNF,
 *   4) p.M >= 2
 *   5) p_i's are in strictly ascending <p,
 *   6) N >= 2,
 *   7) the kind of (+ p_1 .. p_N) is an N arity PLUS,
 *   8) p.d, p_1.d are 1,
 *   9) v has metakind variable, and
 *
 * PNF(t):
 *    (* d v_1 v_2 ... v_M)
 *  where
 *   1) d is of type CONST_RATIONAL,
 *   2) d != 0,
 *   4) M>=1,
 *   5) v_i are of metakind VARIABLE,
 *   6) v_i are in increasing (not strict) nodeOrder, and
 *   7) the kind of t is an M+1 arity MULT.
 *
 * <p is defined over PNF as follows (skipping some symmetry):
 *   cmp( (* d v_1 v_2 ... v_M), (* d' v'_1 v'_2 ... v'_M'):
 *      if(M == M'):
 *      then tupleCompare(v_i, v'_i)
 *      else M -M'
 *
 * Rewrite Normal Form for Terms:
 *    b
 *    v
 *    (+ c p_1 p_2 ... p_N)  |  not(N=1 and c=0 and p_1.d=1)
 *  where
 *   1) b,c is of type CONST_RATIONAL,
 *   3) p_i is in PNF,
 *   4) N >= 1
 *   5) the kind of (+ c p_1 p_2 ... p_N) is an N+1 arity PLUS,
 *   6) and p_i's are in strictly <p.
 *
 */

class ArithRewriter{
private:
  Rational d_ZERO;
  Rational d_ONE;
  Rational d_NEGATIVE_ONE;

  Node d_ZERO_NODE;
  Node d_ONE_NODE;
  Node d_NEGATIVE_ONE_NODE;

  ArithRewriter(NodeManager* nm) : 
    d_ZERO(0,1),
    d_ONE(1,1),
    d_NEGATIVE_ONE(-1,1),
    d_ZERO_NODE(nm->mkConst(d_ZERO)),
    d_ONE_NODE(nm->mkConst(d_ONE)),
    d_NEGATIVE_ONE_NODE(nm->mkConst(d_NEGATIVE_ONE))
  {}

  Node rewriteAtom(TNode atom);
  Node rewriteTerm(TNode t);
  Node rewriteMult(TNode t);
  Node rewritePlus(TNode t);
  Node makeSubtractionNode(const TNode l, const TNode r);

public:
  Node rewrite(TNode t);

};

/** is k \in {LT, LEQ, EQ, GEQ, GT} */
bool isRelationOperator(Kind k);
bool evaluateConstantPredicate(Kind k, const Rational& l, const Rational& r);
Node mkRationalNode(Rational& q);
Node mkBoolNode(bool b);
Kind multKind(Kind k, int sgn);

Node coerceToRationalNode(TNode constant);

Node multPnfByNonZero(TNode pnf, Rational& q);

Node makeSubtractionNode(const TNode l, const TNode r);


Node ArithRewriter::rewrite(TNode t){
  Unimplemented();
  return t;
}


/**
 * Performs a quick check to see if it is easy to rewrite to
 * this normal form
 *        v |><| b
 * Also writes relations with constants on both sides to TRUE or FALSE.
 * If it can, it returns true and sets res to this value.
 *
 * This is for optimizing rewriteAtom() to avoid the more compuationally expensive
 * general rewriting procedure.
 *
 * If simplification is not done, is returning Node::null()
 */
Node almostVarOrConstEqn(TNode atom, Kind k, TNode left, TNode right){
  Assert(atom.getKind() == k);
  Assert(isRelationOperator(k));
  Assert(atom[0] == left);
  Assert(atom[1] == right);
  bool leftIsConst  =  left.getMetaKind() == kind::metakind::CONSTANT;
  bool rightIsConst = right.getMetaKind() == kind::metakind::CONSTANT;

  bool leftIsVar = left.getMetaKind() == kind::metakind::VARIABLE;
  bool rightIsVar = right.getMetaKind() == kind::metakind::VARIABLE;

  if(leftIsConst && rightIsConst){
    Rational lc = coerceToRational(left);
    Rational rc = coerceToRational(right);
    bool res = evaluateConstantPredicate(k,lc, rc);
    return mkBoolNode(res);
  }else if(leftIsVar && rightIsConst){
    return atom;
  }else if(leftIsConst && rightIsVar){
    return NodeManager::currentNM()->mkNode(multKind(k,-1),right,left);
  }

  return Node::null();
}

Node ArithRewriter::rewriteAtom(TNode atom){

  Kind k = atom.getKind();
  Assert(isRelationOperator(k));

  // left |><| right
  TNode left = atom[0];
  TNode right = atom[1];

  Node nf = almostVarOrConstEqn(atom, k,left,right);
  if(nf != Node::null() ){
    return nf;
  }

  //Transform this to: (left- right) |><| 0
  Node diff = makeSubtractionNode(left, right);

  Node rewritten = rewrite(diff);
  // rewritten =_{Reals} left - right => rewritten |><| 0

  if(rewritten.getMetaKind() == kind::metakind::CONSTANT){
    // Case 1 rewritten : c
    Rational c = rewritten.getConst<Rational>();
    bool res = evaluateConstantPredicate(k, c, d_ZERO);
    nf = mkBoolNode(res);
  }else if(rewritten.getMetaKind() == kind::metakind::VARIABLE){
    // Case 2 rewritten : v
    nf = NodeManager::currentNM()->mkNode(k, rewritten, d_ZERO_NODE);
  }else{
    // Case 3 rewritten : (+ c p_1 p_2 ... p_N)  |  not(N=1 and c=0 and p_1.d=1)
    Rational c = rewritten[0].getConst<Rational>();
    c = -c;
    TNode p_1 = rewritten[1];
    Rational d = p_1[0].getConst<Rational>();
    d = d.inverse();
    c = c * d;
    Node newRight = mkRationalNode(c);
    Kind newKind = multKind(k, d.sgn());
    int N = rewritten.getNumChildren() - 1;

    if(N==1){
      int M = p_1.getNumChildren()-1;
      if(M == 1){ // v |><| b
        TNode v = p_1[1];
        nf = NodeManager::currentNM()->mkNode(newKind, v, newRight);
      }else{ // p |><| b
        Node newLeft = multPnfByNonZero(p_1, d);
        nf = NodeManager::currentNM()->mkNode(newKind, newLeft, newRight);
      }
    }else{ //(+ p_1 .. p_N)  |><| b
      NodeBuilder<> plus;
      for(int i=1; i<=N; ++i){
        TNode p_i = rewritten[i];
        plus << multPnfByNonZero(p_i, d);
      }
      Node newLeft = plus;
      nf = NodeManager::currentNM()->mkNode(newKind, newLeft, newRight);
    }
  }

  return nf;
}


/* cmp( (* d v_1 v_2 ... v_M), (* d' v'_1 v'_2 ... v'_M'):
 *      if(M == M'):
 *      then tupleCompare(v_i, v'_i)
 *      else M -M'
 */
struct pnfLessThan {
  bool operator()(Node p0, Node p1) {
    int p0_M = p0.getNumChildren() -1;
    int p1_M = p1.getNumChildren() -1;
    if(p0_M == p1_M){
      for(int i=1; i<= p0_M; ++i){
        if(p0[i] != p1[i]){
          return p0[i] < p1[i];
        }
      }
      return false; //p0 == p1 in this order
    }else{
      return p0_M < p1_M;
    }
  }
};

Node addPnfs(TNode p0, TNode p1){
  //TODO asserts
  Rational c0 = p0[0].getConst<Rational>();
  Rational c1 = p1[0].getConst<Rational>();

  int M = p0.getNumChildren();

  Rational addedC = c0 + c1;
  Node newC = mkRationalNode(addedC);
  NodeBuilder<> nb(kind::PLUS);
  nb << newC;
  for(int i=1; i <= M; ++i){
    nb << p0[i];
  }
  Node newPnf = nb;
  return newPnf;
}

void sortAndCombineCoefficients(std::vector<Node>& pnfs){
  using namespace std;

  typedef set<Node, pnfLessThan> PnfSet;
  PnfSet combined_pnf_set;

  for(vector<Node>::iterator i=pnfs.begin(); i != pnfs.end(); ++i){
    Node pnf = *i;
    PnfSet::iterator pos = combined_pnf_set.find(pnf);

    if(pos == combined_pnf_set.end()){
      combined_pnf_set.insert(pnf);
    }else{
      Node current = *pos;
      Node sum = addPnfs(pnf, current);
      combined_pnf_set.erase(pos);
      combined_pnf_set.insert(sum);
    }
  }
  pnfs.clear();
  for(PnfSet::iterator i=combined_pnf_set.begin(); i != combined_pnf_set.end(); ++i){
    Node pnf = *i;
    pnfs.push_back(pnf);
  }
}

Node ArithRewriter::rewritePlus(TNode t){
  using namespace std;

  Rational accumulator;
  vector<Node> pnfs;

  for(TNode::iterator i = t.begin(); i!= t.end(); ++i){
    TNode child = *i;
    Node rewrittenChild = rewrite(child);

    if(rewrittenChild.getMetaKind() == kind::metakind::CONSTANT){//c
      Rational c = rewrittenChild.getConst<Rational>();
      accumulator = accumulator + c;
    }else if(rewrittenChild.getMetaKind() == kind::metakind::VARIABLE){ //v
      Node pnf = NodeManager::currentNM()->mkNode(kind::MULT,d_ONE_NODE,rewrittenChild);
      pnfs.push_back(pnf);
    }else{ //(+ c p_1 p_2 ... p_N)
      Rational c = rewrittenChild[0].getConst<Rational>();
      accumulator = accumulator + c;
      int N = rewrittenChild.getNumChildren() - 1;
      for(int i=1; i<=N; ++i){
        TNode pnf = rewrittenChild[i];
        pnfs.push_back(pnf);
      }
    }
  }
  sortAndCombineCoefficients(pnfs);
  if(pnfs.size() == 0){
    return mkRationalNode(accumulator);
  }

  // pnfs.size() >= 1

  //Enforce not(N=1 and c=0 and p_1.d=1)
  if(pnfs.size() == 1){
    Node p_1 = *(pnfs.begin());
    if(p_1[0].getConst<Rational>() == d_ONE){
      if(accumulator == 0){  // 0 + (* 1 var) |-> var
        Node var = p_1[1];
        return var;
      }
    }
  }

  //We must be in this case
  //(+ c p_1 p_2 ... p_N)  |  not(N=1 and c=0 and p_1.d=1)

  NodeBuilder<> nb(kind::PLUS);
  nb << mkRationalNode(accumulator);
  for(vector<Node>::iterator i = pnfs.begin(); i != pnfs.end(); ++i){
    nb << *i;
  }

  Node normalForm = nb;
  return normalForm;
}

//Does not enforce
//5) v_i are of metakind VARIABLE,
//6) v_i are in increasing (not strict) nodeOrder,
Node toPnf(Rational& c, std::set<Node>& variables){
  NodeBuilder<> nb(kind::MULT);
  nb << mkRationalNode(c);
  for(std::set<Node>::iterator i = variables.begin(); i != variables.end(); ++i){
    nb << *i;
  }
  Node pnf = nb;
  return pnf;
}

Node distribute(TNode n, TNode sum){
  NodeBuilder<> nb(kind::PLUS);
  for(TNode::iterator i=sum.begin(); i!=sum.end(); ++i){
    Node prod = NodeManager::currentNM()->mkNode(kind::MULT, n, *i);
    nb << prod;
  }
  return nb;
}
Node distributeSum(TNode sum, TNode distribSum){
  NodeBuilder<> nb(kind::PLUS);
  for(TNode::iterator i=sum.begin(); i!=sum.end(); ++i){
    Node dist = distribute(*i, distribSum);
    for(Node::iterator j=dist.begin(); j!=dist.end(); ++j){
      nb << *j;
    }
  }
  return nb;
}

Node ArithRewriter::rewriteMult(TNode t){

  using namespace std;

  Rational accumulator(1,1);
  set<Node> variables;
  vector<Node> sums;
  stack<pair<TNode, TNode::iterator> > mult_iterators;

  mult_iterators.push(make_pair(t, t.begin()));
  while(!mult_iterators.empty()){
    pair<TNode, TNode::iterator> p = mult_iterators.top();
    mult_iterators.pop();

    TNode mult = p.first;
    TNode::iterator i = p.second;

    for(; i!= mult.end(); ++i){
      TNode child = *i;
      if(child.getKind() == kind::MULT){ //TODO add not rewritten already checks
        ++i;
        mult_iterators.push(make_pair(mult,i));
        mult_iterators.push(make_pair(child,child.begin()));
        break;
      }
      Node rewrittenChild = rewrite(child);

      if(rewrittenChild.getMetaKind() == kind::metakind::CONSTANT){//c
        Rational c = rewrittenChild.getConst<Rational>();
        accumulator = accumulator * c;
        if(accumulator == 0){
          return d_ZERO_NODE;
        }
      }else if(rewrittenChild.getMetaKind() == kind::metakind::VARIABLE){ //v
        variables.insert(rewrittenChild);
      }else{ //(+ c p_1 p_2 ... p_N)
        sums.push_back(rewrittenChild);
      }
    }
  }
  // accumulator * (\prod var_i) *(\prod sum_j)

  if(sums.size() == 0){ //accumulator * (\prod var_i)
    if(variables.size() == 0){ //accumulator
      return mkRationalNode(accumulator);
    }else if(variables.size() == 1 && accumulator == d_ONE){ // var_1
      Node var = *(variables.begin());
      return var;
    }else{
      //We need to return (+ c p_1 p_2 ... p_N)
      //To accomplish this:
      //  let pnf = pnf(accumulator * (\prod var_i)) in (+ 0 pnf)
      Node pnf = toPnf(accumulator, variables);
      Node normalForm = NodeManager::currentNM()->mkNode(kind::PLUS, d_ZERO_NODE, pnf);
      return normalForm;
    }
  }else{
    vector<Node>::iterator sum_iter = sums.begin();
    // \sum t
    // t \in Q \cup A
    // where A = lfp {\prod s | s \in Q \cup Variables \cup A}
    Node distributed = *sum_iter;
    ++sum_iter;
    while(sum_iter != sums.end()){
      Node curr = *sum_iter;
      distributed = distributeSum(curr, distributed);
      ++sum_iter;
    }
    if(variables.size() >= 1){
      Node pnf = toPnf(accumulator, variables);
      distributed = distribute(pnf, distributed);
    }else{
      Node constant = mkRationalNode(accumulator);
      distributed = distribute(constant, distributed);
    }

    Node nf_distributed = rewrite(distributed);
    return nf_distributed;
  }
}

Node ArithRewriter::rewriteTerm(TNode t){
  if(t.getMetaKind() == kind::metakind::CONSTANT){
    return coerceToRationalNode(t);
  }else if(t.getMetaKind() == kind::metakind::VARIABLE){
    return t;
  }else if(t.getKind() == kind::MULT){
    return rewriteMult(t);
  }else if(t.getKind() == kind::PLUS){
    return rewritePlus(t);
  }else{
    Unreachable();
    return Node::null();
  }
}


/**
 * Given a node in PNF pnf = (* d p_1 p_2 .. p_M) and a rational q != 0
 * constuct a node equal to q * pnf that is in pnf.
 *
 * The claim is that this is always okay:
 * If d' = q*d, p' = (* d' p_1 p_2 .. p_M) =_{Reals} q * pnf.
 */
Node multPnfByNonZero(TNode pnf, Rational& q){
  Assert(q != 0);
  //TODO Assert(isPNF(pnf) );

  int M = pnf.getNumChildren()-1;
  Rational d = pnf[0].getConst<Rational>();
  Rational new_d = d*q;


  NodeBuilder<> mult;
  mult << mkRationalNode(new_d);
  for(int i=1; i<=M; ++i){
    mult << pnf[i];
  }

  Node result = mult;
  return result;
}



Node ArithRewriter::makeSubtractionNode(const TNode l, const TNode r){
  Node negR = NodeManager::currentNM()->mkNode(kind::MULT, d_NEGATIVE_ONE_NODE, r);
  Node diff = NodeManager::currentNM()->mkNode(kind::PLUS,l,negR);

  return diff;
}


Kind multKind(Kind k, int sgn){
  using namespace kind;

  if(sgn < 0){

    switch(k){
    case LT: return GT;
    case LEQ: return GEQ;
    case EQUAL: return EQUAL;
    case GEQ: return LEQ;
    case GT: return LT;
    default:
      Unhandled();
    }
    return NULL_EXPR;
  }else{
    return k;
  }
}






}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__REWRITER_H */

/*********************                                                        */
/*! \file arith_rewriter.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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


#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_utilities.h"

#include <vector>
#include <set>
#include <stack>


using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;





Kind multKind(Kind k, int sgn);

/**
 * Performs a quick check to see if it is easy to rewrite to
 * this normal form
 *        v |><| b
 * Also writes relations with constants on both sides to TRUE or FALSE.
 * If it can, it returns true and sets res to this value.
 *
 * This is for optimizing rewriteAtom() to avoid the more compuationally
 * expensive general rewriting procedure.
 *
 * If simplification is not done, it returns Node::null()
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
    if(right.getKind() == kind::CONST_RATIONAL){
      return atom;
    }else{
      return NodeManager::currentNM()->mkNode(k,left,coerceToRationalNode(right));
    }
  }else if(leftIsConst && rightIsVar){
    if(left.getKind() == kind::CONST_RATIONAL){
      return NodeManager::currentNM()->mkNode(multKind(k,-1),right,left);
    }else{
      Node q_left = coerceToRationalNode(left);
      return NodeManager::currentNM()->mkNode(multKind(k,-1),right,q_left);
    }
  }

  return Node::null();
}

Node ArithRewriter::rewriteAtomCore(TNode atom){

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
    bool res = evaluateConstantPredicate(k, c, d_constants->d_ZERO);
    nf = mkBoolNode(res);
  }else if(rewritten.getMetaKind() == kind::metakind::VARIABLE){
    // Case 2 rewritten : v
    nf = NodeManager::currentNM()->mkNode(k, rewritten, d_constants->d_ZERO_NODE);
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
      NodeBuilder<> plus(kind::PLUS);
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

Node ArithRewriter::rewriteAtom(TNode atom){
  Node rewritten = rewriteAtomCore(atom);
  if(rewritten.getKind() == kind::LT){
    Node geq = NodeManager::currentNM()->mkNode(kind::GEQ, rewritten[0], rewritten[1]);
    return NodeManager::currentNM()->mkNode(kind::NOT, geq);
  }else if(rewritten.getKind() == kind::GT){
    Node leq = NodeManager::currentNM()->mkNode(kind::LEQ, rewritten[0], rewritten[1]);
    return NodeManager::currentNM()->mkNode(kind::NOT, leq);
  }else if(rewritten.getKind() == kind::EQUAL){
    Node leq = NodeManager::currentNM()->mkNode(kind::LEQ, rewritten[0], rewritten[1]);
    Node geq = NodeManager::currentNM()->mkNode(kind::GEQ, rewritten[0], rewritten[1]);

    return NodeManager::currentNM()->mkNode(kind::AND, leq, geq);
  }else{
    return rewritten;
  }
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

//Two pnfs are equal up to their coefficients
bool pnfsMatch(TNode p0, TNode p1){

  unsigned M = p0.getNumChildren()-1;
  if (M+1 != p1.getNumChildren()){
    return false;
  }

  for(unsigned i=1; i <= M; ++i){
    if(p0[i] != p1[i])
      return false;
  }
  return true;
}

Node addMatchingPnfs(TNode p0, TNode p1){
  Assert(pnfsMatch(p0,p1));

  unsigned M = p0.getNumChildren()-1;

  Rational c0 = p0[0].getConst<Rational>();
  Rational c1 = p1[0].getConst<Rational>();

  Rational addedC = c0 + c1;
  Node newC = mkRationalNode(addedC);
  NodeBuilder<> nb(kind::MULT);
  nb << newC;
  for(unsigned i=1; i <= M; ++i){
    nb << p0[i];
  }
  Node newPnf = nb;
  return newPnf;
}

void ArithRewriter::sortAndCombineCoefficients(std::vector<Node>& pnfs){
  using namespace std;

  /* combined contains exactly 1 representative per for each pnf.
   * This is maintained by combining the coefficients for pnfs.
   * that is equal according to pnfLessThan.
   */
  typedef set<Node, pnfLessThan> PnfSet;
  PnfSet combined;

  for(vector<Node>::iterator i=pnfs.begin(); i != pnfs.end(); ++i){
    Node pnf = *i;
    PnfSet::iterator pos = combined.find(pnf);

    if(pos == combined.end()){
      combined.insert(pnf);
    }else{
      Node current = *pos;
      Node sum = addMatchingPnfs(pnf, current);
      combined.erase(pos);
      combined.insert(sum);
    }
  }
  pnfs.clear();
  for(PnfSet::iterator i=combined.begin(); i != combined.end(); ++i){
    Node pnf = *i;
    if(pnf[0].getConst<Rational>() != d_constants->d_ZERO){
      //after combination the coefficient may be zero
      pnfs.push_back(pnf);
    }
  }
}

Node ArithRewriter::var2pnf(TNode variable){
  return NodeManager::currentNM()->mkNode(kind::MULT,d_constants->d_ONE_NODE,variable);
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
      Node pnf = var2pnf(rewrittenChild);
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
    if(p_1[0].getConst<Rational>() == d_constants->d_ONE){
      if(accumulator == d_constants->d_ZERO){  // 0 + (* 1 var) |-> var
        Node var = p_1[1];
        return var;
      }
    }
  }

  //We must be in this case
  //(+ c p_1 p_2 ... p_N)  |  not(N=1 and c=0 and p_1.d=1)

  NodeBuilder<> nb(kind::PLUS);
  nb << mkRationalNode(accumulator);
  Debug("arithrewrite") << mkRationalNode(accumulator) << std::endl;
  for(vector<Node>::iterator i = pnfs.begin(); i != pnfs.end(); ++i){
    nb << *i;
    Debug("arithrewrite") << (*i) << std::endl;

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

  //These stacks need to be kept in lock step
  stack<TNode> mult_iterators_nodes;
  stack<TNode::const_iterator> mult_iterators_iters;

  mult_iterators_nodes.push(t);
  mult_iterators_iters.push(t.begin());

  while(!mult_iterators_nodes.empty()){
    TNode mult = mult_iterators_nodes.top();
    TNode::const_iterator i = mult_iterators_iters.top();

    mult_iterators_nodes.pop();
    mult_iterators_iters.pop();

    for(; i != mult.end(); ++i){
      TNode child = *i;
      if(child.getKind() == kind::MULT){ //TODO add not rewritten already checks
        ++i;
        mult_iterators_nodes.push(mult);
        mult_iterators_iters.push(i);

        mult_iterators_nodes.push(child);
        mult_iterators_iters.push(child.begin());
        break;
      }
      Node rewrittenChild = rewrite(child);

      if(rewrittenChild.getMetaKind() == kind::metakind::CONSTANT){//c
        Rational c = rewrittenChild.getConst<Rational>();
        accumulator = accumulator * c;
        if(accumulator == d_constants->d_ZERO){
          return d_constants->d_ZERO_NODE;
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
    }else if(variables.size() == 1 && accumulator == d_constants->d_ONE){ // var_1
      Node var = *(variables.begin());
      return var;
    }else{
      //We need to return (+ c p_1 p_2 ... p_N)
      //To accomplish this:
      //  let pnf = pnf(accumulator * (\prod var_i)) in (+ 0 pnf)
      Node pnf = toPnf(accumulator, variables);
      Node normalForm = NodeManager::currentNM()->mkNode(kind::PLUS, d_constants->d_ZERO_NODE, pnf);
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

Node ArithRewriter::rewriteDivByConstant(TNode t){
  Assert(t.getKind()== kind::DIVISION);

  Node left = t[0];
  Node reRight = rewrite(t[1]);
  Assert(reRight.getKind()== kind::CONST_RATIONAL);


  Rational den = reRight.getConst<Rational>();

  Assert(den != d_constants->d_ZERO);

  Rational div = den.inverse();

  Node result = mkRationalNode(div);

  Node mult = NodeManager::currentNM()->mkNode(kind::MULT,left,result);

  Node reMult = rewrite(mult);

  return reMult;
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
  }else if(t.getKind() == kind::DIVISION){
    return rewriteDivByConstant(t);
  }else if(t.getKind() == kind::MINUS){
    Node sub = makeSubtractionNode(t[0],t[1]);
    return rewrite(sub);
  }else if(t.getKind() == kind::UMINUS){
    Node sub = makeUnaryMinusNode(t[0]);
    return rewrite(sub);
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
Node ArithRewriter::multPnfByNonZero(TNode pnf, Rational& q){
  Assert(q != d_constants->d_ZERO);
  //TODO Assert(isPNF(pnf) );

  int M = pnf.getNumChildren()-1;
  Rational d = pnf[0].getConst<Rational>();
  Rational new_d = d*q;


  NodeBuilder<> mult(kind::MULT);
  mult << mkRationalNode(new_d);
  for(int i=1; i<=M; ++i){
    mult << pnf[i];
  }

  Node result = mult;
  return result;
}

Node ArithRewriter::makeUnaryMinusNode(TNode n){
  Node tmp = NodeManager::currentNM()->mkNode(kind::MULT,d_constants->d_NEGATIVE_ONE_NODE,n);
  return tmp;
}

Node ArithRewriter::makeSubtractionNode(TNode l, TNode r){
  Node negR = makeUnaryMinusNode(r);
  Node diff = NodeManager::currentNM()->mkNode(kind::PLUS, l, negR);

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

Node ArithRewriter::rewrite(TNode n){
  Debug("arithrewriter") << "Trace rewrite:" << n << std::endl;

  Node res;

  if(isRelationOperator(n.getKind())){
    res = rewriteAtom(n);
  }else{
    res = rewriteTerm(n);
  }

  Debug("arithrewriter") << "Trace rewrite:" << n << "|->"<< res << std::endl;

  return res;
}

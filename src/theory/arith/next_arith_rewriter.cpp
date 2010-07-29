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


#include "theory/arith/normal_form.h"
#include "theory/arith/next_arith_rewriter.h"
#include "theory/arith/arith_utilities.h"

#include <vector>
#include <set>
#include <stack>


using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

RewriteResponse ArithRewriter::rewritePlus(TNode t){
  Rational acc(0);
  std::vector<Node> total;

  for(TNode::iterator i=t.begin(), tEnd=t.end(); i!=tEnd; ++i){
    TNode curr = postRewrite(*i);
    ArithNormalFormTag tag = getNFTag(curr);
    switch(tag){
    case CONSTANT:
      acc += curr.getConst<Rational>();
      break;
    case VARIABLE:
    case MONOMIAL:
    case COEFFICIENT_MONOMIAL:
      total.push_back(curr);
      break;
    case SUM:
      for(TNode::iterator j=curr.begin(), currEnd = curr.end(); j!=currEnd; ++j){
        total.push_back(*j);
      }
      break;
    case CONSTANT_SUM:
      {
        acc += getConstantFromConstantSum(curr).getConst<Rational>();
        TNode sum = getSumFromConstantSum(curr);
        for(TNode::iterator j=sum.begin(), currEnd=sum.end(); j!=currEnd; ++j){
          total.push_back(*j);
        }
      }
      break;
    default:
      Unreachable();
    }
  }

  Node constant = mkNode<Rational>(acc);
  setNFTag(constant, CONSTANT);

  sort(total, monomial_order);
  combineCoefficients(total);

  if(total.length() == 0){
    return RewriteComplete(constant);
  }

  Node sum;
  if(total.length() == 1){
    sum = total.front();
  }else{
  }

  if(acc == d_constants.ZERO){
    return RewriteComplete(sum);
  }else{
    Node plus = mkNode(kind::PLUS, constant, sum);
    setNFTag(plus, CONSTANT_SUM);
    return RewriteComplete(plus);
  }
}

void combineCoefficients(vector<TNode>& total){
  vector<TNode> newTotal;
  vector<TNode>::iterator iter = total.begin();
  vector<TNode>::iterator end = total.end();

  while(iter != end){
    Node curr = *iter;
    ++iter;
    vector<TNode>::iterator bleck = iter;
    for(; bleck != end; ++bleck){
      TNode next = *bleck;
      if(monomial_order(curr, next) == 0){
        curr = combine(curr, next);
      }else{
        break;
      }
    }
    newTotal.push_back(curr);
    iter = bleck;
  }

  total = newTotal;
}

void rewriteMult(TNode t){
  Assert(t.getKind() == MULT);
  Rational acc(1);
  std::vector<Node> variables;
  std::vector<Node> sums;

  for(TNode::iterator i=t.begin(), tEnd=t.end(); i!=tEnd; ++i){
    TNode curr = postRewrite(*i);
    ArithNormalFormTag tag = curr.getNFTag();
    switch(tag){
    case CONSTANT:
      acc *= curr.getConst<Rational>();
      break;
    case VARIABLE:
      variables.push_back(curr);
      break;
    case MONOMIAL:
      for(TNode::iterator j=curr.begin(), currEnd = curr.end(); j!=currEnd; ++j){
        variables.push_back(*j);
      }
      break;
    case COEFFICIENT_MONOMIAL:
      acc *= getCoefficientFromCoefficientMonomial(curr).getConst<Rational>();
      TNode monomial = getMonomialFromCoefficientMonomial(curr);
      for(TNode::iterator j=monomial.begin(), currEnd = monomial.end();
          j!=currEnd; ++j){
        variables.push_back(*j);
      }
      break;
    case SUM:
    case CONSTANT_SUM:
      sums.push_back(curr);
      break;
    default:
      Unreachable();
    }
  }

  Unimplemented();

}




void rewriteTerm(TNode t){
  if(t.getMetaKind() == kind::metakind::CONSTANT){
    return RewriteComplete(coerceToRationalNode(t));
  }else if(isVariable(t)){
    return RewriteComplete(t);
  }else if(t.getKind() == kind::MINUS){
    Node noMinus = makeSubtractionNode(t[0],t[1]);
    return RewriteMore(sub);
  }else if(t.getKind() == kind::UMINUS){
    Node noUminus = makeUnaryMinusNode(t[0]);
    return RewriteMore(sub);
  }else if(t.getKind() == kind::DIVISION){
    Node noDiv = divByConstant(t);
    return RewriteMore(noDiv);
  }else if(t.getKind() == kind::MULT){
    return rewriteMult(t);
  }else if(t.getKind() == kind::PLUS){
    return rewritePlus(t);
  }else{
    Unreachable();
    return Node::null();
  }
}

Node divByConstant(TNode t){
  Assert(t.getKind() == DIVISION);
  Assert(t.getNumChildren() == 2);

  Node rewrittenNumerator = getPostRewrite(t[0]);
  Node rewrittenDenominator = getPostRewrite(t[1]);

  Assert(rewrittenDenominator.getKind() == kind::CONST_RATIONAL);

  Rational inv = rewrittenDenominator.getConst<Rational>().inverse();
  Node invNode = NodeManager::currentNM()->mkConst<Rational>(inv);

  return NodeManager::currentNM()->mkNode(MULT, invNode, rewrittenNumerator);
}

Node ArithRewriter::makeUnaryMinusNode(TNode n){
  return NodeManager::currentNM()->mkNode(kind::MULT,
                                          d_constants->d_NEGATIVE_ONE_NODE,
                                          n);
}

Node ArithRewriter::makeSubtractionNode(TNode l, TNode r){
  Node negR = makeUnaryMinusNode(r);
  Node diff = NodeManager::currentNM()->mkNode(kind::PLUS, l, negR);

  return diff;
}

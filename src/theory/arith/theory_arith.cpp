#include "expr/node.h"
#include "expr/kind.h"
#include "expr/metakind.h"

#include "util/rational.h"
#include "util/integer.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/normal.h"
#include "theory/arith/slack.h"

#include "theory/arith/rewriter.h"

#include "theory/arith/theory_arith.h"
#include <map>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

Node rewrite(TNode n);


bool isAtom(TNode n){
  Unimplemented();
  return false;
}

bool isTerm(TNode n){
  Unimplemented();
  return false;
}
bool isBasicSum(TNode n){
  Unimplemented();
  return false;
}

Node cons(TNode car, TNode list){
  NodeBuilder<> nb(list.getKind());
  nb << car;
  for(TNode::iterator i = list.begin(); i != list.end(); ++i){
    nb << *i;
  }
  Node ret;
  return ret;
}

Node drop(unsigned int toDrop, TNode list){
  NodeBuilder<> nb(list.getKind());
  for(unsigned int i = toDrop; i < list.getNumChildren(); ++i){
    nb << list[i];
  }
  Node ret = nb;
  return ret;
}

Kind multKind(Kind k){
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
}

Node rewritePlus(TNode sum){
  Assert(sum.getKind() == PLUS);

  //Rewrite children
  Rational constant(0);
  std::map<Node, Rational> rewrittenChildren;
  for(TNode::iterator iter = sum.begin(); iter != sum.end(); ++iter){
    Node kid = *iter;
    Node rewriteKid = rewrite(kid);
    if(rewriteKid.getKind() == CONST_RATIONAL){
      Rational tmp =  rewriteKid.getConst<Rational>();
      constant = constant + tmp;
    }else{
      Assert(rewriteKid.getKind() == PLUS);

      Rational tmp = rewriteKid[0].getConst<Rational>();
      constant = constant + tmp;

      Node::iterator rkIter = rewriteKid.begin();
      ++rkIter;
      for(;rkIter != rewriteKid.end(); ++rkIter){
        Node prod = *rkIter;
        //TODO
      }
    }
    //cases
  }

  Node cNode = mkRationalNode(constant);

  NodeBuilder<> nb(PLUS);
  nb << cNode;
  for(std::map<Node, Rational>::iterator iter = rewrittenChildren.begin();
      iter != rewrittenChildren.end();
      ++iter){
    Rational e = (*iter).second;
    if(e != TheoryArith::s_ZERO){
      Node coeff = mkRationalNode(e);
      nb << cons(coeff, (*iter).first);
    }
  }
  if(nb.getNumChildren() == 1){
    return cNode;
  }else{
    Node ret = nb;
    return ret;
  }
}


Node rewriteMult(TNode mult){
  Unimplemented();
  return Node::null();
}

Node rewriteTerm(TNode term){
  switch(term.getMetaKind()){
  case metakind::VARIABLE:
    return term;
  case metakind::CONSTANT:
    return coerceToRationalNode(term);
  default:
    switch(term.getKind()){
    case PLUS:
      return rewritePlus(term);
    case MULT:
      return rewriteMult(term);
    default:
      Unhandled();
      return Node::null();
    }
  }
}

Node rewriteAtom(TNode atom){
  Node nf;

  Kind k = atom.getKind();
  Assert(isRelationOperator(k));

  // left |><| right
  TNode left = atom[0];
  TNode right = atom[1];


  // left - right |><| 0
  Node no = mkRationalNode(TheoryArith::s_NEGATIVE_ONE);
  TNode neg = NodeManager::currentNM()->mkNode(MULT, no, right);
  TNode diff = NodeManager::currentNM()->mkNode(PLUS,left,neg);

  Node rewritten = rewrite(diff);

  if(rewritten.getKind() == PLUS){
    Assert(rewritten.getNumChildren() >= 2);
    Rational c = -((rewritten[0]).getConst<Rational>());
    if(rewritten.getNumChildren() == 2){
      TNode prod = rewritten[1];
      if(prod.getMetaKind() == metakind::VARIABLE){
        nf =NodeManager::currentNM()-> mkNode(k,
                    prod,
                    mkRationalNode(c));
      }else{
        Assert(prod.getKind() == MULT);
        Assert(prod.getNumChildren() == 2);
        Rational d = ((prod[0]).getConst<Rational>()).inverse();
        TNode var = drop(1, prod);
        Kind newDir = (d < 0) ? multKind(k) : k;

        Rational tmp = c*d;
        Node c_times_d = mkRationalNode(tmp);
        nf = NodeManager::currentNM()->mkNode(newDir, prod, c_times_d);
      }
    }else{
      Node dropC = drop(1,rewritten);
      nf = NodeManager::currentNM()->mkNode(MULT, mkRationalNode(c), dropC);
    }
  }else{
    Assert(rewritten.getKind() == CONST_RATIONAL);
    bool eval = evaluateConstantPredicate(k,
                         rewritten.getConst<Rational>(),
                         TheoryArith::s_ZERO);
    nf = eval ? TheoryArith::s_TRUE_NODE : TheoryArith::s_FALSE_NODE;
  }

  return nf;
}

Node rewrite(TNode n){

  if(n.getAttribute(IsNormal())){
    return n;
  }

  Node res;

  if(isAtom(n)){
    res = rewriteAtom(n);
  }else if(isTerm(n)){
    res = rewriteTerm(n);
  }else{
    Unhandled();
  }

  if(n == res){
    n.setAttribute(NormalForm(), Node::null());
  }else{
    n.setAttribute(NormalForm(), res);
  }

  return res;
}

void registerAtom(TNode rel){
  addBound(rel);
  //Anything else?
}

void TheoryArith::registerTerm(TNode tn){
  if(isAtom(tn)){
    Node normalForm = (isNormalized(tn)) ? Node(tn) : rewrite(tn);
    Kind k = normalForm.getKind();

    if(k != kind::CONST_BOOLEAN){
      Assert(isRelationOperator(k));
      TNode left  = normalForm[0];
      TNode right = normalForm[1];
      if(left.getKind() == PLUS){
        //We may need to introduce a slack variable.
        Assert(left.getNumChildren() >= 2);
        Assert(isBasicSum(left));
        Node slack;
        if(!left.getAttribute(Slack(), slack)){
          //TODO
          //slack = NodeManager::currentNM()->mkVar(RealType());
          left.setAttribute(Slack(), slack);
          makeBasic(slack);

          Node slackEqLeft = NodeManager::currentNM()->mkNode(EQUAL,slack,left);
          slackEqLeft.setAttribute(TheoryArithPropagated(), true);
          //TODO this has to be wrong no?
          d_out->lemma(slackEqLeft);

          d_tableau.addRow(slackEqLeft);
        }

        Node rewritten = NodeManager::currentNM()->mkNode(k,slack,right);
        registerAtom(rewritten);
      }else{
        Assert(left.getMetaKind() == metakind::VARIABLE);
        Assert(right.getKind() == CONST_RATIONAL);
        registerAtom(normalForm);
      }
    }
  }
}

/**
 * x <= l
 * ? c < l
 */
bool belowLowerBound(TNode x, DeltaRational& c, bool strict){
  DeltaRational* l;
  if(!x.getAttribute(partial_model::LowerBound(), l)){
    // l = -\intfy
    // ? c < -\infty |-  _|_
    return false;
  }

  if(strict){
    return c < *l;
  }else{
    return c <= *l;
  }
}

/**
 * x <= u
 * ? c < u
 */
bool aboveUpperBound(TNode x, DeltaRational& c, bool strict){
  DeltaRational* u;
  if(!x.getAttribute(partial_model::UpperBound(), u)){
    // c = \intfy
    // ? c > \infty |-  _|_
    return false;
  }

  if(strict){
    return c > *u;
  }else{
    return c >= *u;
  }
}
/* procedure AssertUpper( x_i <= c_i) */
void TheoryArith::AssertUpper(TNode n){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(), dcoeff);

  if(aboveUpperBound(x_i, c_i, false) ){
    return; //sat
  }
  if(belowLowerBound(x_i, c_i, true)){
    d_out->conflict(n);
    return;
  }

  setUpperBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }
}

/* procedure AssertLower( x_i >= c_i ) */
void TheoryArith::AssertLower(TNode n){
  TNode x_i = n[0];
  Rational dcoeff = Rational(Integer(deltaCoeff(n.getKind())));
  DeltaRational c_i(n[1].getConst<Rational>(),dcoeff);

  if(belowLowerBound(x_i, c_i, false)){
    return; //sat
  }
  if(aboveUpperBound(x_i, c_i, true)){
    d_out->conflict(n);
    return;
  }

  setLowerBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }
}

void TheoryArith::update(TNode x_i, DeltaRational& v){

  DeltaRational assignment_x_i = getAssignment(x_i);
  DeltaRational diff = v - assignment_x_i;

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    TNode x_j = *basicIter;
    Row* row_j = d_tableau.lookup(x_j);

    Rational& a_ji = row_j->lookup(x_i);

    DeltaRational assignment = getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    setAssignment(x_j, nAssignment);
  }

  setAssignment(x_i, v);
}

void TheoryArith::pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v){
  Row* row_i = d_tableau.lookup(x_i);
  Rational& a_ij = row_i->lookup(x_i);


  DeltaRational betaX_i = getAssignment(x_i);

  Rational inv_aij = a_ij.inverse();
  DeltaRational theta = (v - betaX_i)*inv_aij;

  setAssignment(x_i, v);


  DeltaRational tmp = getAssignment(x_j) + theta;
  setAssignment(x_j, tmp);

  for(Tableau::VarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end();
      ++basicIter){
    TNode x_k = *basicIter;
    Row* row_k = d_tableau.lookup(x_k);

    if(x_k != x_i){
      DeltaRational a_kj = row_k->lookup(x_j);
      DeltaRational nextAssignment = getAssignment(x_k) + theta;
      setAssignment(x_k, nextAssignment);
    }
  }

  d_tableau.pivot(x_i, x_j);
}

TNode selectSmallestInconsistentVar(){
  Unimplemented();
  return TNode::null();
}

TNode selectSlack(TNode x_i, bool lb){
  Unimplemented();
  return TNode::null();
}


TNode TheoryArith::updateInconsistentVars(){ //corresponds to Check() in dM06

  while(true){
    TNode x_i = selectSmallestInconsistentVar();
    if(x_i == Node::null()){
      return Node::null(); //sat
    }
    DeltaRational beta_i = getAssignment(x_i);
    DeltaRational l_i = getLowerBound(x_i);
    DeltaRational u_i = getUpperBound(x_i);
    if(belowLowerBound(x_i, beta_i, true)){
      TNode x_j = selectSlack(x_i, true);
      if(x_j == TNode::null() ){
        return x_i; //unsat
      }
      pivotAndUpdate(x_i, x_j, l_i);
    }else if(aboveUpperBound(x_i, beta_i, true)){
      TNode x_j = selectSlack(x_i, false);
      if(x_j == TNode::null() ){
        return x_j; //unsat
      }
      pivotAndUpdate(x_i, x_j, u_i);
    }
  }
}
Node pushInNegation(Node assertion){
  Assert(assertion.getKind() == NOT);

  Node p = assertion[0];

  Kind k;

  switch(p.getKind()){
  case EQUAL:
    return assertion;
  case GT:
    k = LT;
    break;
  case GEQ:
    k = LEQ;
    break;
  case LEQ:
    k = GEQ;
    break;
  case LT:
    k = GT;
    break;
  default:
    Unreachable();
  }

  return NodeManager::currentNM()->mkNode(k, p[0],p[1]);
}
void TheoryArith::check(Effort level){
  while(!done()){
    Node assertion = get();

    if(assertion.getKind() == NOT){
      assertion = pushInNegation(assertion);
    }

    switch(assertion.getKind()){
    case LT:
    case LEQ:
      AssertUpper(assertion);
      break;
    case GEQ:
    case GT:
      AssertLower(assertion);
      break;
    case EQUAL:
      AssertUpper(assertion);
      AssertLower(assertion);
      break;
    case NOT: // must be a disequality
      d_diseq.push_back(assertion);
      break;
    default:
      Unhandled();
    }
  }

  if(fullEffort(level)){
    NodeBuilder<> lemmas(AND);
    for(context::CDList<Node>::const_iterator i = d_diseq.begin(); i!= d_diseq.end(); ++i){
      Node assertion = *i;
      TNode eq = assertion[0];
      TNode x_i = eq[0];
      TNode c_i = eq[1];
      DeltaRational constant =  c_i.getConst<Rational>();
      if(getAssignment(x_i) == constant){
        Node lt = NodeManager::currentNM()->mkNode(LT,x_i,c_i);
        Node gt = NodeManager::currentNM()->mkNode(GT,x_i,c_i);
        Node disjunct = NodeManager::currentNM()->mkNode(OR, eq, lt, gt);
        lemmas<< disjunct;
      }
    }
    Node caseSplits = lemmas;
    //TODO
    //DemandCaseSplits(caseSplits);
  }
}

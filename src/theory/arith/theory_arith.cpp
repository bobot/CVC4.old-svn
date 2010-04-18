
/** DRAFT 1
 * Normal form for predicates:
 *    TRUE
 *    FALSE
 *    var_i |><| b
 *    \sum_i product_i  |><| b
 *  where
 *   1) b is of type CONST_RATIONAL
 *   2) |><| is of type <=, >, =, < or >=
 *   3) product_i is in product normal form,
 *   4) product_i is not 0,
 *   5) product_i's are in strictly ascending productOrder,
 *   6) product_i has at least 2 members,
 *   7) product_1 has a positive coefficient, and
 *   8) var_i has metakind variable.
 *
 * Normal form for terms:
 *    c
 *    c + \sum_i product_i
 *  where
 *   1) c is of type CONST_RATIONAL,
 *   2) product_i is in product normal form,
 *   3) product_i is not a constant,
 *   4) and product_i's are in strictly ascending productOrder.
 *
 * Normal form for products:
 *    d
 *    var_i
 *    e * \prod var_i
 *  where
 *   1) d,e is of type CONST_RATIONAL,
 *   2) e != 0,
 *   3) e != 1 or there are at least 2 variables,
 *   2) var_i is of metakind VARIABLE,
 *   3) and var_i are in increasing (not strict) nodeOrder.
 *
 * productOrder is well defined over normal form products as follows:
 *   cmp(d,d') = rational order.
 *   cmp(d,var_i)= -1
 *   cmp(var_i,var_j) is the node order
 *   cmp(var_i,d * \prod var_i) = -1
 *   cmp(p = d * \prod var_i, p' = d' * \prod var_i')=
 *      if(len(p) == len(p'))
 *      then tupleCompare(var_i, var_i')
 *      else len(p) - len(p')
 */



/** DRAFT 2
 * Normal form for predicates:
 *    TRUE
 *    FALSE
 *    var |><| b
 *    (\sum_{i=1 to N} p_i)  |><| b
 *  where
 *   1) b is of type CONST_RATIONAL
 *   2) |><| is of kind <, <=, =, >= or >
 *   3) p_i is in PNF,
 *   5) p_i's are in strictly ascending <p,
 *   6) N >= 2,
 *   7) the kind of (\sum_{i=1 to N} p_i) is an N arity PLUS,
 *   8) p_1 has coefficient 1, and
 *   9) var has metakind variable.
 *
 * PNF:
 *    v
 *    d * v
 *    (\prod_{i=1 to M} v_i)
 *    d * (\prod_{i=1 to M} v_i)
 *  where
 *   1) d is of type CONST_RATIONAL,
 *   2) d != 0,
 *   3) d != 1,
 *   4) M>=2,
 *   5) v, v_i are of metakind VARIABLE,
 *   6) v_i are in increasing (not strict) nodeOrder, and
 *   7) the kind of (\prod_{i=1 to M} v_i) is an M arity MULT.
 *
 * <p is defined over PNF as follows (skipping some symmetry):
 *   cmp(  v,   v') is the node order over v and v'
 *   cmp(  v,d'*v') is the node order over v and v'
 *   cmp(d*v,d'*v') is the node order over v and v'
 *   cmp(  v,   (\prod v'_i)) = -1
 *   cmp(d*v,   (\prod  v_i)) = -1
 *   cmp(  v, d*(\prod v'_i)) = -1
 *   cmp(d*v, d*(\prod  v_i)) = -1
 *   cmp((\prod_{i=1 to M} v_i),(\prod_{i=1 to M'} v'_i))=
 *      if(M == M')
 *      then tupleCompare(v_i, v'_i)
 *      else M - M'
 *   cmp((\prod_{i=1 to M} v_i), d*(\prod_{i=1 to M'} v'_i))=
 *      if(M == M')
 *      then tupleCompare(v_i, v'_i)
 *      else M - M'
 *   cmp(d * (\prod_{i=1 to M} v_i), d' * (\prod_{i=1 to M'} v'_i))=
 *      if(M == M')
 *      then tupleCompare(v_i, v'_i)
 *      else M - M'
 *
 * Rewrite Normal Form for Terms:
 *    b
 *    p
 *    c + p
 *    (\sum_{i=1 to N} p_i)
 *    c + (\sum_{i=1 to N} p_i)
 *  where
 *   1) b,c is of type CONST_RATIONAL,
 *   2) c != 0,
 *   3) p, p_i is in PNF,
 *   4) N >= 2
 *   5) the kind of (\sum_{i=1 to N} p_i) is an N arity PLUS,
 *   6) and p_i's are in strictly <p.
 *
 */


bool isVarMultList(TNode v){
  for(v = 1 to l.getLength()){
    if(!isVar(v[i])){
      return false;
    }
  }

  for(v = 2 to l.getLength()){
    if(!(v[i-1] <= v[i])){
      return false;
    }
  }
  return true;
}

bool isPNF(TNode p){
   if(p.getKind() == MULT){
     if(p[0].getKind() == CONST_RATIONAL){
       if(p[0].getConst<CONST_RATIONAL>() != 0 &&
          p[0].getConst<CONST_RATIONAL> != 1){
         if(p[1].getKind() != MULT){
           if(p[1].getMetaKind() == VARIABLE){
             return true; // d * v
           }else{
             return false;
           }
         }else{
           if(isVarMultList(p[1])){
             return true; // d * (\prod_{i=1 to M} v_i)
           }else{
             return false;
           }
         }
       }else{
         return false;
       }
     }else{
       if(isVarMultList(p)){
         return true; //(\prod_{i=1 to M} v_i)
       }else{
         return false;
       }
     }
   }else{
     if(p.getMetaKind() == VARIABLE){
       return true; // v
     }else{
       return false;
     }
   }
}


bool <p(TNode p0, TNode p1){
  PNFType t0 = same as the comments in isPNF(p0);
  PNFType t1 = same as the comments in isPNF(p1);

  bool t0IsVar = (t0 == "v") ||(t0 == "d*v");
  bool t1IsVar = (t1 == "v") ||(t1 == "d*v");

  if(t0IsVar && t1IsVar){
    TNode v0 = (t0 == "d*v") ? p0[1] : p0;
    TNode v1 = (t1 == "d*v") ? p1[1] : p1;
    return v0 < v1;
  }else if(!t0IsVar && t1IsVar){
    return false;
  }else if(t0IsVar && !t1IsVar){
    return true;
  }else{
    TNode prod0 = (t0 == "d * (\prod_{i=1 to M} v_i)") ? p0[1] : p0;
    TNode prod1 = (t1 == "d * (\prod_{i=1 to M} v_i)") ? p1[1] : p1;

    int M0 = prod0.getNumChildren();
    int M1 = prod1.getNumChildren();

    if(M0 == M1){
      for(i in 1 to M0){
        if(prod0[i] < prod[i]){
          return true;
        }
      }
      return false;
    }else{
      return M0 < M1;
    }
  }
}

bool isPNFSum(TNode p){

  for(i = 1 to p.getNumChildren()){
    if(!isPNF(p[i])){
      return false;
    }
  }
  for(i = 2 to p.getNumChildren()){
    if(!(p[i-1] <p p[i])){
      return false;
    }
  }
  return true;
}

string isNormalFormTerm(TNode t){
  Kind k = t.getKind();
  if(k != PLUS){
    if(k == CONST_RATIONAL){
      return true; // b
    }else if(isPNF(p)){
      return true; // p
    }else{
      return false;
    }
  }else{
    if(t[0].getKind() == CONST_RATIONAL){
      if(t[0].getConst<CONST_RATIONAL>() != 0){
        if(t[1].getKind() == PLUS){
          if(isPNFSum(t[1])){
            return true; // c + (\sum_{i=1 to N} p_i)
          }else{
            return false;
          }
        }else{
          if(isPNF(t[1])){
            return true; // c + p
          }else{
            return false;
          }
        }
      }else{
        return false;
      }
    }else{
      if(isPNFSum(t)){
        return true; // (\sum_{i=1 to N} p_i)
      }else{
        return false;
      }
    }
  }
}

Node drop(unsigned int toDrop, TNode list){
  NodeBuilder<> nb(list.getKind());
  for(int i = toDrop; i < list.getNumChildren(); ++i){
    nb << list[i];
  }
  Node ret = nb;
  return ret;
}

Kind multKind(Kind k){
  switch(k){
  case LT: return GT;
  case LEQ: return GEQ;
  case EQ: return EQ;
  case GEQ: return LEQ;
  case GT: return LT;
  default:
    Unhandled();
  }
  return NULL;
}

Node mkRationalNode(Rational& q){
  return NodeManager::currentNM()->mkConst<CONST_RATIONAL>(q);
}

Node rewritePlus(TNode sum){
  Assert(sum.getKind() == PLUS);

  //Rewrite children
  Rational constant(0);
  std::map<Node, Rational> rewrittenChildren;
  for(TNode::iterator iter = sum.begin(); iter != sum.end() ++iter){
    Node kid = *iter;
    Node rewriteKid = rewrite(kid);
    if(rewriteKid.getKind() == CONST_RATIONAL){
      constant += rewriteKid.getConst<CONST_RATIONAL>();
    }else{
      Assert(rewriteKid.getKind() == PLUS);
      constant += rewriteKid[0].getConst<CONST_RATIONAL>();
      Node::iterator rkiter = rewriteKid.begin();
      ++rkIter;
      for(;rkIter != rewriteKid.end(); ++rkiter){
        Node prod = *rkIter;

        
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
    Rational e = *iter.second;
    if(e != zero){
      Node coeff = mkRationalNode(e);
      nb << cons(coeff, *iter.first);
    }
  }
  if(nb.getNumChildren() == 1){
    return cNode;
  }else{
    Node ret = nb;
    return ret;
  }
}

Node coerceToRational(TNode constant){
  switch(constant.getKind()){
  case CONST_INTEGER:
    {
      Rational q(constant.getConst<CONST_INTEGER>());
      return NodeManager::currentNM()->mkConst<CONST_RATIONAL>(q);
    }
  case CONST_RATIONAL:
    return constant;
  default:
    Unhandled();
  }

  return Node::null();
}

Node rewriteTerm(TNode term){
  switch(term.getMetaKind()){
  case VARIABLE:
    return term;
  case CONSTANT:
    return coerceToRational(term);
  default:
    switch(term.getKind()){
    case PLUS:
      return rewritePlus(term);
    case MULT:
      return rewriteMult(term);
    default:
      Unhandled();
      return Node::null;
    }
  }
}

Node rewriteAtom(TNode atom){
  Node nf;

  Kind k = atom.getKind();
  Assert(k \in {LT, LEQ, ...});

  // left |><| right
  TNode left = atom[0];
  TNode right = atom[1];


  // left - right |><| 0
  TNode diff = mkNode(MINUS, left, right);

  Node rewritten = rewrite(diff);

  if(rewritten.getKind() == PLUS){
    Assert(rewritten.getNumChildren() >= 2);
    Rational c = (rewritten[0]).getConst<CONST_RATIONAL>().negate();
    if(rewritten.getNumChildren() == 2){
      TNode prod = rewritten[1];
      if(prod.getMetaKind() == VARIABLE){
        nf = mkNode(k, prod, mkConst<CONST_RATIONAL>(c))
      }else{
        Assert(prod.getKind() == MULT);
        Assert(prod.getNumChildren() == 2);
        Rational e = ((prod[0]).getConst<CONST_RATIONAL>()).inverse();
        TNode var = drop(1, prod);
        Kind newDir = (d < 0) ? multKind(k) : k;
        nf = mkNode(newDir, prod, mkConst<CONST_RATIONAL>(c*d));
      }
    }else{
      Node dropC = drop(1,rewritten);
      nf = mkNode(dropC, mkConst<CONST_RATIONAL>(c));
    }
  }else{
    Assert(rewritten.getKind() == CONST_RATIONAL);
    bool eval = evaluate(k, rewritten, d_zero);
    nf = eval ? TRUE_NODE : FALSE_NODE;
  }

  return nf;
}

Node rewrite(TNode n){
  if(n.getAttribute(IsNormal())){
    return n;
  }

  Node res;

  if(n.isAtom()){
    res = rewriteAtom(n);
  }else if(n.isTerm()){
    res = rewriteTerm(n);
  }else{
    Unhandled();
  }

  if(n == nf){
    n.setAttribute(NormalForm(), Node::null);
  }else{
    n.setAttribute(NormalForm(), nf);
  }

  return res;
}

void registerRewrittenAtom(TNode rel){
  addBound(eq);
  //Anything else?
}

void register(TNode tn){
  if(tn.isAtom()){
    Node normalForm = (isNormalized(tn)) ? tn : rewrite(tn);
    Kind k = normalForm.getKind();

    if(!(k == TRUE || k == FALSE)){
      Assert(k \in {LT,LEQ,EQ,GEQ,GT});
      TNode left  = normalForm[0];
      TNode right = normalForm[1];
      if(left.getKind() == PLUS){
        //We may need to introduce a slack variable.
        Assert(left.getNumChildren() >= 2);
        Assert(isBasicSum(left));
        Node slack;
        if(!left.getAttribute(Slack(), slack)){
          slack = NodeManager::getCurrentNM()->mkVar(RealType());
          left.setAttribute(Slack(), slack);
          makeBasic(slack);

          Node slackEqLeft = slack.makeEq(left);
          slackEqLeft.setAttribute(TheoryArithPropagated(), true);
          output_channel.propogateToLevel(0, slackEqLeft);

          d_tableau.addRow(slack, left);
        }

        Node rewritten = mkNode(k,slack,right);
        registerAtom(rewritten);
      }else{
        Assert(left.getMetaKind() == VARIABLE);
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
template <bool strict>
bool belowLowerBound(TNode x, ExtendedConstant& c){
  ExtendedConstant l;
  if(!x.getAttribute(LowerBound(), l)){
    // l = -\intfy
    // ? c < -\infty |-  _|_
    return false;
  }

  if(strict){
    return c < l;
  }else{
    return c <= l;
  }
}

/**
 * x <= u
 * ? c < u
 */
template <bool strict>
bool aboveUpperBound(TNode x, ExtendedConstant& c){
  ExtendedConstant u;
  if(!x.getAttribute(UpperBound(), l)){
    // c = \intfy
    // ? c > \infty |-  _|_
    return false;
  }

  if(strict){
    return c > u;
  }else{
    return c >= u;
  }
}
/* procedure AssertUpper( x_i <= c_i) */
void AssertUpper(TNode n){
  TNode x_i = n[0];
  ExtendedRational c_i(n[1].getConst<CONST_RATIONAL>(),
                       deltaCoeff(n.getKind()));

  if(aboveUpperBound<false>(x_i, c_i) ){
    return; //sat
  }
  if(belowLowerBound<true>(x_i, c_i )){
    d_outputchannel.conflict(n);
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
void AssertLower(TNode n){
  TNode x_i = n[0];
  ExtendedRational c_i(n[1].getConst<CONST_RATIONAL>(),
                       deltaCoeff(n.getKind()));

  if(belowLowerBound<false>(x_i, c_i)){
    return; //sat
  }
  if(aboveUpperBound<true>(x_i, c_i)){
    d_outputchannel.conflict(n);
    return;
  }

  setLowerBound(x_i, c_i);

  if(!isBasic(x_i)){
    if(getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }
}

void update(TNode x_i, DeltaRational& v){

  DeltaRational assignment_x_i = getAssignment(x_i);
  DeltaRational diff = v - assignment_x_i;

  for(Tableau::iterator rowIter = d_tableau.begin();
      rowIter != d_tableau.end();
      ++rowIter){
    Row& row_j = *rowIter;
    TNode x_j = row.getBasic();

    Rational& a_ji = row_j.lookup(x_i);

    ExtendedRational assignment = getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(a_ji*diff);
    setAssignment(x_j, nAssignment);
  }

  setAssignment(x_i, v);
}

void pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v){
  Row& row_i = d_tableau[x_i];
  Rational& a_ij = row_i.lookup(x_i);


  DeltaRational betaX_i = getAssignment(x_i);

  DeltaRational theta = (a_ij.inverse())*(v - betaX_i);

  setAssignment(x_i, v);
  setAssignment(x_j, getAssignment(x_j) + theta);

  for(Tableau::iterator rowIter = d_tableau.begin(); rowIter != d_tableau.end(); ++rowIter){
    Row& row_k = *rowIter;
    TNode x_k = row.getBasic();
    if(x_k != x_i){
      ExtendedRational a_kj = row_k.lookup(x_j);
      setAssignment(x_k, getAssignment(x_k) + theta);
    }
  }

  d_tableau.pivot(x_i, x_j);
}

bool Check(){

  while(true){
    TNode x_i = selectSmallestInconsistentVar();
    if(x_i == Node::Null){
      return satisfiable;
    }
    if(belowLowerBound(x_i)){
      TNode x_j = selectSlack<true>(x_i);
      if(x_j is NULL){
        return unsat;
      }
      pivotAndUpdate(x_i, x_j, l_i);
    }
    if(getAssignment(x_i) > upperBound(x_i)){
      TNode x_j = selectSlack<false>(x_i);
      if(x_j is NULL){
        return unsat;
      }
      pivotAndUpdate(x_i, x_j, u_i);
    }
  }
}

void TheoryUF::check(Effort level){
  while(!done()){
    Node assertion = get();

    if( assertion : x_i <= c_i ){
      AssertUpper(assertion);
    }else if( assertion : x_i >= c_i ){
      AssertLower(assertion);
    }else if( assertion : x_i == c_i){
      AssertUpper(assertion);
      AssertLower(assertion);
    }else if( assertion : x_i != c_i){
      d_diseq.push_back(assertion);
    }else {
      Unhandled();
    }
  }

  if(fullEffort(level)){
    NodeBuilder lemmas(AND);
    for(assertion in d_diseq){
      TNode eq = assertion[0];
      TNode x_i = eq[0];
      TNode c_i = eq[1];
      if(getAssignment(x_i) == c_i.getConst<CONT_RATIONAL>() ){
        lemmas<< (eq || (mkNode(LT,x_i)) || (mkNode(GT,x_i,c_i)) );
      }
    }
    Node caseSplits = lemmas;
    DemandCaseSplits(caseSplits);
  }
}

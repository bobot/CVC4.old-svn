
/**
 * Normal form for predicates:
 *    \sum_i product_i  |><| b
 *  where
 *   1) b is of type CONST_RATIONAL
 *   2) |><| is of type <=, >, =, or != (> and != are negations)
 *   3) product_i is in product normal form,
 *   4) product_i is not 0
 *   5) and product_i's are in strictly ascending productOrder.
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

  for(Tableau::iterator rowIter = d_tableau.begin(); rowIter != d_tableau.end(); ++rowIter){
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

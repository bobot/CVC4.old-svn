
class Row {
  TNode d_x_i;

  std::set<TNode> d_nonbasic;
  std::hash_map<TNode, Rational> d_coeffs;

public:

  /**
   * Construct a row equal to:
   *   basic = \sum_{x_i} c_i * x_i
   */
  Row(TNode basic, TNode sum): d_x_i(basic),d_nonbasic(), d_coeffs(){
    Assert(d_x_i.getMetaKind() == VARIABLE);
    Assert(d_x_i.getType() == REAL);
    Assert(sum.getKind() == PLUS);

    for(TNode::iterator iter=sum.begin(); iter != sum.end() ++iter){
      TNode pair = *iter;
      Assert(pair.getKind() == MULT);
      Assert(pair.getNumChildren() == 2);
      TNode coeff = pair[0];
      TNode var_i = pair[1];
      Assert(coeff.getKind() == CONST_RATIONAL);
      Assert(var_i.getKind() == VARIABLE);
      Assert(var_i.getKind() == REAL);
      Assert(!has(var_i));
      d_nonbasic.add(var_i);
      d_coeffs[var_i] = coeff.getConst<CONST_RATIONAL>();
    }
  }

  TNode basicVar(){
    return d_x_i;
  }

  bool has(TNode x_j){
    return d_coeffs.find(x_j) != d_coeffs.end();
  }

  Rational& lookup(TNode x_j){
    return d_coeffs[x_j];
  }

  void pivot(TNode x_j){
    Rational negInverseA_rs = -(lookup(x_j).inverse());
    d_coeffs[d_x_i] = Rational(-1);
    d_coeffs.erase(x_j);

    d_nonbasic.remove(x_j);
    d_nonbasic.add(d_x_i);
    d_x_i = x_j;

    for(set<TNode>::iterator nonbasicIter = d_nonbasic.begin();
        nonbasicIter != d_nonbasic.end();
        ++nonbasicIter){
      d_coeffs *= negInverseA_rs;
    }
  }

  void subsitute(Row& row_s){
    TNode x_s = row_s.basicVar();

    Assert(!has(x_s));
    Assert(x_s != d_x_i);


    Rational a_rs = lookup(x_s);
    d_coeffs.erase(x_s);

    for(std::set<TNode>::iterator iter = row_s.d_nonbasic.begin();
        iter != row_s.d_nonbasic.end();
        ++iter){
      TNode x_j = *iter;
      Rational a_sj = a_rs * row_s.lookup(x_j);
      if(has(x_j)){
        d_coeffs[x_j] += a_sj;
      }else{
        d_nonbasic.add(x_j);
        d_coeffs[x_j] = a_sj;
      }
    }
  }
};

class Tableau {
private:
  typedef std::set<TNode> VarSet;
  typedef std::hash_map<TNode, Row> RowsTable;

  VarSet d_basicVars;
  RowsTables d_rows;

public:
  /**
   * Constructs an empty tableau.
   */
  Tableau() : d_basicVars(), d_rows() {}

  /**
   * Iterator for the tableau. Iterates over rows.
   */
  class iterator {
  private:
    VarSet::iterator variableIter;
    iterator(VarSet::iterator& i) : variableIter(i){}
  public:
    void operator++(){
      ++variableIter;
    }

    bool operator==(iterator& other){
      return variableIter == other.variableIter;
    }
    bool operator!=(iterator& other){
      return variableIter != other.variableIter;
    }

    Row& operator*(){
      return d_rows[*variableIter];
    }
  };
  iterator begin(){
    return iterator(d_basicVars.begin());
  }
  iterator end(){
    return iterator(d_basicVars.end());
  }

  void addRow(TNode eq){
    Assert(eq.getKind() == EQ);
    Assert(eq.getNumChildren() == 2);

    TNode var = eq[0];
    TNode sum = eq[1];

    Assert(isAdmissableVariable(var));
    Assert(var.getAttribute(IsBasic()));

    d_basicVars.add(var);
    d_rows[var] = Row(var.,sum);
  }

  /**
   * preconditions:
   *   x_r is basic,
   *   x_s is non-basic, and
   *   a_rs != 0.
   */
  void pivot(TNode x_r, TNode x_s){
    RowsTable::iterator ptrRow_r = d_rows.find(x_r);
    Assert(row_r != d_rows.end());

    Row row_s = *ptrRow_r;

    Assert(row_s.has(x_s));
    row_s.pivot(x_s);

    d_rows.erase(ptrRow_r);
    d_basicVars.remove(x_r);
    makeNonbasic(x_r);

    d_rows.insert(mk_pair(xs,row_s));
    d_basicVars.insert(x_s);
    makeBasic(x_s);

    for(Tableau::iterator rowIter = begin(); rowIter != end(); ++rowIter){
      Row& row_k = *rowIter;
      if(row_k.basicVar() != x_s){
        if(row_k.has(x_s)){
          row_k.subsitute(row_s);
        }
      }
    }
  }
};

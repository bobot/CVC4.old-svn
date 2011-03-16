/*********************                                                        */
/*! \file tableau.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
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


#include "theory/arith/tableau.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

Tableau::Tableau(const Tableau& tab){
  internalCopy(tab);
}

void Tableau::internalCopy(const Tableau& tab){
  uint32_t N = tab.d_rowsTable.size();

  Debug("tableau::copy") << "tableau copy "<< N << endl;

  if(N >= 1){
    for(unsigned i = 0; i < N; ++i){
      d_columnMatrix.push_back(new Column());
    }
    d_rowsTable.insert(d_rowsTable.end(), N, NULL);
    d_basicVariables.increaseSize(N-1);

    Assert(d_basicVariables.allocated() == tab.d_basicVariables.allocated());

    d_rowCount.insert(d_rowCount.end(), N, 0);
  }

  ArithVarSet::iterator i_basicIter = tab.d_basicVariables.begin();
  ArithVarSet::iterator i_basicEnd = tab.d_basicVariables.end();
  for(; i_basicIter != i_basicEnd; ++i_basicIter){
    ArithVar basicVar = *i_basicIter;
    const ReducedRowVector* otherRow = tab.d_rowsTable[basicVar];

    Assert(otherRow != NULL);

    std::vector< ArithVar > variables;
    std::vector< Rational > coefficients;
    otherRow->enqueueNonBasicVariablesAndCoefficients(variables, coefficients);

    ReducedRowVector* copy = new ReducedRowVector(basicVar, variables, coefficients, d_rowCount, d_columnMatrix);

    Debug("tableau::copy") << "copying " << basicVar << endl;
    copy->printRow();

    d_basicVariables.add(basicVar);
    d_rowsTable[basicVar] = copy;
  }
}

Tableau& Tableau::operator=(const Tableau& other){
  clear();
  internalCopy(other);
  return (*this);
}

Tableau::~Tableau(){
  clear();
}

void Tableau::clear(){
  while(!d_basicVariables.empty()){
    ArithVar curr = *(d_basicVariables.begin());
    ReducedRowVector* vec = removeRow(curr);
    delete vec;
  }

  //must be emptied after rows
  for(ColumnMatrix::iterator i = d_columnMatrix.begin(), end = d_columnMatrix.end(); i != end; ++i ){
    Column* col = *i;
    delete col;
  }

  d_rowsTable.clear();
  d_basicVariables.clear();
  d_rowCount.clear();
  d_columnMatrix.clear();
}

void Tableau::addRow(ArithVar basicVar,
                     const std::vector<Rational>& coeffs,
                     const std::vector<ArithVar>& variables){

  Assert(coeffs.size() == variables.size());

  //The new basic variable cannot already be a basic variable
  Assert(!d_basicVariables.isMember(basicVar));
  d_basicVariables.add(basicVar);
  ReducedRowVector* row_current = new ReducedRowVector(basicVar,variables, coeffs,d_rowCount, d_columnMatrix);
  d_rowsTable[basicVar] = row_current;

  //A variable in the row may have been made non-basic already.
  //If this is the case we fake pivoting this variable
  vector<ArithVar>::const_iterator varsIter = variables.begin();
  vector<ArithVar>::const_iterator varsEnd = variables.end();

  for( ; varsIter != varsEnd; ++varsIter){
    ArithVar var = *varsIter;

    if(d_basicVariables.isMember(var)){
      ReducedRowVector& row_var = lookup(var);
      row_current->substitute(row_var);
    }
  }
}

ReducedRowVector* Tableau::removeRow(ArithVar basic){
  Assert(d_basicVariables.isMember(basic));

  ReducedRowVector* row = d_rowsTable[basic];

  d_basicVariables.remove(basic);
  d_rowsTable[basic] = NULL;

  return row;
}

void Tableau::pivot(ArithVar x_r, ArithVar x_s){
  Assert(d_basicVariables.isMember(x_r));
  Assert(!d_basicVariables.isMember(x_s));

  Debug("tableau") << "Tableau::pivot(" <<  x_r <<", " <<x_s <<")"  << endl;

  ReducedRowVector* row_s = d_rowsTable[x_r];
  Assert(row_s != NULL);
  Assert(row_s->has(x_s));

  //Swap x_r and x_s in d_activeRows
  d_rowsTable[x_s] = row_s;
  d_rowsTable[x_r] = NULL;

  d_basicVariables.remove(x_r);

  d_basicVariables.add(x_s);

  row_s->pivot(x_s);

  Column copy(getColumn(x_s));
  Column::const_iterator basicIter = copy.begin(), endIter = copy.end();

  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    if(basic == x_s) continue;

    ReducedRowVector& row_k = lookup(basic);
    Assert(row_k.has(x_s));

    row_k.substitute(*row_s);
  }
  Assert(getColumn(x_s).size() == 1);
  Assert(getRowCount(x_s) == 1);
}


void printColumn(const Column& col) {
  Debug("tableau") << "{";
  for(Column::const_iterator colIter = col.begin(), colEnd = col.end(); colIter!=colEnd; ++colIter){
    ArithVar basic = *colIter;
    Debug("tableau") << basic << ", ";
  }
  Debug("tableau") << "}";
}

void Tableau::printTableau(){
  Debug("tableau") << "Tableau::d_activeRows"  << endl;

  typedef RowsTable::iterator table_iter;
  for(table_iter rowIter = d_rowsTable.begin(), end = d_rowsTable.end();
      rowIter != end; ++rowIter){
    ReducedRowVector* row_k = *rowIter;
    if(row_k != NULL){
      row_k->printRow();
    }
  }

  Debug("tableau") << "Tableau::columns begin" << endl;
  typedef ColumnMatrix::iterator col_iter;
  ArithVar i = 0;
  for(col_iter matIter = d_columnMatrix.begin(), endMat = d_columnMatrix.end();
      matIter != endMat; ++matIter, ++i){
    Column& col = *(*matIter);
    Debug("tableau") << "Tableau::column "<< i << ": ";
    printColumn(col);
    Debug("tableau") << endl;
  }
  Debug("tableau") << "Tableau::columns end" << endl;
}


uint32_t Tableau::numNonZeroEntries() const {
  uint32_t colSum = 0;
  ColumnMatrix::const_iterator i = d_columnMatrix.begin(), end = d_columnMatrix.end();
  for(; i != end; ++i){
    const Column& col = *(*i);
    colSum += col.size();
  }
  return colSum;
}

uint32_t Tableau::numNonZeroEntriesByRow() const {
  uint32_t rowSum = 0;
  ArithVarSet::iterator i = d_basicVariables.begin(), end = d_basicVariables.end();
  for(; i != end; ++i){
    ArithVar basic = *i;
    const ReducedRowVector& row = *(d_rowsTable[basic]);
    rowSum += row.size();
  }
  return rowSum;
}

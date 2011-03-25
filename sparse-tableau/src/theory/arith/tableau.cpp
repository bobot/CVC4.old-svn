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

  if(N > 1){
    d_columnMatrix.insert(d_columnMatrix.end(), N, Column());
    d_rowsTable.insert(d_rowsTable.end(), N, NULL);
    d_basicVariables.increaseSize(N-1);

    Assert(d_basicVariables.allocated() == tab.d_basicVariables.allocated());

    d_rowCount.insert(d_rowCount.end(), N, 0);
  }

  ColumnMatrix::const_iterator otherIter = tab.d_columnMatrix.begin();
  ColumnMatrix::iterator i_colIter = d_columnMatrix.begin();
  ColumnMatrix::iterator end_colIter = d_columnMatrix.end();
  for(; i_colIter != end_colIter; ++i_colIter, ++otherIter){
    Assert(otherIter != tab.d_columnMatrix.end());
    Column& col = *i_colIter;
    const Column& otherCol = *otherIter;
    col.increaseSize(otherCol.allocated());
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

  rowPivot(x_r, x_s);

  ColIterator colIter = getColIterator(x_s);
  while(!colIter.atEnd()){
    EntryID id = colIter.getID();
    TableauEntry& entry = d_entryManager.get(id);

    ++colIter;
    if(entry.getRowVar() == x_s){
      continue;
    }
    ArithVar basicTo = entry.getBasic();
    const Rational& coeff = entry.getCoefficient();
    rowPlusRowTimesConstant(coeff, basicTo, x_s);
  }

  Assert(d_basicVariables.isMember(x_r));
  Assert(!d_basicVariables.isMember(x_s));
  Assert(getColLength(x_s) == 1);
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
}

uint32_t Tableau::numNonZeroEntries() const {
  uint32_t colSum = 0;
  ColumnMatrix::const_iterator i = d_columnMatrix.begin(), end = d_columnMatrix.end();
  for(; i != end; ++i){
    const Column& col = *i;
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




/**
 * Changes basic to newbasic (a variable on the row).
 */
void Tableau::rowPivot(ArithVar basic, ArithVar newBasic){
  Assert(mergeBufferIsEmpty());
  Assert(isBasic(basic));
  Assert(!isBasic(newBasic));

  EntryID newBasicID = ENTRYID_SENTINEL;

  for(RowIterator i = beginRow(basic); !i.atEnd(); ++i){
    EntryID id = i.getId();
    TableauEntry& entry = *i;
    ArithVar colVar = entry.getColVar();
    d_mergeBuffer[colVar] = make_pair(id, false);

    if(colVar == newBasic){
      Assert(newBasicID == ENTRYID_SENTINEL);
      newBasicID = id;
    }
  }
  Assert(newBasicID != ENTRYID_SENTINEL);

  TableauEntry& newBasicEntry = d_manager.get(newBasicID);
  Rational negInverseA_rs = -(newBasicEntry.getCoefficient().inverse());

  for(RowIterator i = beginRow(basic); !i.atEnd(); ++i){
    TableauEntry& entry = *i;

    entry.getCoefficient() *= c;
    entry.setBasicVar(newBasic);
  }

  d_rowHeads[newBasic] = d_rowHeads[basic];
  d_rowsHeads[basic] = ENTRYID_SENTINEL;

  d_rowLengths[newBasic] = d_rowLengths[basic];
  d_rowLengths[basic] = 0;

  d_basicManager.remove(basic);
  d_basicManager.add(newBasic);
}

void addEntry(ArithVar row, ArithVar col, const Rational& coeff){
  EntryID newId = d_entryManager.newEntry();
  TableauCoefficient& newEntry =  d_entryManager.get(newId);
  newEntry = TableauEntry( row, col, d_rowHeads[row], d_colHeads[col], coeff);
  Assert(newEntry.getCoefficient() != 0);

  d_rowHeads[row] = newId;
  d_colHeads[col] = newId;
  ++d_rowLengths;
  ++d_colLengths;
}

void removeEntry(EntryID id){
  TableauEntry& entry = d_basicManager.get(id);
  --d_rowLength[entry.getRowVar()];
  --d_colLength[entry.getColVar()];
  entry.markUnused();
}

void Tableau::rowPlusRowTimesConstant(const Rational& c, ArithVar basicTo, ArithVar basicFrom){

  Assert(c != 0);
  Assert(isBasic(basicTo));
  Assert(isBasic(basicFrom));
  Assert( d_usedList.empty() );

  for(RowIterator i = beginRow(basicTo); !i.atEnd(); ++i){
    TableauEntry& entry = *i;
    ArithVar colVar = entry.getColVar();

    if(bufferPairIsNotEmpty(d_mergeBuffer[colVar])){
      d_mergeBuffer[colVar].second = true;
      usedList.push_back(colVar);

      EntryID inOtherRow = d_mergeBuffer[colVar].first;
      const TableauEntry& other = d_entryManager.get(inOtherRow);
      entry.getCoefficient() += c * other.getCoefficient();

      if(entry.getCoefficient().sgn() == 0){
        removeEntry(i.getId());
      }
    }
  }

  for(RowIterator i = beginRow(basicFrom); !i.atEnd(); ++i){
    TableauEntry& entry = *i;
    ArithVar colVar = entry.getColVar();

    if(!(d_mergeBuffer[colVar]).second){
      Rational newCoeff =  c * other.getCoefficient();
      addEntry(basicTo, colVar, newCoeff);
    }
  }

  clearUsedList();
}

void clearUsedList(){
  ArrithVarArray::iterator i, end;
  for(i = d_usedList.begin(), end = d_usedList.end(); i != end; ++i){
    ArithVar pos = *i;
    d_mergeBuffer[pos].second = false;
  }
  d_usedList.clear();
}

void addRow(ArithVar basic,
            const std::vector<ArithVar>& variables,
            const std::vector<Rational>& coefficients)
{
  Assert(coefficients.size() == variables.size() );

  addEntry(basic, basic, Rational(-1));
  d_entries.push_back(VarCoeffPair(basic, Rational(-1)));

  vector<Rational>::const_iterator coeffIter = coefficients.begin();
  vector<Rational>::const_iterator coeffEnd = coefficients.end();
  vector<ArithVar>::const_iterator varIter = variables.begin();

  for(; coeffIter != coeffEnd; ++coeffIter, ++varIter){
    const Rational& coeff = *coeffIter;
    ArithVar var_i = *varIter;
    addEntry(basic, var_i, coeff);
  }

  Assert(noZeroCoefficients(basic);

  Assert(matchingCounts(basic));
  Assert(wellFormed());
  Assert(d_rowCount[d_basic] == 1);
}



ReducedRowVector::~ReducedRowVector(){
  //This executes before the super classes destructor RowVector,
  // which will set this to 0.
  Assert(d_rowCount[basic()] == 1);

  const_iterator curr = begin();
  const_iterator endEntries = end();
  for(;curr != endEntries; ++curr){
    ArithVar v = (*curr).getArithVar();
    Assert(d_rowCount[v] >= 1);
    d_columnMatrix[v].remove(basic());
    --(d_rowCount[v]);
  }

  Assert(matchingCounts());
}

bool ReducedRowVector::noZeroCoefficients(const VarCoeffArray& arr){
  for(const_iterator curr = arr.begin(), endEntries = arr.end();
      curr != endEntries; ++curr){
    const Rational& coeff = (*curr).getCoefficient();
    if(coeff == 0) return false;
  }
  return true;
}

void ReducedRowVector::enqueueNonBasicVariablesAndCoefficients(std::vector< ArithVar >& variables,std::vector< Rational >& coefficients) const{
  for(const_iterator i=begin(), endEntries=end(); i != endEntries; ++i){
    ArithVar var = (*i).getArithVar();
    const Rational& q = (*i).getCoefficient();
    if(var != basic()){
      variables.push_back(var);
      coefficients.push_back(q);
    }
  }
}

Node ReducedRowVector::asEquality(const ArithVarToNodeMap& map) const{
  using namespace CVC4::kind;

  Assert(size() >= 2);

  vector<Node> nonBasicPairs;
  for(const_iterator i = begin(); i != end(); ++i){
    ArithVar nb = (*i).getArithVar();
    if(nb == basic()) continue;
    Node var = (map.find(nb))->second;
    Node coeff = mkRationalNode((*i).getCoefficient());

    Node mult = NodeBuilder<2>(MULT) << coeff << var;
    nonBasicPairs.push_back(mult);
  }

  Node sum = Node::null();
  if(nonBasicPairs.size() == 1 ){
    sum = nonBasicPairs.front();
  }else{
    Assert(nonBasicPairs.size() >= 2);
    NodeBuilder<> sumBuilder(PLUS);
    sumBuilder.append(nonBasicPairs);
    sum = sumBuilder;
  }
  Node basicVar = (map.find(basic()))->second;
  return NodeBuilder<2>(EQUAL) << basicVar << sum;
}

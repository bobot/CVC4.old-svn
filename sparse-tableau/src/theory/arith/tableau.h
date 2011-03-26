/*********************                                                        */
/*! \file tableau.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
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


#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_set.h"
#include "theory/arith/normal_form.h"

#include "theory/arith/row_vector.h"

#include <queue>
#include <vector>
#include <utility>

#ifndef __CVC4__THEORY__ARITH__TABLEAU_H
#define __CVC4__THEORY__ARITH__TABLEAU_H

namespace CVC4 {
namespace theory {
namespace arith {

typedef uint32_t EntryID;
#define ENTRYID_SENTINEL std::numeric_limits<ArithVar>::max()

class TableauEntry {
private:
  ArithVar d_rowVar;
  ArithVar d_colVar;

  EntryID d_nextRow;
  EntryID d_nextCol;

  Rational d_coefficient;

public:
  TableauEntry():
    d_rowVar(ARITHVAR_SENTINEL),
    d_colVar(ARITHVAR_SENTINEL),
    d_nextRow(ENTRYID_SENTINEL),
    d_nextCol(ENTRYID_SENTINEL),
    d_coefficient(0)
  {}

  TableauEntry(ArithVar row, ArithVar col,
               EntryID nextRowEntry, EntryID nextColEntry,
               const Rational& coeff):
    d_rowVar(row),
    d_colVar(col),
    d_nextRow(nextRowEntry),
    d_nextCol(nextColEntry),
    d_coefficient(coeff)
  {}

private:
  bool unusedConsistent() const {
    return (d_rowVar == ARITHVAR_SENTINEL && d_colVar == ARITHVAR_SENTINEL) ||
      (d_rowVar != ARITHVAR_SENTINEL && d_colVar != ARITHVAR_SENTINEL);
  }

public:

  EntryID getNextRowID() const {
    return d_nextRow;
  }

  EntryID getNextColID() const {
    return d_nextRow;
  }

  EntryID& getNextRowIDRef() {
    return d_nextRow;
  }

  EntryID& getNextColIDRef() {
    return d_nextRow;
  }

  void setRowVar(ArithVar newRowVar){
    d_rowVar = newRowVar;
  }

  ArithVar getRowVar() const{
    return d_rowVar;
  }
  ArithVar getColVar() const{
    return d_colVar;
  }

  const Rational& getCoefficient() const {
    return d_coefficient;
  }

  Rational& getCoefficient(){
    return d_coefficient;
  }

  bool isUnused() const{
    Assert(unusedConsistent());

    return d_rowVar == ARITHVAR_SENTINEL;
  }

  void markUnused (){
    Assert(!isUnused());

    d_rowVar = ARITHVAR_SENTINEL;
    d_colVar = ARITHVAR_SENTINEL;
    Assert(isUnused());
  }

  EntryID unlinkFromRow(){
    Assert(isUnused());
    EntryID currNextRow = d_nextRow;
    d_nextRow = ENTRYID_SENTINEL;
    return currNextRow;
  }

  EntryID unlinkFromCol(){
    Assert(isUnused());
    EntryID currNextCol = d_nextCol;
    d_nextCol = ENTRYID_SENTINEL;
    return currNextCol;
  }

  bool isUnusedAndUnlinked() const{
    return isUnused() && d_nextRow == ENTRYID_SENTINEL && d_nextCol == ENTRYID_SENTINEL;
  }
};

class TableauEntryManager {
private:
  typedef std::vector<TableauEntry> EntryArray;

  EntryArray d_entries;
  std::queue<EntryID> d_freedEntries;

  uint32_t d_size;

public:
  TableauEntryManager():
    d_entries(), d_freedEntries(), d_size(0)
  {}

  const TableauEntry& get(EntryID id) const{
    Assert(inBounds(id));
    return d_entries[id];
  }

  TableauEntry& get(EntryID id){
    Assert(inBounds(id));
    return d_entries[id];
  }

  void freeEntry(EntryID id){
    Assert(get(id).isUnusedAndUnlinked());
    Assert(d_size > 0);

    d_freedEntries.push(id);
    --d_size;
  }

  EntryID newEntry(){
    EntryID newId;
    if(d_freedEntries.empty()){
      newId = d_entries.size();
      d_entries.push_back(TableauEntry());
    }else{
      newId = d_freedEntries.front();
      d_freedEntries.pop();
    }
    ++d_size;
    return newId;
  }

  uint32_t size() const{ return d_size; }
private:
  bool inBounds(EntryID id) const{
    return id < size();
  }
};

class Tableau {
private:

  // VectorHeadTable : ArithVar |-> EntryID of the head of the vector
  typedef std::vector<EntryID> VectorHeadTable;
  VectorHeadTable d_rowHeads;
  VectorHeadTable d_colHeads;

  // VectorSizeTable : ArithVar |-> length of the vector
  typedef std::vector<uint32_t> VectorSizeTable;
  VectorSizeTable d_colLengths;
  VectorSizeTable d_rowLengths;

  // Set of all of the basic variables in the tableau.
  ArithVarSet d_basicVariables;

  typedef std::pair<EntryID, bool> PosUsedPair;
  typedef std::vector<PosUsedPair> PosUsedPairArray;
  PosUsedPairArray d_mergeBuffer;

  typedef std::vector<ArithVar> ArithVarArray;
  ArithVarArray d_usedList;

  TableauEntryManager d_entryManager;

public:
  /**
   * Constructs an empty tableau.
   */
  Tableau() {}
  ~Tableau();

private:
  void addEntry(ArithVar row, ArithVar col, const Rational& coeff);
  void removeEntry(EntryID id);

  template <bool isRowIterator>
  class Iterator {
  private:
    EntryID d_curr;
    TableauEntryManager& d_entryManager;

  public:
    Iterator(ArithVar basic, VectorHeadTable& table, TableauEntryManager& manager) :
      d_entryManager(manager)
    {
      EntryID& head = table[basic];
      updateNext(head);
      d_curr = head;
    }

    /**
     * Updates both d_curr and start to point to the next entry in the list the is valid.
     * If this is the end of the list
     */
    void updateNext(EntryID& start){
      while(start != ENTRYID_SENTINEL){
        TableauEntry& nextEntry = d_entryManager.get(start);
        if(nextEntry.isUnused()){
          EntryID tmp = isRowIterator ?
            nextEntry.unlinkFromRow() :
            nextEntry.unlinkFromCol();

          if(nextEntry.isUnusedAndUnlinked()){
            d_entryManager.freeEntry(start);
          }
          start = tmp;
        }else{
          break;
        }
      }
    }

  public:

    EntryID getID() const {
      return d_curr;
    }

    const TableauEntry& operator*() const{
      Assert(!atEnd());
      return d_entryManager.get(d_curr);
    }

    Iterator& operator++(){
      Assert(!atEnd());
      TableauEntry& entry = d_entryManager.get(d_curr);
      EntryID& nextRef = isRowIterator ?
        entry.getNextRowIDRef() :
        entry.getNextColIDRef();
      updateNext(nextRef);
      d_curr = nextRef;
      return *this;
    }

    bool atEnd() const {
      return d_curr == ENTRYID_SENTINEL;
    }
  };

public:
  typedef Iterator<true> RowIterator;
  typedef Iterator<false> ColIterator;

  size_t getNumRows() const {
    return d_basicVariables.size();
  }

  void increaseSize(){
    d_basicVariables.increaseSize();

    d_rowHeads.push_back(ENTRYID_SENTINEL);
    d_colHeads.push_back(ENTRYID_SENTINEL);

    d_colLengths.push_back(0);
    d_rowLengths.push_back(0);

    d_mergeBuffer.push_back(std::make_pair(ENTRYID_SENTINEL, false));
  }

  bool isBasic(ArithVar v) const {
    return d_basicVariables.isMember(v);
  }

  ArithVarSet::const_iterator beginBasic() const{
    return d_basicVariables.begin();
  }

  ArithVarSet::const_iterator endBasic() const{
    return d_basicVariables.end();
  }

  RowIterator rowIterator(ArithVar v){
    Assert(v < d_rowHeads.size());
    return RowIterator(v, d_rowHeads, d_entryManager);
  }

  ColIterator colIterator(ArithVar v){
    Assert(v < d_colHeads.size());
    return ColIterator(v, d_colHeads, d_entryManager);
  }


  uint32_t getRowLength(ArithVar x) const{
    Assert(x < d_rowLengths.size());
    return d_rowLengths[x];
  }

  uint32_t getColLength(ArithVar x) const{
    Assert(x < d_colLengths.size());
    return d_colLengths[x];
  }

  /**
   * Adds a row to the tableau.
   * The new row is equivalent to:
   *   basicVar = \sum_i coeffs[i] * variables[i]
   * preconditions:
   *   basicVar is already declared to be basic
   *   basicVar does not have a row associated with it in the tableau.
   *
   * Note: each variables[i] does not have to be non-basic.
   * Pivoting will be mimicked if it is basic.
   */
  void addRow(ArithVar basicVar,
              const std::vector<Rational>& coeffs,
              const std::vector<ArithVar>& variables);

  /**
   * preconditions:
   *   x_r is basic,
   *   x_s is non-basic, and
   *   a_rs != 0.
   */
  void pivot(ArithVar basicOld, ArithVar basicNew);
private:
  void rowPivot(ArithVar basicOld, ArithVar basicNew);
  /** Requires merge buffer to be loaded with basicFrom and used to be empty. */
  void rowPlusRowTimesConstant(ArithVar basicTo, const Rational& coeff, ArithVar basicFrom);

  EntryID findOnRow(ArithVar basic, ArithVar find);
public:

  /**
   * Prints the contents of the Tableau to Debug("tableau::print")
   */
  void printTableau();
  void printRow(ArithVar basic);
  void printEntry(const TableauEntry& entry);


private:
  void loadRowIntoMergeBuffer(ArithVar basic);
  void emptyRowFromMergeBuffer(ArithVar basic);
  void clearUsedList();

  static bool bufferPairIsNotEmpty(const PosUsedPair& p){
    return !(p.first == ENTRYID_SENTINEL && p.second == false);
  }

  static bool bufferPairIsEmpty(const PosUsedPair& p){
    return (p.first == ENTRYID_SENTINEL && p.second == false);
  }
  bool mergeBufferIsEmpty() const {
    return d_mergeBuffer.end() == std::find_if(d_mergeBuffer.begin(),
                                               d_mergeBuffer.end(),
                                               bufferPairIsNotEmpty);
  }

  void setColumnUnused(ArithVar v);

  uint32_t getNumNonZeroEntries() const {
    return d_entryManager.size();
  }

  Node rowAsEquality(ArithVar basic, const ArithVarToNodeMap& map);
private:
  uint32_t numNonZeroEntries() const;
  uint32_t numNonZeroEntriesByRow() const;
  uint32_t numNonZeroEntriesByCol() const;


  bool debugNoZeroCoefficients(ArithVar basic);
  bool debugMatchingCountsForRow(ArithVar basic);
  uint32_t debugCountColLength(ArithVar var);
  uint32_t debugCountRowLength(ArithVar var);

};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */

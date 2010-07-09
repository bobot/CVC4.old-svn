
#include "expr/node.h"
#include "util/rational.h"
#include "theory/arith/basic.h"
#include <ext/hash_map>

#include <list>

#ifndef __CVC4__THEORY__ARITH__TABLEAU_H
#define __CVC4__THEORY__ARITH__TABLEAU_H

namespace CVC4 {
namespace theory {
namespace arith {

class TableauCell;
typedef std::list< TableauCell* > CellList;

class Tableau;

class Row {
 private:

  size_t id;

  CellList cells;


  /**
   * The basic variable for a row is not stored as a cell.
   * This is to make iteration over the rows more straight forward.
   */
  TNode basic;

 public:
  Row(TNode b){
    static size_t id_dist = 0;
    id = id_dist++;
    setBasic(b);
  }

  size_t getId() const{ return id; }

  void setBasic(TNode b){
    Assert(isBasic(b));
    basic = b;
  }

  TNode getBasic() const{
    return basic;
  }

  void erase(CellList::iterator i){
    cells.erase(i);
  }

  size_t size() const{
    return cells.size();
  }

  CellList::iterator insert(TableauCell* cell){
    return cells.insert(cells.end(), cell);
  }

  CellList::iterator begin(){
    return cells.begin();
  }
  CellList::iterator end(){
    return cells.end();
  }

  CellList::const_iterator begin() const{
    return cells.begin();
  }
  CellList::const_iterator end() const{
    return cells.end();
  }
  Node asEquality() const;

};

class Column {
private:
  size_t id;

  TNode var;
  CellList appearances; /* This must be empty for basic variables. */

public:
  Column(TNode x): var(x) {
    static size_t id_dist = 0;
    id = id_dist++;
  }

  TNode getVariable(){
    return var;
  }

  size_t size(){
    return appearances.size();
  }
  size_t getId(){ return id; }
  CellList::iterator begin(){
    return appearances.begin();
  }
  CellList::iterator end(){
    return appearances.end();
  }
  CellList::iterator insert(TableauCell* cell){
    return appearances.insert(appearances.end(), cell);
  }
  void erase(CellList::iterator i){
    appearances.erase(i);
  }
};


class TableauCell {
 private:
  Rational coefficient;
  Row* d_row;
  Column* d_col;

  CellList::iterator d_rowPos;
  CellList::iterator d_colPos;

  friend class Tableau;

 public:
  TableauCell(Row* r, Column* c, const Rational& q):
    coefficient(q), d_row(r), d_col(c){
    d_rowPos = d_row->insert(this);
    d_colPos = d_col->insert(this);
  }

  Rational& getCoefficient(){
    return coefficient;
  }

  Row* getRow(){
    return d_row;
  }
  Column* getColumn(){
    return d_col;
  }
};

// for hash_maps, hash_sets..
struct RowColumnHash {
  size_t operator()( std::pair<Row*, Column*> p) const {
     __gnu_cxx::hash<size_t> H;
    Row* r = p.first;
    Column* c = p.second;
    return H(r->getId() xor H(c->getId()));

  }
};
typedef __gnu_cxx::hash_map< std::pair<Row*,Column*>, TableauCell*, RowColumnHash> CellMap;
typedef __gnu_cxx::hash_map< TNode, Row*, NodeHashFunction> RowMap;
typedef __gnu_cxx::hash_map< TNode, Column*, NodeHashFunction> ColumnMap;

class Tableau {
private:
  CellMap cellMap;
  RowMap rowMap;
  ColumnMap colMap;

  void removeCell(TableauCell* cell);

  void addNonbasicsInRow(Row* dest, Row* src, const Rational& coeff);

  void multRow(Row* dest, const Rational& q);


  void removeRow(Row* r);

public:
  Tableau() {}

  void initializeVariable(TNode x);

  bool hasCell(Row* r, Column* c);
  bool hasCell(Row* r, Column* c, TableauCell*& cell);

  bool hasRow(TNode basic);
  bool hasRow(TNode basic, Row* & r);

  bool hasColumn(TNode variable);
  bool hasColumn(TNode basic, Column* & c);

  TableauCell* lookupCell(Row* r, Column* c);
  Row* lookupRow(TNode basic);
  Column* lookupColumn(TNode variable);

  void insertRow(TNode eq);

  void pivot(Row* r, Column* c);

  void printTableau(){}

  RowMap::iterator rowBegin(){
    return rowMap.begin();
  }
  RowMap::iterator rowEnd(){
    return rowMap.end();
  }

  bool isEjected(TNode var);

  void ejectBasic(TNode basic);
  void reinjectBasic(TNode basic);

  size_t rowSize(TNode basic){
    Row* r = lookupRow(basic);
    return r->size();
  }
};


}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */

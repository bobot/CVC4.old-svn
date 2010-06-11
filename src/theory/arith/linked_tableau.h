
#include "expr/node.h"
#include "util/rational.h"
#include <ext/hash_map>

#include <list>

using namespace CVC4;

class TableauCell;
typedef std::list< TableauCell* > CellList;

class Tableau;

class Row {
 private:

  size_t id;

  CellList cells;

  TNode basic;
  CellList::iterator basicPos;

  friend class TableauCell;
  friend class Tableau;

 public:
  Row(){
    static size_t id_dist = 0;
    id = id_dist++;
  }

  size_t getId(){ return id; }

  void setBasic(TNode b, TableauCell* cell);

  CellList::iterator begin(){
    return cells.begin();
  }
  CellList::iterator end(){
    return cells.end();
  }
};

class Column {
private:
  size_t id;

  TNode var;
  CellList appearances;

  friend class TableauCell;
  friend class Tableau;
 
public:
  Column(TNode x): var(x) {
    static size_t id_dist = 0;
    id = id_dist++;
  }

  size_t getId(){ return id; }
  CellList::iterator begin(){
    return appearances.begin();
  }
  CellList::iterator end(){
    return appearances.end();
  }
};


class TableauCell {
 private:
  Rational coefficient;
  Row* d_row;
  Column* d_col;

  CellList::iterator d_rowPos;
  CellList::iterator d_colPos;

  friend class Row;
  friend class Tableau;

 public:
  TableauCell(Row* r, Column* c, const Rational& q):
    coefficient(q), d_row(r), d_col(c){
    d_rowPos = d_row->cells.insert(d_row->begin(), this);
    d_colPos = d_col->appearances.insert(d_col->begin(), this);
  }
};

// for hash_maps, hash_sets..
struct RowColumnHash {
  size_t operator()( pair<Row*, Column*> p) const {
     __gnu_cxx::hash<size_t> H;
    Row* r = p.first;
    Column* c = p.second;
    return H(r->getId() xor H(c->getId()));

  }
};
typedef __gnu_cxx::hash_map< pair<Row*,Column*>, TableauCell*, RowColumnHash> CellMap;
typedef __gnu_cxx::hash_map< TNode, Row*, NodeHashFunction> RowMap;
typedef __gnu_cxx::hash_map< TNode, Column*, NodeHashFunction> ColumnMap;

class Tableau {
private:
  CellMap cellMap;
  RowMap rowMap;
  ColumnMap colMap;

  void removeCell(TableauCell* cell);

  void addRows(Row* dest, Row* src, const Rational& coeff);

  void multRow(Row* dest, const Rational& q);



public:
  Tableau();

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

};

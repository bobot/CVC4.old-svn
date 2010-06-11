#include "theory/arith/linked_tableau.h"
#include "theory/arith/basic.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

void Row::setBasic(TNode b, TableauCell* cell){
  basic = b;
  basicPos = cell->d_rowPos;
}

void Tableau::insertRow(TNode eq){
    Assert(eq.getKind() == kind::EQUAL);
    Assert(eq.getNumChildren() == 2);

    TNode var = eq[0];
    TNode sum = eq[1];

    Assert(var.getAttribute(IsBasic()));

    Row* row_var = new Row();
    Column* c = new Column(var);

    TableauCell* cell_var = new TableauCell(row_var, c, -1);
    cellMap.insert(make_pair(make_pair(row_var, c), cell_var));

    row_var->setBasic(var, cell_var);

    for(TNode::iterator iter=sum.begin(); iter != sum.end(); ++iter){
      TNode pair = *iter;
      Assert(pair.getKind() == MULT);
      Assert(pair.getNumChildren() == 2);
      Assert(pair[0].getKind() == CONST_RATIONAL);
      const Rational& coeff = pair[0].getConst<Rational>();
      TNode var_i = pair[1];

      if(isBasic(var_i)){
        Row* nbRow = lookupRow(var_i);
        addRows(row_var, nbRow, coeff);
      }else{
        Column* col;
        if(!hasColumn(var_i, col)){
          col = new Column(var_i);
          colMap.insert(make_pair(var_i, col));
        }
        TableauCell* newCell = new TableauCell(row_var, col, coeff);
        cellMap.insert(make_pair(make_pair(row_var,col), newCell));
      }
    }
  }

void Tableau::pivot(Row* r, Column* c){
  TableauCell* basicCell= *(r->basicPos);
  TableauCell* nbCell = lookupCell(r,c);

  TNode oldBasic = r->basic;
  rowMap.erase(oldBasic);

  makeBasic(oldBasic);
  makeNonbasic(c->var);

  r->setBasic(c->var,nbCell);

  rowMap.insert(make_pair(c->var, r));

  Rational q = -(nbCell->coefficient.inverse());
  multRow(r, q);

  for(CellList::iterator rowIter = c->appearances.begin();
      rowIter != c->appearances.end();
      ++rowIter){
    TableauCell* cell = *rowIter;
    if(r != cell->d_row){
      Rational copy = cell->coefficient;
      addRows(cell->d_row, r, copy);
    }
  }
}

void Tableau::removeCell(TableauCell* cell){
  cellMap.erase(make_pair(cell->d_row,cell->d_col));
  cell->d_row->cells.erase(cell->d_rowPos);
  cell->d_col->appearances.erase(cell->d_colPos);
  delete cell;
}

void Tableau::addRows(Row* dest, Row* src, const Rational& coeff){
  for(CellList::iterator i=src->begin(); i != src->end(); ++i){
    TableauCell* cell= *i;
    Column* c = cell->d_col;
    TableauCell* target;
    if(hasCell(dest,c, target)){
      target->coefficient += cell->coefficient * coeff;
      if(target->coefficient == 0){
        removeCell(target);
      }
    }else{
      target = new TableauCell(dest, c, cell->coefficient * coeff);
      cellMap.insert(make_pair(make_pair(dest,c), target));
    }
  }
}

void Tableau::multRow(Row* dest, const Rational& q){
  for(CellList::iterator i=dest->begin(); i != dest->end(); ++i){
    TableauCell* cell= *i;
    cell->coefficient *= q;
  }
}

bool Tableau::hasRow(TNode basic){
  return rowMap.find(basic) != rowMap.end();
}

bool Tableau::hasColumn(TNode variable){
  return colMap.find(variable) != colMap.end();
}

bool Tableau::hasRow(TNode basic, Row* & r){
  RowMap::iterator i = rowMap.find(basic);
  bool res = (i != rowMap.end());
  r = res ? i->second : NULL;
  return res;
}

bool Tableau::hasColumn(TNode variable, Column* & c){
  ColumnMap::iterator i = colMap.find(variable);
  bool res = (i != colMap.end());
  c = res ? (i->second) : NULL;
  return res;
}

Row* Tableau::lookupRow(TNode basic){
  RowMap::iterator i = rowMap.find(basic);
  Assert( i != rowMap.end());
  return (i->second);

}
Column* Tableau::lookupColumn(TNode variable){
  ColumnMap::iterator i = colMap.find(variable);
  Assert( i != colMap.end());
  return (i->second);
}

TableauCell* Tableau::lookupCell(Row* r, Column* c){
  CellMap::iterator i = cellMap.find(make_pair(r,c));
  Assert(i != cellMap.end());
  return (i->second);
}

bool Tableau::hasCell(Row* r, Column* c){
  return cellMap.find(make_pair(r,c)) != cellMap.end();
}
bool Tableau::hasCell(Row* r, Column* c, TableauCell*& cell){
  CellMap::iterator i = cellMap.find(make_pair(r,c));
  bool res = (i != cellMap.end());
  cell = res ? (i->second) : NULL;
  return res;
}

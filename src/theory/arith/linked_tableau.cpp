#include "theory/arith/linked_tableau.h"
#include "theory/arith/basic.h"
#include "expr/kind.h"



using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
using namespace CVC4::kind;

struct EjectedID;
typedef expr::Attribute<EjectedID, Node> Ejected;

Node Row::asEquality() const{
  NodeBuilder<> nb(PLUS);
  for(CellList::const_iterator nbIter = begin(); nbIter != end(); ++nbIter){
    TableauCell* nonBasic = *nbIter;
    TNode var = nonBasic->getColumn()->getVariable();
    const Rational& qCoeff = nonBasic->getCoefficient();
    Node coeff = NodeManager::currentNM()->mkConst<Rational>(qCoeff);
    Node mult  = NodeManager::currentNM()->mkNode(MULT, coeff, var);
    nb << mult;
  }

  Assert(nb.getNumChildren() > 1);
  return NodeManager::currentNM()->mkNode(EQUAL, getBasic(), Node(nb));
}

void Tableau::initializeVariable(TNode x){
  Assert(!hasColumn(x));

  Column* col = new Column(x);
  colMap.insert(std::make_pair(x,col));
}


void Tableau::repivotFixpoint(TNode basic, std::vector<Node>& reinjected){

  Node asEq = basic.getAttribute(Ejected());

  TNode sum = asEq[1];

  reinjected.push_back(basic);
  reinjectBasic(basic);

  Row* basicRow = lookupRow(basic);

  for(TNode::iterator iter=sum.begin(); iter != sum.end(); ++iter){
    TNode pair = *iter;
    Assert(pair.getKind() == MULT);
    Assert(pair.getNumChildren() == 2);
    Assert(pair[0].getKind() == CONST_RATIONAL);
    const Rational& coeff = pair[0].getConst<Rational>();
    TNode var_i = pair[1];

    if(isBasic(var_i)){
      if(isEjected(var_i)){
        repivotFixpoint(var_i, reinjected);
      }
      Row* nbRow = lookupRow(var_i);
      addNonbasicsInRow(basicRow, nbRow, coeff);
    }
  }
}

void Tableau::insertRow(TNode eq){
  Assert(eq.getKind() == kind::EQUAL);
  Assert(eq.getNumChildren() == 2);

  TNode var = eq[0];
  TNode sum = eq[1];

  Assert(var.getAttribute(IsBasic()));

  Row* row_var = new Row(var);
  //Column* col_var = new Column(var);

  rowMap.insert(std::make_pair(var,row_var));
  //  colMap.insert(make_pair(var,col_var));

  std::vector<Node> reinjected;

  for(TNode::iterator iter=sum.begin(); iter != sum.end(); ++iter){
    TNode pair = *iter;
    Assert(pair.getKind() == MULT);
    Assert(pair.getNumChildren() == 2);
    Assert(pair[0].getKind() == CONST_RATIONAL);
    const Rational& coeff = pair[0].getConst<Rational>();
    TNode var_i = pair[1];

    if(isBasic(var_i)){
      if(isEjected(var_i))
        repivotFixpoint(var_i, reinjected);
      Row* nbRow = lookupRow(var_i);
      addNonbasicsInRow(row_var, nbRow, coeff);
    }else{
      Column* col = lookupColumn(var_i);
      TableauCell* newCell = new TableauCell(row_var, col, coeff);
      cellMap.insert(std::make_pair(std::make_pair(row_var,col), newCell));
    }
  }

  for(std::vector<Node>::iterator reinIter = reinjected.begin(); reinIter != reinjected.end(); ++reinIter){
    Node ejectBasiced = *reinIter;
    ejectBasic(ejectBasiced);
  }
}

void Tableau::pivot(Row* r, Column* c){
  TableauCell* nbCell = lookupCell(r,c);

  TNode oldBasic = r->getBasic();
  rowMap.erase(oldBasic);

  makeNonbasic(oldBasic);
  makeBasic(c->getVariable());

  r->setBasic(c->getVariable());

  rowMap.insert(std::make_pair(r->getBasic(), r));

  Column* oldBasicCol = lookupColumn(oldBasic);
  TableauCell* oldBasicCell = new TableauCell(r, oldBasicCol, -1);
  cellMap.insert(std::make_pair(std::make_pair(r,oldBasicCol), oldBasicCell));


  Rational q = -(nbCell->coefficient.inverse());
  removeCell(nbCell);

  multRow(r, q);

  for(CellList::iterator rowIter = c->begin(), next; rowIter != c->end(); ){
    TableauCell* cell = *rowIter;
    Row* dest = cell->getRow();
    Rational copy(cell->coefficient);

    ++rowIter; //This is order dependent

    removeCell(cell);
    addNonbasicsInRow(dest, r, copy);
  }
}

void Tableau::removeCell(TableauCell* cell){
  cellMap.erase(std::make_pair(cell->getRow(),cell->getColumn()));
  cell->d_row->erase(cell->d_rowPos);
  cell->d_col->erase(cell->d_colPos);
  delete cell;
}

void Tableau::addNonbasicsInRow(Row* dest, Row* src, const Rational& coeff){
  for(CellList::iterator i=src->begin(); i != src->end();){
    TableauCell* cell= *i;
    ++i; // i must be incremented before a removeCell call
    Column* c = cell->d_col;
    TableauCell* target;
    if(hasCell(dest,c, target)){
      target->coefficient += cell->coefficient * coeff;
      if(target->coefficient == 0){
        removeCell(target);
      }
    }else{
      target = new TableauCell(dest, c, cell->coefficient * coeff);
      cellMap.insert(std::make_pair(std::make_pair(dest,c), target));
    }
  }
}

void Tableau::multRow(Row* dest, const Rational& q){
  Assert(q != 0);
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
  CellMap::iterator i = cellMap.find(std::make_pair(r,c));
  Assert(i != cellMap.end());
  return (i->second);
}

bool Tableau::hasCell(Row* r, Column* c){
  return cellMap.find(std::make_pair(r,c)) != cellMap.end();
}
bool Tableau::hasCell(Row* r, Column* c, TableauCell*& cell){
  CellMap::iterator i = cellMap.find(std::make_pair(r,c));
  bool res = (i != cellMap.end());
  cell = res ? (i->second) : NULL;
  return res;
}


bool Tableau::isEjected(TNode var){
  if(var.hasAttribute(Ejected())){
    return Node::null() != var.getAttribute(Ejected());
  }
  return false;
}

void Tableau::ejectBasic(TNode basic){
  Assert(isBasic(basic));
  Assert(!isEjected(basic));

  Row* row = lookupRow(basic);

  Assert(row->size() > 1);

  Node asEq = row->asEquality();

  removeRow(row);
  basic.setAttribute(Ejected(), asEq);
}

void Tableau::reinjectBasic(TNode basic){
  Assert(isBasic(basic));
  Assert(isEjected(basic));

  Node asEq = basic.getAttribute(Ejected());
  basic.setAttribute(Ejected(), Node::null() );
  insertRow(asEq);
}

void Tableau::removeRow(Row* r){
  TNode basic = r->getBasic();

  for(CellList::iterator nbIter = r->begin(); nbIter != r->end(); ){
    TableauCell* nbCell = *nbIter;
    ++nbIter;
    removeCell(nbCell);
  }

  rowMap.erase(basic);
  delete r;
}

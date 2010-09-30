/*********************                                                        */
/*! \file tableau.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters
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
#include "theory/arith/arith_activity.h"
#include "theory/arith/basic.h"
#include "theory/arith/normal_form.h"

#include <ext/hash_map>
#include <map>
#include <set>

#ifndef __CVC4__THEORY__ARITH__TABLEAU_H
#define __CVC4__THEORY__ARITH__TABLEAU_H

namespace CVC4 {
namespace theory {
namespace arith {


class Row {
  ArithVar d_x_i;

  typedef std::map<ArithVar, Rational, std::greater<ArithVar> > CoefficientTable;

  CoefficientTable d_coeffs;

public:

  typedef CoefficientTable::iterator iterator;

  /**
   * Construct a row equal to:
   *   basic = \sum_{x_i} c_i * x_i
   */
  Row(ArithVar basic,
      const std::vector< Rational >& coefficients,
      const std::vector< ArithVar >& variables);


  iterator begin(){
    return d_coeffs.begin();
  }

  iterator end(){
    return d_coeffs.end();
  }

  ArithVar basicVar(){
    return d_x_i;
  }

  bool has(ArithVar x_j){
    CoefficientTable::iterator x_jPos = d_coeffs.find(x_j);
    return x_jPos != d_coeffs.end();
  }

  const Rational& lookup(ArithVar x_j){
    CoefficientTable::iterator x_jPos = d_coeffs.find(x_j);
    Assert(x_jPos !=  d_coeffs.end());
    return (*x_jPos).second;
  }

  void pivot(ArithVar x_j);

  void subsitute(Row& row_s);

  void printRow();
};

class Tableau {
public:
  typedef std::set<ArithVar> VarSet;

private:
  typedef __gnu_cxx::hash_map<ArithVar, Row*> RowsTable;

  VarSet d_activeBasicVars;
  RowsTable d_activeRows, d_inactiveRows;

  ActivityMonitor& d_activityMonitor;
  IsBasicManager& d_basicManager;


public:
  /**
   * Constructs an empty tableau.
   */
  Tableau(ActivityMonitor &am, IsBasicManager& bm) :
    d_activeBasicVars(),
    d_activeRows(),
    d_inactiveRows(),
    d_activityMonitor(am),
    d_basicManager(bm)
  {}

  VarSet::iterator begin(){
    return d_activeBasicVars.begin();
  }

  VarSet::iterator end(){
    return d_activeBasicVars.end();
  }

  Row* lookup(ArithVar var){
    Assert(isActiveBasicVariable(var));
    return d_activeRows[var];
  }

private:
  Row* lookupEjected(ArithVar var){
    Assert(isEjected(var));
    return d_inactiveRows[var];
  }
public:

  void addRow(ArithVar basicVar, const std::vector<Rational>& coeffs, const std::vector<ArithVar>& variables);

  /**
   * preconditions:
   *   x_r is basic,
   *   x_s is non-basic, and
   *   a_rs != 0.
   */
  void pivot(ArithVar x_r, ArithVar x_s);

  void printTableau();

  bool isEjected(ArithVar var){
    return d_inactiveRows.find(var) != d_inactiveRows.end();
  }

  void ejectBasic(ArithVar basic){
    Assert(d_basicManager.isBasic(basic));
    Assert(isActiveBasicVariable(basic));

    Row* row = lookup(basic);
    d_activeRows.erase(basic);
    d_activeBasicVars.erase(basic);

    d_inactiveRows.insert(std::make_pair(basic, row));
  }

  void reinjectBasic(ArithVar basic){
    Assert(d_basicManager.isBasic(basic));
    Assert(isEjected(basic));

    Row* row = lookupEjected(basic);

    d_inactiveRows.erase(basic);
    d_activeBasicVars.insert(basic);
    d_activeRows.insert(std::make_pair(basic, row));

    updateRow(row);
  }
private:
  inline bool isActiveBasicVariable(ArithVar var){
    return d_activeBasicVars.find(var) != d_activeBasicVars.end();
  }

  void updateRow(Row* row);
};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */

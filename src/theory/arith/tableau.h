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
#include "theory/arith/arithvar_dense_set.h"
#include "theory/arith/simplex.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/partial_model.h"

#include "theory/arith/row_vector.h"

#include <ext/hash_map>
#include <set>

#ifndef __CVC4__THEORY__ARITH__TABLEAU_H
#define __CVC4__THEORY__ARITH__TABLEAU_H

namespace CVC4 {
namespace theory {
namespace arith {

class ArithVarSet {
private:
  typedef std::list<ArithVar> VarList;

public:
  typedef VarList::const_iterator iterator;

private:
  VarList d_list;
  std::vector< VarList::iterator > d_posVector;

public:
  ArithVarSet() : d_list(),  d_posVector() {}

  iterator begin() const{ return d_list.begin(); }
  iterator end() const{ return d_list.end(); }

  void insert(ArithVar av){
    Assert(inRange(av) );
    Assert(!inSet(av) );

    d_posVector[av] = d_list.insert(d_list.end(), av);
  }

  void erase(ArithVar var){
    Assert( inRange(var) );
    Assert( inSet(var) );

    d_list.erase(d_posVector[var]);
    d_posVector[var] = d_list.end();
  }

  void increaseSize(){
    d_posVector.push_back(d_list.end());
  }

  bool inSet(ArithVar v) const{
    Assert(inRange(v) );

    return d_posVector[v] != d_list.end();
  }

private:
  bool inRange(ArithVar v) const{
    return v < d_posVector.size();
  }
};

class Tableau {
private:

  typedef std::vector< ReducedRowVector* > RowsTable;

  ArithVarSet d_activeBasicVars;
  RowsTable d_rowsTable;


  ActivityMonitor& d_activityMonitor;
  ArithVarDenseSet& d_basicManager;

  ArithPartialModel& d_pm;

  std::vector<uint32_t> d_rowCount;

public:
  /**
   * Constructs an empty tableau.
   */
  Tableau(ActivityMonitor &am, ArithVarDenseSet& bm, ArithPartialModel& pm);

  void increaseSize(){
    d_activeBasicVars.increaseSize();
    d_rowsTable.push_back(NULL);
    d_rowCount.push_back(0);
  }

  ArithVarSet::iterator begin(){
    return d_activeBasicVars.begin();
  }

  ArithVarSet::iterator end(){
    return d_activeBasicVars.end();
  }

  ReducedRowVector* lookup(ArithVar var){
    Assert(isActiveBasicVariable(var));
    return d_rowsTable[var];
  }

private:
  ReducedRowVector* lookupEjected(ArithVar var){
    Assert(isEjected(var));
    return d_rowsTable[var];
  }
public:

  uint32_t getRowCount(ArithVar x){
    Assert(x < d_rowCount.size());
    return d_rowCount[x];
  }

  void addRow(ArithVar basicVar,
              const std::vector<Rational>& coeffs,
              const std::vector<ArithVar>& variables);

  /**
   * preconditions:
   *   x_r is basic,
   *   x_s is non-basic, and
   *   a_rs != 0.
   */
  void pivot(ArithVar x_r, ArithVar x_s);

  void printTableau();

  bool isEjected(ArithVar var){
    return d_basicManager.isMember(var) && !isActiveBasicVariable(var);
  }

  void ejectBasic(ArithVar basic){
    Assert(d_basicManager.isMember(basic));
    Assert(isActiveBasicVariable(basic));

    Debug("arith::eject") << "eject" <<basic << std::endl;

    d_activeBasicVars.erase(basic);
  }

  /**
   * This code undoes the tableau modifications of an injection.
   * Do not call this unless you know what you are doing.
   * You probably want simplex.h's reinjectVariable() instead!
   *
   * Why is this not what you?
   * This code does NOT update the partial model.
   * DO NOT CALL THIS DIRECTLY UNLESS YOU ARE ABSOLUTELY SURE YOU HAVE
   * PROPERLY UPDATED THE PARTIAL MODEL! Learn from my pain --Tim.
   */
  void reinjectBasic(ArithVar basic){
    Assert(d_basicManager.isMember(basic));
    Assert(isEjected(basic));

    Debug("arith::eject") << "reinject" <<basic << std::endl;
    ReducedRowVector* row = lookupEjected(basic);
    d_activeBasicVars.insert(basic);
    updateRow(row);
  }
private:
  inline bool isActiveBasicVariable(ArithVar var){
    return d_activeBasicVars.inSet(var);
  }

  void updateRow(ReducedRowVector* row);
};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */


#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_dense_set.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/simplex.h"


#include "theory/arith/row_vector.h"
#include <vector>

#ifndef __CVC4__THEORY__ARITH__REDUCE_H
#define __CVC4__THEORY__ARITH__REDUCE_H

namespace CVC4 {
namespace theory {
namespace arith {


class Reduce {
private:
  ArithPartialModel& d_pm;
  Tableau& d_tab;

  ArithVarDenseSet& d_bm;
  SimplexDecisionProcedure& d_simplex;

  ArithVar d_oneVar;
  Node d_oneVarIsOne;

  std::vector<ArithVar> constantVars;

  ArithVar d_maxVar;

public:
  Reduce(ArithPartialModel& pm,
         Tableau& tab,
         ArithVarDenseSet& bm,
         SimplexDecisionProcedure& sim,
         ArithVar oneVar,
         Node oneVarIsOne,
         ArithVar maxVar);
  void RemoveConstants();

private:
  void replaceWithConstant(ArithVar x);
  void propagateConstant(ArithVar basic, const Rational& value);
};

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__REDUCE_H */

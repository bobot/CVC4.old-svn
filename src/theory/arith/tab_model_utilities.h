
/**
 * This purpose of this class is to provide utilities
 * that require using both the tableau and the partial model.
 *
 * These utilities are isolated to avoid recursive header issues.
 */

#include "theory/arith/arith_utilities.h"
#include "theory/arith/tableau.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/arithvar_dense_set.h"


#ifndef __CVC4__THEORY__ARITH__TABLEAU_MODEL_UTILITIES_H
#define __CVC4__THEORY__ARITH__TABLEAU_MODEL_UTILITIES_H

namespace CVC4 {
namespace theory {
namespace arith {

class TableauModelUtilities {
public:

  static void reinjectVariable(Tableau& tableau,  ArithVarDenseSet& d_basicManager, ArithPartialModel& pm, ArithVar x);


  static DeltaRational computeRowValue(Tableau& tableau, ArithVarDenseSet& d_basicManager, ArithPartialModel& pm, ArithVar x, bool useSafe);

  static void checkTableau(Tableau& tableau, ArithVarDenseSet& d_basicManager, ArithPartialModel& pm);
};

//static DeltaRational computeRowValue(Tableau* tableau, ArithVarDenseSet& d_basicManager, ArithPartialModel& pm, ArithVar x, bool useSafe);

}; /* namespace arith  */
}; /* namespace theory */
}; /* namespace CVC4   */

#endif /* __CVC4__THEORY__ARITH__TABLEAU_H */

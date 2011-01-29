
#include "theory/arith/tab_model_utilities.h"
#include "theory/arith/delta_rational.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

DeltaRational TableauModelUtilities::computeRowValue(Tableau& tableau, ArithVarDenseSet& basicManager, ArithPartialModel& pm, ArithVar x, bool useSafe)
{
  Assert(basicManager.isMember(x));
  DeltaRational sum(0);

  ReducedRowVector* row = tableau.lookup(x);
  for(ReducedRowVector::NonZeroIterator i = row->beginNonZero(),
        end = row->endNonZero();
      i != end;++i){
    ArithVar nonbasic = getArithVar(*i);
    if(nonbasic == row->basic()) continue;

    Assert(!basicManager.isMember(nonbasic));
    const Rational& coeff = getCoefficient(*i);

    const DeltaRational& assignment =
      pm.getAssignment(nonbasic, useSafe);
    sum = sum + (assignment * coeff);
  }
  return sum;
}

void TableauModelUtilities::reinjectVariable(Tableau& tableau, ArithVarDenseSet& bm, ArithPartialModel& pm, ArithVar x){
  //++(d_statistics.d_statUnEjections);

  tableau.reinjectBasic(x);

  DeltaRational safeAssignment = computeRowValue(tableau, bm, pm, x, true);
  DeltaRational assignment = computeRowValue(tableau, bm, pm, x, false);
  pm.setAssignment(x,safeAssignment,assignment);

  if(Debug.isOn("paranoid:check_tableau")){ checkTableau(tableau, bm, pm); }
}


/**
 * This check is quite expensive.
 * It should be wrapped in a Debug.isOn() guard.
 *   if(Debug.isOn("paranoid:check_tableau")){
 *      checkTableau();
 *   }
 */
void TableauModelUtilities::checkTableau(Tableau& tableau, ArithVarDenseSet& d_basicManager, ArithPartialModel& pm){

  for(ArithVarSet::iterator basicIter = tableau.begin(), end = tableau.end();
      basicIter != end; ++basicIter){
    ArithVar basic = *basicIter;
    ReducedRowVector* row_k = tableau.lookup(basic);
    DeltaRational sum;
    Debug("paranoid:check_tableau") << "starting row" << basic << endl;
    for(ReducedRowVector::NonZeroIterator nonbasicIter = row_k->beginNonZero();
        nonbasicIter != row_k->endNonZero();
        ++nonbasicIter){
      ArithVar nonbasic = nonbasicIter->first;
      if(basic == nonbasic) continue;

      const Rational& coeff = nonbasicIter->second;
      DeltaRational beta = pm.getAssignment(nonbasic);
      Debug("paranoid:check_tableau") << nonbasic << beta << coeff<<endl;
      sum = sum + (beta*coeff);
    }
    DeltaRational shouldBe = pm.getAssignment(basic);
    Debug("paranoid:check_tableau") << "ending row" << sum
                                    << "," << shouldBe << endl;

    Assert(sum == shouldBe);
  }
}



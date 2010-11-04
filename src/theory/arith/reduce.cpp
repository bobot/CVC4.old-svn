#include "theory/arith/reduce.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith ;

Reduce::Reduce(ArithPartialModel& pm,
               Tableau& tab,
               ArithVarDenseSet& bm,
               SimplexDecisionProcedure& sim,
               ArithVar oneVar,
               Node oneVarIsOne,
               ArithVar maxVar)
     :    d_pm(pm),
          d_tab(tab),
          d_bm(bm),
          d_simplex(sim),
          d_oneVar(oneVar),
          d_oneVarIsOne(oneVarIsOne),
          d_maxVar(maxVar)
{
}

void Reduce::replaceWithConstant(ArithVar x){
  Assert(!d_bm.isMember(x));

  Assert(d_pm.hasUpperBound(x));
  Assert(d_pm.hasLowerBound(x));
  Assert(d_pm.getLowerBound(x) == d_pm.getUpperBound(x));
  Assert(d_pm.getLowerBound(x).getInfinitesimalPart() == 0);
  Assert(d_pm.getUpperBound(x).getInfinitesimalPart() == 0);

  Rational assignment = d_pm.getLowerBound(x).getNoninfinitesimalPart();

  for(ArithVarSet::iterator i = d_tab.begin(), end = d_tab.end(); i != end;){
    ArithVar basic = *i; ++i;
    ReducedRowVector* row = d_tab.lookup(basic);
    if(row->has(x)){
      Rational coeff = row->lookup(x);
      RowVector cancel(x, coeff);
      row->addRowTimesConstant(-1,cancel);

      if(assignment == 0){
        if(row->size() == 1){
          propagateConstant(row->basic(),0);
          constantVars.push_back(row->basic());
        }
      }else{
        RowVector constant(d_oneVar, coeff*assignment);
        row->addRowTimesConstant(1,constant);
      }
      if(row->size() == 1){
        propagateConstant(row->basic(),0);
      }else if(row->size() == 2){
        ArithVar nonBasic = row->selectAnyNonBasic();
        if(d_oneVar == nonBasic){
          propagateConstant(row->basic(), row->lookup(nonBasic));
        }
      }
    }
  }
}

void Reduce::propagateConstant(ArithVar basic, const Rational& value){
  Assert(d_bm.isMember(basic));
  Assert(d_bm.isMember(basic));
  DeltaRational dvalue(value, 0);

  bool conflict = d_simplex.AssertEquality(basic, dvalue, d_oneVarIsOne);

  Assert(!conflict);

  d_tab.removeRow(basic);
}

void Reduce::RemoveConstants(){
  d_tab.reinjectAll();

  for(ArithVar x = 0; x < d_maxVar; ++x){
    if(x == d_oneVar) continue;

    if(d_pm.hasUpperBound(x) &&
       d_pm.hasLowerBound(x) &&
       d_pm.getLowerBound(x) == d_pm.getUpperBound(x)){
      Assert(d_pm.getLowerBound(x).getInfinitesimalPart() == 0);
      Assert(d_pm.getUpperBound(x).getInfinitesimalPart() == 0);
      constantVars.push_back(x);
    }
  }
  for(unsigned i = 0; i < constantVars.size(); ++i){
    ArithVar x = constantVars[i];
    if(!d_bm.isMember(x)){
      replaceWithConstant(x);
    }else{
      Assert(d_bm.isMember(x));
      ReducedRowVector* row = d_tab.lookup(x);
      if(row->size() == 1){

        Assert(d_pm.getLowerBound(x) == DeltaRational(0,0));
        Assert(d_pm.getUpperBound(x) == DeltaRational(0,0));

        propagateConstant(x, 0);
      }else{
        ArithVar nonBasic = row->selectAnyNonBasic();
        d_tab.pivot(x, nonBasic);
        replaceWithConstant(x);
      }
    }
  }
}

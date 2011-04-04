
#include "theory/arith/arith_prop_manager.h"

#include "theory/arith/arith_utilities.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdmap.h"
#include "context/cdo.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
using namespace CVC4::kind;
using namespace std;


bool ArithPropManager::propagateArithVar(bool upperbound, ArithVar var, const DeltaRational& b, TNode reason){
  bool success = false;
  Node varAsNode = d_arithvarNodeMap.asNode(var);

  Assert((!upperbound) || (b.getInfinitesimalPart() <= 0) );
  Assert(upperbound || (b.getInfinitesimalPart() >= 0) );
  Kind kind;
  if(upperbound){
    kind = b.getInfinitesimalPart() < 0 ? LT : LEQ;
  } else{
    kind = b.getInfinitesimalPart() > 0 ? GT : GEQ;
  }

  Node righthand = mkRationalNode(b.getNoninfinitesimalPart());

  Node bAsNode = NodeBuilder<2>(kind) << varAsNode << righthand;

  Node bestImplied = upperbound ?
    d_propagator.getBestImpliedUpperBound(bAsNode):
    d_propagator.getBestImpliedLowerBound(bAsNode);

  Debug("ArithPropManager") << upperbound <<","<< var <<","<< b <<","<< reason << endl
                            << bestImplied << endl;

  if(!bestImplied.isNull()){
    Node satValue = d_valuation.getSatValue(bestImplied);
    if(satValue.isNull() && !isPropagated(bestImplied)){
      propagate(bestImplied, reason);
      success = true;
    }else{
      Assert(satValue.getConst<bool>());
    }
  }
  return false;
}

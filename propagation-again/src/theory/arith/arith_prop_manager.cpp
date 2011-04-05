
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

  ++d_statistics.d_propagateArithVarCalls;

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
      ++d_statistics.d_addedPropagation;
      success = true;
    }else if(satValue.isNull()){
      ++d_statistics.d_alreadyPropagatedNode;
    }else if(!isPropagated(bestImplied)){
      Assert(satValue.getConst<bool>());
      ++d_statistics.d_alreadySetSatLiteral;
    }else{
      Assert(satValue.getConst<bool>());
    }
  }
  return success;
}

ArithPropManager::Statistics::Statistics():
  d_propagateArithVarCalls("arith::prop-manager::propagateArithVarCalls",0),
  d_addedPropagation("arith::prop-manager::addedPropagation",0),
  d_alreadySetSatLiteral("arith::prop-manager::alreadySetSatLiteral",0),
  d_alreadyPropagatedNode("arith::prop-manager::alreadyPropagatedNode",0)
{
  StatisticsRegistry::registerStat(&d_propagateArithVarCalls);
  StatisticsRegistry::registerStat(&d_alreadySetSatLiteral);
  StatisticsRegistry::registerStat(&d_alreadyPropagatedNode);
  StatisticsRegistry::registerStat(&d_addedPropagation);
}

ArithPropManager::Statistics::~Statistics()
{
  StatisticsRegistry::unregisterStat(&d_propagateArithVarCalls);
  StatisticsRegistry::unregisterStat(&d_alreadySetSatLiteral);
  StatisticsRegistry::unregisterStat(&d_alreadyPropagatedNode);
  StatisticsRegistry::unregisterStat(&d_addedPropagation);
}

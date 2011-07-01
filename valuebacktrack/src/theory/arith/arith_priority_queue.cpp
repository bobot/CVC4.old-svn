
#include "theory/arith/arith_priority_queue.h"

#include <algorithm>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

ArithPriorityQueue::Statistics::Statistics():
  d_enqueues("theory::arith::pqueue::enqueues", 0),
  d_enqueuesCollection("theory::arith::pqueue::enqueuesCollection", 0),
  d_enqueuesDiffMode("theory::arith::pqueue::enqueuesDiffMode", 0),
  d_enqueuesVarOrderMode("theory::arith::pqueue::enqueuesVarOrderMode", 0),
  d_enqueuesCollectionDuplicates("theory::arith::pqueue::enqueuesCollectionDuplicates", 0),
  d_enqueuesVarOrderModeDuplicates("theory::arith::pqueue::enqueuesVarOrderModeDuplicates", 0)
{
  StatisticsRegistry::registerStat(&d_enqueues);
  StatisticsRegistry::registerStat(&d_enqueuesCollection);
  StatisticsRegistry::registerStat(&d_enqueuesDiffMode);
  StatisticsRegistry::registerStat(&d_enqueuesVarOrderMode);
  StatisticsRegistry::registerStat(&d_enqueuesCollectionDuplicates);
  StatisticsRegistry::registerStat(&d_enqueuesVarOrderModeDuplicates);
}

ArithPriorityQueue::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_enqueues);
  StatisticsRegistry::unregisterStat(&d_enqueuesCollection);
  StatisticsRegistry::unregisterStat(&d_enqueuesDiffMode);
  StatisticsRegistry::unregisterStat(&d_enqueuesVarOrderMode);
  StatisticsRegistry::unregisterStat(&d_enqueuesCollectionDuplicates);
  StatisticsRegistry::unregisterStat(&d_enqueuesVarOrderModeDuplicates);
}

ArithPriorityQueue::ArithPriorityQueue(ArithPartialModel& pm, const Tableau& tableau):
  d_pivotRule(MINIMUM),
  d_partialModel(pm),
  d_tableau(tableau),
  d_modeInUse(Collection),
  d_ZERO_DELTA(0,0)
{}

void ArithPriorityQueue::setPivotRule(PivotRule rule){
  Assert(!inDifferenceMode());
  Debug("arith::setPivotRule") << "setting pivot rule " << rule << endl;
  d_pivotRule = rule;
}

ArithVar ArithPriorityQueue::dequeueInconsistentBasicVariable(){
  AlwaysAssert(!inCollectionMode());

  Debug("arith_update") << "dequeueInconsistentBasicVariable()" << endl;

  if(inDifferenceMode()){
    while(!d_diffQueue.empty()){
      ArithVar var = d_diffQueue.front().variable();
      switch(d_pivotRule){
      case MINIMUM:
        pop_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::minimumRule);
        break;
      case BREAK_TIES:
        pop_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::breakTiesRules);
        break;
      case MAXIMUM:
        pop_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::maximumRule);
        break;
      }
      d_diffQueue.pop_back();
      Debug("arith_update") << "possiblyInconsistentGriggio var" << var << endl;
      if(d_varSet.isMember(var)){
        d_varSet.remove(var);
      }
      if(basicAndInconsistent(var)){

        Debug("test") << d_varSet.size() << ", "
                      << d_diffQueue.size() << endl;
        Assert(d_varSet.size() <= d_diffQueue.size());
        return var;
      }
    }
  }else{
    Assert(inVariableOrderMode());
    Debug("arith_update") << "possiblyInconsistent.size()"
                          << d_varOrderQueue.size() << endl;

    while(!d_varOrderQueue.empty()){
      ArithVar var = d_varOrderQueue.front();
      pop_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());
      d_varOrderQueue.pop_back();

      Debug("arith_update") << "possiblyInconsistent var" << var << endl;
      if(basicAndInconsistent(var)){
        d_varSet.remove(var);
        Assert(d_varSet.size() == d_varOrderQueue.size());
        return var;
      }
    }
  }
  return ARITHVAR_SENTINEL;
}

ArithPriorityQueue::VarDRatPair ArithPriorityQueue::computeDiff(ArithVar basic){
  Assert(basicAndInconsistent(basic));
  const DeltaRational& beta = d_partialModel.getAssignment(basic);
  DeltaRational diff = d_partialModel.belowLowerBound(basic,beta,true) ?
    d_partialModel.getLowerBound(basic) - beta:
    beta - d_partialModel.getUpperBound(basic);

  Assert(d_ZERO_DELTA < diff);
  return VarDRatPair(basic,diff);
}

void ArithPriorityQueue::enqueueIfInconsistent(ArithVar basic){
  Assert(d_tableau.isBasic(basic));

  if(basicAndInconsistent(basic)){
    ++d_statistics.d_enqueues;

    switch(d_modeInUse){
    case Collection:
      ++d_statistics.d_enqueuesCollection;
      if(!d_varSet.isMember(basic)){
        d_varSet.add(basic);
        //d_candidates.push_back(basic);
      }else{
        ++d_statistics.d_enqueuesCollectionDuplicates;
      }
      break;
    case VariableOrder:
      ++d_statistics.d_enqueuesVarOrderMode;
      if(!d_varSet.isMember(basic)){
        d_varSet.add(basic);
        d_varOrderQueue.push_back(basic);
        push_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());
      }else{
        ++d_statistics.d_enqueuesVarOrderModeDuplicates;
      }

      Assert(d_varSet.size() == d_varOrderQueue.size());
      break;
    case Difference:
      ++d_statistics.d_enqueuesDiffMode;
      d_varSet.softAdd(basic);
      d_diffQueue.push_back(computeDiff(basic));
      switch(d_pivotRule){
      case MINIMUM:
        push_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::minimumRule);
        break;
      case BREAK_TIES:
        push_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::breakTiesRules);
        break;
      case MAXIMUM:
        push_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::maximumRule);
        break;
      }
      Assert(d_varSet.size() <= d_diffQueue.size());
      break;
    default:
      Unreachable();
    }
  }
}

void ArithPriorityQueue::purgeInconsistents(bool clearVQO) {
  Assert(d_varOrderQueue.empty());
  ArithVarArray::const_iterator i = d_varSet.begin(), end = d_varSet.end();
  for(; i != end; ++i){
    if(basicAndInconsistent(*i)){
      d_varOrderQueue.push_back(*i);
    }
  }
  d_varSet.purge();

  i = d_varOrderQueue.begin(), end = d_varOrderQueue.end();
  for(; i != end; ++i){
    ArithVar var = *i;
    Assert(basicAndInconsistent(var));
    d_varSet.add(var);
  }
  if(clearVQO){
    d_varOrderQueue.clear();
  }
  Assert(!clearVQO || d_varOrderQueue.empty());
}
void ArithPriorityQueue::transitionToDifferenceMode() {
  Assert(inCollectionMode());
  Assert(d_varOrderQueue.empty());
  Assert(d_diffQueue.empty());

  Debug("arith::priorityqueue") << "transitionToDifferenceMode()" << endl;
  //Fixme up!
  //d_varSet.purge();

  purgeInconsistents(true);
  ArithVarArray::const_iterator i = d_varSet.begin(), end = d_varSet.end();
  for(; i != end; ++i){
    d_diffQueue.push_back(computeDiff(*i));
  }

  switch(d_pivotRule){
  case MINIMUM:
    make_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::minimumRule);
    break;
  case BREAK_TIES:
    make_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::breakTiesRules);
    break;
  case MAXIMUM:
    make_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::maximumRule);
    break;
  }

  //d_candidates.clear();
  d_modeInUse = Difference;

  Assert(d_varSet.size() == d_diffQueue.size());
  Assert(inDifferenceMode());
  Assert(d_varOrderQueue.empty());
  //Assert(d_candidates.empty());
}

void ArithPriorityQueue::transitionToVariableOrderMode() {
  Assert(inDifferenceMode());
  Assert(d_varOrderQueue.empty());
  //Assert(d_candidates.empty());
  //Assert(d_varSet.empty());

  Debug("arith::priorityqueue") << "transitionToVariableOrderMode()" << endl;
  purgeInconsistents(false);

  // DifferenceArray::const_iterator i = d_diffQueue.begin(), end = d_diffQueue.end();
  // for(; i != end; ++i){
  //   ArithVar var = (*i).variable();
  //   if(basicAndInconsistent(var) && !d_varSet.isMember(var)){
  //     d_varSet.add(var);
  //     d_varOrderQueue.push_back(var);
  //   }
  // }
  make_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());

  d_diffQueue.clear();
  d_modeInUse = VariableOrder;

  Assert(inVariableOrderMode());
  Assert(d_diffQueue.empty());
  Assert(d_varSet.size() == d_varOrderQueue.size());
  //Assert(d_candidates.empty());
}

void ArithPriorityQueue::transitionToCollectionMode() {
  Assert(inDifferenceMode() || inVariableOrderMode());
  //Assert(d_diffQueue.empty());
  //Assert(d_candidates.empty());
  //Assert(d_varOrderQueue.empty());
  //Assert(d_varSet.empty());

  Debug("arith::priorityqueue") << "transitionToCollectionMode()" << endl;

  if(inDifferenceMode()){
    d_diffQueue.clear();

    // DifferenceArray::const_iterator i = d_diffQueue.begin(), end = d_diffQueue.end();
    // for(; i != end; ++i){
    //   ArithVar var = (*i).variable();
    //   if(basicAndInconsistent(var) && !d_varSet.isMember(var)){
    //     d_varSet.add(var);
    //     d_varOrderQueue.push_back(var);
    //   }
    // }
    //     d_varSet.add(basic);
    //     d_candidates.push_back(basic);
  }else{
    Assert(inVariableOrderMode());
    d_varOrderQueue.clear();
  }

  d_modeInUse = Collection;
  Assert(d_diffQueue.empty());
  Assert(d_varOrderQueue.empty());
  //Assert(d_candidates.empty());
  //Assert(d_varSet.empty());
}

// void ArithPriorityQueue::clear(){
//   switch(d_modeInUse){
//   case Collection:
//     d_candidates.clear();
//     d_varSet.purge();
//     break;
//   case VariableOrder:
//     if(!d_varOrderQueue.empty()) {
//       d_varOrderQueue.clear();
//       d_varSet.purge();
//     }
//     break;
//   case Difference:
//     if(!d_diffQueue.empty()){
//       d_diffQueue.clear();
//       d_varSet.purge();
//     }
//     break;
//   default:
//     Unreachable();
//   }

//   Assert(d_varSet.empty());
//   Assert(d_candidates.empty());
//   Assert(d_varOrderQueue.empty());
//   Assert(d_diffQueue.empty());
// }

std::ostream& CVC4::theory::arith::operator<<(std::ostream& out, ArithPriorityQueue::PivotRule rule) {
  switch(rule) {
  case ArithPriorityQueue::MINIMUM:
    out << "MINIMUM";
    break;
  case ArithPriorityQueue::BREAK_TIES:
    out << "BREAK_TIES";
    break;
  case ArithPriorityQueue::MAXIMUM:
    out << "MAXIMUM";
    break;
  default:
    out << "PivotRule!UNKNOWN";
  }

  return out;
}

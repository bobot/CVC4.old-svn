
#include "theory/arith/simplex.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;


static const uint32_t NUM_CHECKS = 10;
static const bool CHECK_AFTER_PIVOT = true;
static const uint32_t VARORDER_CHECK_PERIOD = 200;

SimplexDecisionProcedure::Statistics::Statistics():
  d_statPivots("theory::arith::pivots",0),
  d_statUpdates("theory::arith::updates",0),
  d_statAssertUpperConflicts("theory::arith::AssertUpperConflicts", 0),
  d_statAssertLowerConflicts("theory::arith::AssertLowerConflicts", 0),
  d_statUpdateConflicts("theory::arith::UpdateConflicts", 0),
  d_findConflictOnTheQueueTime("theory::arith::findConflictOnTheQueueTime"),
  d_attemptBeforeDiffSearch("theory::arith::qi::BeforeDiffSearch::attempt",0),
  d_successBeforeDiffSearch("theory::arith::qi::BeforeDiffSearch::success",0),
  d_attemptAfterDiffSearch("theory::arith::qi::AfterDiffSearch::attempt",0),
  d_successAfterDiffSearch("theory::arith::qi::AfterDiffSearch::success",0),
  d_attemptDuringDiffSearch("theory::arith::qi::DuringDiffSearch::attempt",0),
  d_successDuringDiffSearch("theory::arith::qi::DuringDiffSearch::success",0),
  d_attemptDuringVarOrderSearch("theory::arith::qi::DuringVarOrderSearch::attempt",0),
  d_successDuringVarOrderSearch("theory::arith::qi::DuringVarOrderSearch::success",0),
  d_attemptAfterVarOrderSearch("theory::arith::qi::AfterVarOrderSearch::attempt",0),
  d_successAfterVarOrderSearch("theory::arith::qi::AfterVarOrderSearch::success",0),
  d_delayedConflicts("theory::arith::delayedConflicts",0),
  d_pivotTime("theory::arith::pivotTime"),
  d_avgNumRowsNotContainingOnUpdate("theory::arith::avgNumRowsNotContainingOnUpdate"),
  d_avgNumRowsNotContainingOnPivot("theory::arith::avgNumRowsNotContainingOnPivot")
{
  StatisticsRegistry::registerStat(&d_statPivots);
  StatisticsRegistry::registerStat(&d_statUpdates);
  StatisticsRegistry::registerStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::registerStat(&d_statAssertLowerConflicts);
  StatisticsRegistry::registerStat(&d_statUpdateConflicts);

  StatisticsRegistry::registerStat(&d_findConflictOnTheQueueTime);

  StatisticsRegistry::registerStat(&d_attemptBeforeDiffSearch);
  StatisticsRegistry::registerStat(&d_successBeforeDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptAfterDiffSearch);
  StatisticsRegistry::registerStat(&d_successAfterDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptDuringDiffSearch);
  StatisticsRegistry::registerStat(&d_successDuringDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptDuringVarOrderSearch);
  StatisticsRegistry::registerStat(&d_successDuringVarOrderSearch);
  StatisticsRegistry::registerStat(&d_attemptAfterVarOrderSearch);
  StatisticsRegistry::registerStat(&d_successAfterVarOrderSearch);

  StatisticsRegistry::registerStat(&d_delayedConflicts);

  StatisticsRegistry::registerStat(&d_pivotTime);

  StatisticsRegistry::registerStat(&d_avgNumRowsNotContainingOnUpdate);
  StatisticsRegistry::registerStat(&d_avgNumRowsNotContainingOnPivot);
}

SimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statPivots);
  StatisticsRegistry::unregisterStat(&d_statUpdates);
  StatisticsRegistry::unregisterStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::unregisterStat(&d_statAssertLowerConflicts);
  StatisticsRegistry::unregisterStat(&d_statUpdateConflicts);

  StatisticsRegistry::unregisterStat(&d_findConflictOnTheQueueTime);

  StatisticsRegistry::unregisterStat(&d_attemptBeforeDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successBeforeDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptAfterDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successAfterDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptDuringDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successDuringDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptDuringVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_successDuringVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_attemptAfterVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_successAfterVarOrderSearch);

  StatisticsRegistry::unregisterStat(&d_delayedConflicts);
  StatisticsRegistry::unregisterStat(&d_pivotTime);

  StatisticsRegistry::unregisterStat(&d_avgNumRowsNotContainingOnUpdate);
  StatisticsRegistry::unregisterStat(&d_avgNumRowsNotContainingOnPivot);
}

/* procedure AssertLower( x_i >= c_i ) */
Node SimplexDecisionProcedure::AssertLower(ArithVar x_i, const DeltaRational& c_i, TNode original){
  Debug("arith") << "AssertLower(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_partialModel.belowLowerBound(x_i, c_i, false)){
    return Node::null();
  }
  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    //d_out->conflict(conflict);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    ++(d_statistics.d_statAssertLowerConflicts);
    return conflict;
  }

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);

  if(!d_tableau.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) < c_i){
      update(x_i, c_i);
    }
  }else{
    d_queue.enqueueIfInconsistent(x_i);
  }

  if(Debug.isOn("model")) { d_partialModel.printModel(x_i); }

  return Node::null();
}

/* procedure AssertUpper( x_i <= c_i) */
Node SimplexDecisionProcedure::AssertUpper(ArithVar x_i, const DeltaRational& c_i, TNode original){

  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_partialModel.aboveUpperBound(x_i, c_i, false) ){ // \upperbound(x_i) <= c_i
    return Node::null(); //sat
  }
  if(d_partialModel.belowLowerBound(x_i, c_i, true)){// \lowerbound(x_i) > c_i
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    ++(d_statistics.d_statAssertUpperConflicts);
    return conflict;
  }

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);

  if(!d_tableau.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }else{
    d_queue.enqueueIfInconsistent(x_i);
  }

  if(Debug.isOn("model")) { d_partialModel.printModel(x_i); }

  return Node::null();
}


/* procedure AssertLower( x_i == c_i ) */
Node SimplexDecisionProcedure::AssertEquality(ArithVar x_i, const DeltaRational& c_i, TNode original){

  Debug("arith") << "AssertEquality(" << x_i << " " << c_i << ")"<< std::endl;

  // u_i <= c_i <= l_i
  // This can happen if both c_i <= x_i and x_i <= c_i are in the system.
  if(d_partialModel.belowLowerBound(x_i, c_i, false) &&
     d_partialModel.aboveUpperBound(x_i, c_i, false)){
    return Node::null(); //sat
  }

  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    return conflict;
  }

  if(d_partialModel.belowLowerBound(x_i, c_i, true)){
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    return conflict;
  }

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);

  if(!d_tableau.isBasic(x_i)){
    if(!(d_partialModel.getAssignment(x_i) == c_i)){
      update(x_i, c_i);
    }
  }else{
    d_queue.enqueueIfInconsistent(x_i);
  }
  return Node::null();
}

// set<ArithVar> tableauAndHasSet(Tableau& tab, ArithVar v){
//   set<ArithVar> has;
//   for(ArithVarSet::const_iterator basicIter = tab.beginBasic();
//       basicIter != tab.endBasic();
//       ++basicIter){
//     ArithVar basic = *basicIter;
//     ReducedRowVector& row = tab.lookup(basic);

//     if(row.has(v)){
//       has.insert(basic);
//     }
//   }
//   return has;
// }

// set<ArithVar> columnIteratorSet(Tableau& tab,ArithVar v){
//   set<ArithVar> has;
//   Column::iterator basicIter = tab.beginColumn(v);
//   Column::iterator endIter = tab.endColumn(v);
//   for(; basicIter != endIter; ++basicIter){
//     ArithVar basic = *basicIter;
//     has.insert(basic);
//   }
//   return has;
// }


/*
bool matchingSets(Tableau& tab, ArithVar v){
  return tableauAndHasSet(tab, v) == columnIteratorSet(tab, v);
}
*/

void SimplexDecisionProcedure::update(ArithVar x_i, const DeltaRational& v){
  Assert(!d_tableau.isBasic(x_i));
  DeltaRational assignment_x_i = d_partialModel.getAssignment(x_i);
  ++(d_statistics.d_statUpdates);

  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  //Assert(matchingSets(d_tableau, x_i));
  Tableau::ColIterator basicIter = d_tableau.colIterator(x_i);
  for(; !basicIter.atEnd(); ++basicIter){
    const TableauEntry& entry = *basicIter;
    Assert(entry.getColVar() == x_i);

    ArithVar x_j = entry.getRowVar();
    //ReducedRowVector& row_j = d_tableau.lookup(x_j);

    //const Rational& a_ji = row_j.lookup(x_i);
    const Rational& a_ji = entry.getCoefficient();

    const DeltaRational& assignment = d_partialModel.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    d_partialModel.setAssignment(x_j, nAssignment);

    d_queue.enqueueIfInconsistent(x_j);
  }

  d_partialModel.setAssignment(x_i, v);

  Assert(d_tableau.getNumRows() >= d_tableau.getRowLength(x_i));
  double difference = ((double)d_tableau.getNumRows()) - ((double) d_tableau.getRowLength(x_i));

  (d_statistics.d_avgNumRowsNotContainingOnUpdate).addEntry(difference);
  if(Debug.isOn("paranoid:check_tableau")){  debugCheckTableau(); }
}

void SimplexDecisionProcedure::debugPivotSimplex(ArithVar x_i, ArithVar x_j){
  Debug("arith::simplex:row") << "debugRowSimplex("
                              << x_i  << "|->" << x_j
                              << ")" << endl;

  for(Tableau::RowIterator iter = d_tableau.rowIterator(x_i); !iter.atEnd(); ++iter){
    const TableauEntry& entry = *iter;

    ArithVar var = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    DeltaRational beta = d_partialModel.getAssignment(var);
    Debug("arith::simplex:row") << var << beta << coeff;
    if(d_partialModel.hasLowerBound(var)){
      Debug("arith::simplex:row") << "(lb " << d_partialModel.getLowerBound(var) << ")";
    }
    if(d_partialModel.hasUpperBound(var)){
      Debug("arith::simplex:row") << "(up " << d_partialModel.getUpperBound(var) << ")";
    }
    Debug("arith::simplex:row") << endl;
  }
  Debug("arith::simplex:row") << "end row"<< endl;
}

void SimplexDecisionProcedure::pivotAndUpdate(ArithVar x_i, ArithVar x_j, DeltaRational& v){
  Assert(x_i != x_j);

  TimerStat::CodeTimer codeTimer(d_statistics.d_pivotTime);

  if(Debug.isOn("arith::simplex:row")){ debugPivotSimplex(x_i, x_j); }

  const TableauEntry& entry_ij =  d_tableau.findEntry(x_i, x_j);
  Assert(!entry_ij.blank());


  const Rational& a_ij = entry_ij.getCoefficient();


  const DeltaRational& betaX_i = d_partialModel.getAssignment(x_i);

  Rational inv_aij = a_ij.inverse();
  DeltaRational theta = (v - betaX_i)*inv_aij;

  d_partialModel.setAssignment(x_i, v);


  DeltaRational tmp = d_partialModel.getAssignment(x_j) + theta;
  d_partialModel.setAssignment(x_j, tmp);


  //Assert(matchingSets(d_tableau, x_j));
  for(Tableau::ColIterator iter = d_tableau.colIterator(x_j); !iter.atEnd(); ++iter){
    const TableauEntry& entry = *iter;
    Assert(entry.getColVar() == x_j);
    ArithVar x_k = entry.getRowVar();
    if(x_k != x_i ){
      const Rational& a_kj = entry.getCoefficient();
      DeltaRational nextAssignment = d_partialModel.getAssignment(x_k) + (theta * a_kj);
      d_partialModel.setAssignment(x_k, nextAssignment);

      d_queue.enqueueIfInconsistent(x_k);
    }
  }

  // Pivots
  ++(d_statistics.d_statPivots);

  Assert(d_tableau.getNumRows() >= d_tableau.getRowLength(x_j));
  double difference = ((double)d_tableau.getNumRows()) - ((double) d_tableau.getRowLength(x_j));
  (d_statistics.d_avgNumRowsNotContainingOnPivot).addEntry(difference);
  d_tableau.pivot(x_i, x_j);


  d_queue.enqueueIfInconsistent(x_j);

  if(Debug.isOn("tableau")){
    d_tableau.printTableau();
  }
}

ArithVar SimplexDecisionProcedure::minVarOrder(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!simp.d_tableau.isBasic(x));
  Assert(!simp.d_tableau.isBasic(y));
  if(x <= y){
    return x;
  } else {
    return y;
  }
}

ArithVar SimplexDecisionProcedure::minColLength(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!simp.d_tableau.isBasic(x));
  Assert(!simp.d_tableau.isBasic(y));
  uint32_t xLen = simp.d_tableau.getColLength(x);
  uint32_t yLen = simp.d_tableau.getColLength(y);
  if( xLen > yLen){
     return y;
  } else if( xLen== yLen ){
    return minVarOrder(simp,x,y);
  }else{
    return x;
  }
}

ArithVar SimplexDecisionProcedure::minBoundAndRowCount(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!simp.d_tableau.isBasic(x));
  Assert(!simp.d_tableau.isBasic(y));
  if(simp.d_partialModel.hasEitherBound(x) && !simp.d_partialModel.hasEitherBound(y)){
    return y;
  }else if(!simp.d_partialModel.hasEitherBound(x) && simp.d_partialModel.hasEitherBound(y)){
    return x;
  }else {
    return minColLength(simp, x, y);
  }
}

template <bool above, SimplexDecisionProcedure::PreferenceFunction pref>
ArithVar SimplexDecisionProcedure::selectSlack(ArithVar x_i){
  ArithVar slack = ARITHVAR_SENTINEL;

  for(Tableau::RowIterator iter = d_tableau.rowIterator(x_i); !iter.atEnd();  ++iter){
    const TableauEntry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x_i) continue;

    const Rational& a_ij = entry.getCoefficient();
    int sgn = a_ij.sgn();
    if(isAcceptableSlack<above>(sgn, nonbasic)){
      //If one of the above conditions is met, we have found an acceptable
      //nonbasic variable to pivot x_i with.  We can now choose which one we
      //prefer the most.
      slack = (slack == ARITHVAR_SENTINEL) ? nonbasic : pref(*this, slack, nonbasic);
    }
  }

  return slack;
}

Node betterConflict(TNode x, TNode y){
  if(x.isNull()) return y;
  else if(y.isNull()) return x;
  else if(x.getNumChildren() <= y.getNumChildren()) return x;
  else return y;
}

Node SimplexDecisionProcedure::findConflictOnTheQueue(SearchPeriod type, bool returnFirst) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_findConflictOnTheQueueTime);

  switch(type){
  case BeforeDiffSearch:     ++(d_statistics.d_attemptBeforeDiffSearch); break;
  case DuringDiffSearch:     ++(d_statistics.d_attemptDuringDiffSearch); break;
  case AfterDiffSearch:      ++(d_statistics.d_attemptAfterDiffSearch); break;
  case DuringVarOrderSearch: ++(d_statistics.d_attemptDuringVarOrderSearch); break;
  case AfterVarOrderSearch:  ++(d_statistics.d_attemptAfterVarOrderSearch); break;
  }

  bool success = false;
  Node firstConflict = Node::null();
  ArithPriorityQueue::const_iterator i = d_queue.begin();
  ArithPriorityQueue::const_iterator end = d_queue.end();
  for(; i != end; ++i){
    ArithVar x_i = *i;

    if(d_tableau.isBasic(x_i)){
      Node possibleConflict = checkBasicForConflict(x_i);
      if(!possibleConflict.isNull()){
        success = true;
        if(returnFirst && firstConflict.isNull()){
          firstConflict = possibleConflict;
        }else{
          delayConflictAsLemma(possibleConflict);
        }
      }
    }
  }
  if(success){
    switch(type){
    case BeforeDiffSearch:     ++(d_statistics.d_successBeforeDiffSearch); break;
    case DuringDiffSearch:     ++(d_statistics.d_successDuringDiffSearch); break;
    case AfterDiffSearch:      ++(d_statistics.d_successAfterDiffSearch); break;
    case DuringVarOrderSearch: ++(d_statistics.d_successDuringVarOrderSearch); break;
    case AfterVarOrderSearch:  ++(d_statistics.d_successAfterVarOrderSearch); break;
    }
  }
  return firstConflict;
}

Node SimplexDecisionProcedure::updateInconsistentVars(){
  if(d_queue.empty()){
    return Node::null();
  }
  static unsigned int instance = 0;
  ++instance;

  Debug("arith::updateInconsistentVars") << "begin updateInconsistentVars() "
                                         << instance << endl;

  d_queue.transitionToDifferenceMode();

  Node possibleConflict = Node::null();
  if(d_queue.size() > 1){
    possibleConflict = findConflictOnTheQueue(BeforeDiffSearch);
  }
  if(possibleConflict.isNull()){
    uint32_t numHueristicPivots = d_numVariables + 1;
    uint32_t pivotsRemaining = numHueristicPivots;
    uint32_t pivotsPerCheck = (numHueristicPivots/NUM_CHECKS) + (NUM_CHECKS-1);
    while(!d_queue.empty() &&
          possibleConflict.isNull() &&
          pivotsRemaining > 0){
      uint32_t pivotsToDo = min(pivotsPerCheck, pivotsRemaining);
      possibleConflict = searchForFeasibleSolution<minBoundAndRowCount>(pivotsToDo);
      pivotsRemaining -= pivotsToDo;
      //Once every CHECK_PERIOD examine the entire queue for conflicts
      if(possibleConflict.isNull()){
        possibleConflict = findConflictOnTheQueue(DuringDiffSearch);
      }else{
        findConflictOnTheQueue(AfterDiffSearch, false);
      }
    }
  }

  if(!d_queue.empty() && possibleConflict.isNull()){
    d_queue.transitionToVariableOrderMode();

    while(!d_queue.empty() && possibleConflict.isNull()){
      possibleConflict = searchForFeasibleSolution<minVarOrder>(VARORDER_CHECK_PERIOD);

      //Once every CHECK_PERIOD examine the entire queue for conflicts
      if(possibleConflict.isNull()){
        possibleConflict = findConflictOnTheQueue(DuringVarOrderSearch);
      }else{
        findConflictOnTheQueue(AfterVarOrderSearch, false);
      }
    }
  }

  Assert(!possibleConflict.isNull() || d_queue.empty());

  // Curiously the invariant that we always do a full check
  // means that the assignment we can always empty these queues.
  d_queue.clear();

  Assert(!d_queue.inCollectionMode());
  d_queue.transitionToCollectionMode();


  Assert(d_queue.inCollectionMode());

  Debug("arith::updateInconsistentVars") << "end updateInconsistentVars() "
                                         << instance << endl;

  return possibleConflict;
}

Node SimplexDecisionProcedure::checkBasicForConflict(ArithVar basic){

  Assert(d_tableau.isBasic(basic));
  const DeltaRational& beta = d_partialModel.getAssignment(basic);

  if(d_partialModel.belowLowerBound(basic, beta, true)){
    ArithVar x_j = selectSlackUpperBound<minVarOrder>(basic);
    if(x_j == ARITHVAR_SENTINEL ){
      return generateConflictBelowLowerBound(basic);
    }
  }else if(d_partialModel.aboveUpperBound(basic, beta, true)){
    ArithVar x_j = selectSlackLowerBound<minVarOrder>(basic);
    if(x_j == ARITHVAR_SENTINEL ){
      return generateConflictAboveUpperBound(basic);
    }
  }
  return Node::null();
}

//corresponds to Check() in dM06
template <SimplexDecisionProcedure::PreferenceFunction pf>
Node SimplexDecisionProcedure::searchForFeasibleSolution(uint32_t remainingIterations){
  Debug("arith") << "updateInconsistentVars" << endl;
  Assert(remainingIterations > 0);

  while(remainingIterations > 0){
    if(Debug.isOn("paranoid:check_tableau")){ debugCheckTableau(); }

    ArithVar x_i = d_queue.dequeueInconsistentBasicVariable();
    Debug("arith::update::select") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == ARITHVAR_SENTINEL){
      Debug("arith_update") << "No inconsistent variables" << endl;
      return Node::null(); //sat
    }

    --remainingIterations;

    DeltaRational beta_i = d_partialModel.getAssignment(x_i);
    ArithVar x_j = ARITHVAR_SENTINEL;

    if(d_partialModel.belowLowerBound(x_i, beta_i, true)){
      x_j = selectSlackUpperBound<pf>(x_i);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictBelowLowerBound(x_i); //unsat
      }
      DeltaRational l_i = d_partialModel.getLowerBound(x_i);
      pivotAndUpdate(x_i, x_j, l_i);

    }else if(d_partialModel.aboveUpperBound(x_i, beta_i, true)){
      x_j = selectSlackLowerBound<pf>(x_i);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictAboveUpperBound(x_i); //unsat
      }
      DeltaRational u_i = d_partialModel.getUpperBound(x_i);
      pivotAndUpdate(x_i, x_j, u_i);
    }
    Assert(x_j != ARITHVAR_SENTINEL);

    //Check to see if we already have a conflict with x_j to prevent wasteful work
    if(CHECK_AFTER_PIVOT){
      if(selectSlackUpperBound<pf>(x_j) == ARITHVAR_SENTINEL){
        Node possibleConflict  = deduceUpperBound(x_j);
        if(!possibleConflict.isNull()){
          return possibleConflict;
        }
      }
      if(selectSlackLowerBound<pf>(x_j) == ARITHVAR_SENTINEL){
        Node possibleConflict  = deduceLowerBound(x_j);
        if(!possibleConflict.isNull()){
          return possibleConflict;
        }
      }
    }
  }
  Assert(remainingIterations == 0);

  return Node::null();
}

template <bool upperBound>
void SimplexDecisionProcedure::explainNonbasics(ArithVar basic, NodeBuilder<>& output){
  Assert(d_tableau.isBasic(basic));

  Tableau::RowIterator iter = d_tableau.rowIterator(basic);
  for(; !iter.atEnd(); ++iter){
    const TableauEntry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == basic) continue;

    const Rational& a_ij = entry.getCoefficient();
    Assert(a_ij != d_ZERO);
    TNode bound = TNode::null();

    int sgn = a_ij.sgn();
    Assert(sgn != 0);
    if(upperBound){
      if(sgn < 0){
        bound = d_partialModel.getLowerConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound = d_partialModel.getUpperConstraint(nonbasic);
      }
    }else{
      if(sgn < 0){
        bound =  d_partialModel.getUpperConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound =  d_partialModel.getLowerConstraint(nonbasic);
      }
    }
    Assert(!bound.isNull());
    output << bound;
  }
}


Node SimplexDecisionProcedure::deduceUpperBound(ArithVar basicVar){
  Assert(d_tableau.isBasic(basicVar));
  Assert(selectSlackUpperBound<minVarOrder>(basicVar) == ARITHVAR_SENTINEL);

  const DeltaRational& assignment = d_partialModel.getAssignment(basicVar);

  Assert(assignment.getInfinitesimalPart() <= 0);

  if(d_partialModel.strictlyBelowUpperBound(basicVar, assignment)){
    NodeBuilder<> nb(kind::AND);
    explainNonbasicsUpperBound(basicVar, nb);
    Node explanation = nb;
    Debug("waka-waka") << basicVar << " ub " << assignment << " "<< explanation << endl;
    Node res = AssertUpper(basicVar, assignment, explanation);
    if(res.isNull()){
      d_propManager.propagateArithVar(true, basicVar, assignment, explanation);
    }
    return res;
  }else{
    return Node::null();
  }
}

Node SimplexDecisionProcedure::deduceLowerBound(ArithVar basicVar){
  Assert(d_tableau.isBasic(basicVar));
  Assert(selectSlackLowerBound<minVarOrder>(basicVar) == ARITHVAR_SENTINEL);
  const DeltaRational& assignment = d_partialModel.getAssignment(basicVar);

  if(Debug.isOn("paranoid:check_tableau")){ debugCheckTableau(); }

  Assert(assignment.getInfinitesimalPart() >= 0);

  if(d_partialModel.strictlyAboveLowerBound(basicVar, assignment)){
    NodeBuilder<> nb(kind::AND);
    explainNonbasicsLowerBound(basicVar, nb);
    Node explanation = nb;
    Debug("waka-waka") << basicVar << " lb " << assignment << " "<< explanation << endl;
    Node res = AssertLower(basicVar, assignment, explanation);
    if(res.isNull()){
      d_propManager.propagateArithVar(false, basicVar, assignment, explanation);
    }
    return res;
  }else{
    return Node::null();
  }
}

Node SimplexDecisionProcedure::generateConflictAboveUpperBound(ArithVar conflictVar){

  NodeBuilder<> nb(kind::AND);
  nb << d_partialModel.getUpperConstraint(conflictVar);

  explainNonbasicsLowerBound(conflictVar, nb);

  Node conflict = nb;
  return conflict;
}

Node SimplexDecisionProcedure::generateConflictBelowLowerBound(ArithVar conflictVar){
  NodeBuilder<> nb(kind::AND);
  nb << d_partialModel.getLowerConstraint(conflictVar);

  explainNonbasicsUpperBound(conflictVar, nb);

  Node conflict = nb;
  return conflict;
}

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational SimplexDecisionProcedure::computeRowValue(ArithVar x, bool useSafe){
  Assert(d_tableau.isBasic(x));
  DeltaRational sum(0);

  for(Tableau::RowIterator i = d_tableau.rowIterator(x); !i.atEnd(); ++i){
    const TableauEntry& entry = (*i);
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x) continue;
    const Rational& coeff = entry.getCoefficient();

    const DeltaRational& assignment = d_partialModel.getAssignment(nonbasic, useSafe);
    sum = sum + (assignment * coeff);
  }
  return sum;
}

/**
 * This check is quite expensive.
 * It should be wrapped in a Debug.isOn() guard.
 *   if(Debug.isOn("paranoid:check_tableau")){
 *      checkTableau();
 *   }
 */
void SimplexDecisionProcedure::debugCheckTableau(){
  ArithVarSet::const_iterator basicIter = d_tableau.beginBasic();
  ArithVarSet::const_iterator endIter = d_tableau.endBasic();
  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    DeltaRational sum;
    Debug("paranoid:check_tableau") << "starting row" << basic << endl;
    Tableau::RowIterator nonbasicIter = d_tableau.rowIterator(basic);
    for(; !nonbasicIter.atEnd(); ++nonbasicIter){
      const TableauEntry& entry = *nonbasicIter;
      ArithVar nonbasic = entry.getColVar();
      if(basic == nonbasic) continue;

      const Rational& coeff = entry.getCoefficient();
      DeltaRational beta = d_partialModel.getAssignment(nonbasic);
      Debug("paranoid:check_tableau") << nonbasic << beta << coeff<<endl;
      sum = sum + (beta*coeff);
    }
    DeltaRational shouldBe = d_partialModel.getAssignment(basic);
    Debug("paranoid:check_tableau") << "ending row" << sum
                                    << "," << shouldBe << endl;

    Assert(sum == shouldBe);
  }
}


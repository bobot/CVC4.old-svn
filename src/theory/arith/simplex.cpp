
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
    //return false; //sat
    return Node::null();
  }
  if(d_partialModel.belowLowerBound(x_i, c_i, true)){// \lowerbound(x_i) > c_i
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    ++(d_statistics.d_statAssertUpperConflicts);
    //d_out->conflict(conflict);
    return conflict;
    //return true;
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
  //return false;
}


/* procedure AssertLower( x_i == c_i ) */
Node SimplexDecisionProcedure::AssertEquality(ArithVar x_i, const DeltaRational& c_i, TNode original){

  Debug("arith") << "AssertEquality(" << x_i << " " << c_i << ")"<< std::endl;

  // u_i <= c_i <= l_i
  // This can happen if both c_i <= x_i and x_i <= c_i are in the system.
  if(d_partialModel.belowLowerBound(x_i, c_i, false) &&
     d_partialModel.aboveUpperBound(x_i, c_i, false)){
    //return false; //sat
    return Node::null();
  }

  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    //d_out->conflict(conflict);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    //return true;
    return conflict;
  }

  if(d_partialModel.belowLowerBound(x_i, c_i, true)){
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    //d_out->conflict(conflict);
    //return true;
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
    //checkBasicVariable(x_i);
  }

  //return false;
  return Node::null();
}

set<ArithVar> tableauAndHasSet(Tableau& tab, ArithVar v){
  set<ArithVar> has;
  for(ArithVarSet::iterator basicIter = tab.begin();
      basicIter != tab.end();
      ++basicIter){
    ArithVar basic = *basicIter;
    ReducedRowVector& row = tab.lookup(basic);

    if(row.has(v)){
      has.insert(basic);
    }
  }
  return has;
}

set<ArithVar> columnIteratorSet(Tableau& tab,ArithVar v){
  set<ArithVar> has;
  Column::iterator basicIter = tab.beginColumn(v);
  Column::iterator endIter = tab.endColumn(v);
  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    has.insert(basic);
  }
  return has;
}


bool matchingSets(Tableau& tab, ArithVar v){
  return tableauAndHasSet(tab, v) == columnIteratorSet(tab, v);
}

void SimplexDecisionProcedure::update(ArithVar x_i, const DeltaRational& v){
  Assert(!d_tableau.isBasic(x_i));
  DeltaRational assignment_x_i = d_partialModel.getAssignment(x_i);
  ++(d_statistics.d_statUpdates);

  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  Assert(matchingSets(d_tableau, x_i));
  Column::iterator basicIter = d_tableau.beginColumn(x_i);
  Column::iterator endIter   = d_tableau.endColumn(x_i);
  for(; basicIter != endIter; ++basicIter){
    ArithVar x_j = *basicIter;
    ReducedRowVector& row_j = d_tableau.lookup(x_j);

    Assert(row_j.has(x_i));
    const Rational& a_ji = row_j.lookup(x_i);

    const DeltaRational& assignment = d_partialModel.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    d_partialModel.setAssignment(x_j, nAssignment);

    d_queue.enqueueIfInconsistent(x_j);
  }

  d_partialModel.setAssignment(x_i, v);

  Assert(d_tableau.getNumRows() >= d_tableau.getRowCount(x_i));
  double difference = ((double)d_tableau.getNumRows()) - ((double) d_tableau.getRowCount(x_i));

  (d_statistics.d_avgNumRowsNotContainingOnUpdate).addEntry(difference);
  if(Debug.isOn("paranoid:check_tableau")){
    checkTableau();
  }
}

void SimplexDecisionProcedure::pivotAndUpdate(ArithVar x_i, ArithVar x_j, DeltaRational& v){
  Assert(x_i != x_j);

  TimerStat::CodeTimer codeTimer(d_statistics.d_pivotTime);

  if(Debug.isOn("arith::pivotAndUpdate")){
    Debug("arith::pivotAndUpdate") << "x_i " << "|->" << x_j << endl;
    ReducedRowVector& row_k = d_tableau.lookup(x_i);
    for(ReducedRowVector::const_iterator varIter = row_k.begin();
        varIter != row_k.end();
        ++varIter){

      ArithVar var = (*varIter).getArithVar();
      const Rational& coeff = (*varIter).getCoefficient();
      DeltaRational beta = d_partialModel.getAssignment(var);
      Debug("arith::pivotAndUpdate") << var << beta << coeff;
      if(d_partialModel.hasLowerBound(var)){
        Debug("arith::pivotAndUpdate") << "(lb " << d_partialModel.getLowerBound(var) << ")";
      }
      if(d_partialModel.hasUpperBound(var)){
        Debug("arith::pivotAndUpdate") << "(up " << d_partialModel.getUpperBound(var)
                                       << ")";
      }
      Debug("arith::pivotAndUpdate") << endl;
    }
    Debug("arith::pivotAndUpdate") << "end row"<< endl;
  }


  ReducedRowVector& row_i = d_tableau.lookup(x_i);
  const Rational& a_ij = row_i.lookup(x_j);


  const DeltaRational& betaX_i = d_partialModel.getAssignment(x_i);

  Rational inv_aij = a_ij.inverse();
  DeltaRational theta = (v - betaX_i)*inv_aij;

  d_partialModel.setAssignment(x_i, v);


  DeltaRational tmp = d_partialModel.getAssignment(x_j) + theta;
  d_partialModel.setAssignment(x_j, tmp);


  Assert(matchingSets(d_tableau, x_j));
  Column::iterator basicIter = d_tableau.beginColumn(x_j);
  Column::iterator endIter   = d_tableau.endColumn(x_j);
  for(; basicIter != endIter; ++basicIter){
    ArithVar x_k = *basicIter;
    ReducedRowVector& row_k = d_tableau.lookup(x_k);

    Assert(row_k.has(x_j));
    if(x_k != x_i ){
      const Rational& a_kj = row_k.lookup(x_j);
      DeltaRational nextAssignment = d_partialModel.getAssignment(x_k) + (theta * a_kj);
      d_partialModel.setAssignment(x_k, nextAssignment);

      d_queue.enqueueIfInconsistent(x_k);
    }
  }

  // Pivots
  ++(d_statistics.d_statPivots);

  Assert(d_tableau.getNumRows() >= d_tableau.getRowCount(x_j));
  double difference = ((double)d_tableau.getNumRows()) - ((double) d_tableau.getRowCount(x_j));
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

ArithVar SimplexDecisionProcedure::minRowCount(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!simp.d_tableau.isBasic(x));
  Assert(!simp.d_tableau.isBasic(y));
  if(simp.d_tableau.getRowCount(x) > simp.d_tableau.getRowCount(y)){
    return y;
  } else {
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
    return minRowCount(simp, x, y);
  }
}

template <bool above, SimplexDecisionProcedure::PreferenceFunction pref>
ArithVar SimplexDecisionProcedure::selectSlack(ArithVar x_i){
  ReducedRowVector& row_i = d_tableau.lookup(x_i);

  ArithVar slack = ARITHVAR_SENTINEL;

  for(ReducedRowVector::const_iterator nbi = row_i.begin(), end = row_i.end();
      nbi != end; ++nbi){
    ArithVar nonbasic = (*nbi).getArithVar();
    if(nonbasic == x_i) continue;

    const Rational& a_ij = (*nbi).getCoefficient();
    int sgn = a_ij.sgn();
    if(( above && sgn < 0 && d_partialModel.strictlyBelowUpperBound(nonbasic)) ||
       ( above && sgn > 0 && d_partialModel.strictlyAboveLowerBound(nonbasic)) ||
       (!above && sgn > 0 && d_partialModel.strictlyBelowUpperBound(nonbasic)) ||
       (!above && sgn < 0 && d_partialModel.strictlyAboveLowerBound(nonbasic))) {
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

  static CVC4_THREADLOCAL(unsigned int) instance = 0;
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
    ArithVar x_j = selectSlackBelow<minVarOrder>(basic);
    if(x_j == ARITHVAR_SENTINEL ){
      return generateConflictBelow(basic);
    }
  }else if(d_partialModel.aboveUpperBound(basic, beta, true)){
    ArithVar x_j = selectSlackAbove<minVarOrder>(basic);
    if(x_j == ARITHVAR_SENTINEL ){
      return generateConflictAbove(basic);
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
    if(Debug.isOn("paranoid:check_tableau")){ checkTableau(); }

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
      x_j = selectSlackBelow<pf>(x_i);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictBelow(x_i); //unsat
      }
      DeltaRational l_i = d_partialModel.getLowerBound(x_i);
      pivotAndUpdate(x_i, x_j, l_i);

    }else if(d_partialModel.aboveUpperBound(x_i, beta_i, true)){
      x_j = selectSlackAbove<pf>(x_i);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictAbove(x_i); //unsat
      }
      DeltaRational u_i = d_partialModel.getUpperBound(x_i);
      pivotAndUpdate(x_i, x_j, u_i);
    }
    Assert(x_j != ARITHVAR_SENTINEL);
    //Check to see if we already have a conflict with x_j to prevent wasteful work
    if(CHECK_AFTER_PIVOT){
      Node earlyConflict = checkBasicForConflict(x_j);
      if(!earlyConflict.isNull()){
        return earlyConflict;
      }
    }
  }
  Assert(remainingIterations == 0);

  return Node::null();
}


Node SimplexDecisionProcedure::generateConflictAbove(ArithVar conflictVar){

  ReducedRowVector& row_i = d_tableau.lookup(conflictVar);

  NodeBuilder<> nb(kind::AND);
  TNode bound = d_partialModel.getUpperConstraint(conflictVar);

  Debug("arith")  << "generateConflictAbove "
                  << "conflictVar " << conflictVar
                  << " " << d_partialModel.getAssignment(conflictVar)
                  << " " << bound << endl;

  nb << bound;

  ReducedRowVector::const_iterator nbi = row_i.begin(), end = row_i.end();

  for(; nbi != end; ++nbi){
    ArithVar nonbasic = (*nbi).getArithVar();
    if(nonbasic == conflictVar) continue;

    const Rational& a_ij = (*nbi).getCoefficient();
    Assert(a_ij != d_ZERO);

    int sgn = a_ij.sgn();
    Assert(sgn != 0);
    if(sgn < 0){
      bound =  d_partialModel.getUpperConstraint(nonbasic);
      Debug("arith") << "below 0 " << nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic)
                     << " " << bound << endl;
      nb << bound;
    }else{
      Assert(sgn > 0);
      bound =  d_partialModel.getLowerConstraint(nonbasic);
      Debug("arith") << " above 0 " << nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic)
                     << " " << bound << endl;
      nb << bound;
    }
  }
  Node conflict = nb;
  return conflict;
}

Node SimplexDecisionProcedure::generateConflictBelow(ArithVar conflictVar){
  ReducedRowVector& row_i = d_tableau.lookup(conflictVar);

  NodeBuilder<> nb(kind::AND);
  TNode bound = d_partialModel.getLowerConstraint(conflictVar);

  Debug("arith") << "generateConflictBelow "
                 << "conflictVar " << conflictVar
                 << d_partialModel.getAssignment(conflictVar) << " "
                 << " " << bound << endl;
  nb << bound;


  ReducedRowVector::const_iterator nbi = row_i.begin(), end = row_i.end();
  for(; nbi != end; ++nbi){
    ArithVar nonbasic = (*nbi).getArithVar();
    if(nonbasic == conflictVar) continue;

    const Rational& a_ij = (*nbi).getCoefficient();

    int sgn = a_ij.sgn();
    Assert(a_ij != d_ZERO);
    Assert(sgn != 0);

    if(sgn < 0){
      TNode bound = d_partialModel.getLowerConstraint(nonbasic);
      Debug("arith") << "Lower "<< nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic) << " "
                     << bound << endl;

      nb << bound;
    }else{
      Assert(sgn > 0);
      TNode bound = d_partialModel.getUpperConstraint(nonbasic);
      Debug("arith") << "Upper "<< nonbasic << " "
                     << d_partialModel.getAssignment(nonbasic) << " "
                     << bound << endl;

      nb << bound;
    }
  }
  Node conflict (nb.constructNode());
  return conflict;
}

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational SimplexDecisionProcedure::computeRowValue(ArithVar x, bool useSafe){
  Assert(d_tableau.isBasic(x));
  DeltaRational sum(0);

  ReducedRowVector& row = d_tableau.lookup(x);
  for(ReducedRowVector::const_iterator i = row.begin(), end = row.end();
      i != end;++i){
    ArithVar nonbasic = (*i).getArithVar();
    if(nonbasic == row.basic()) continue;
    const Rational& coeff = (*i).getCoefficient();

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
void SimplexDecisionProcedure::checkTableau(){

  for(ArithVarSet::iterator basicIter = d_tableau.begin();
      basicIter != d_tableau.end(); ++basicIter){
    ArithVar basic = *basicIter;
    ReducedRowVector& row_k = d_tableau.lookup(basic);
    DeltaRational sum;
    Debug("paranoid:check_tableau") << "starting row" << basic << endl;
    for(ReducedRowVector::const_iterator nonbasicIter = row_k.begin();
        nonbasicIter != row_k.end();
        ++nonbasicIter){
      ArithVar nonbasic = (*nonbasicIter).getArithVar();
      if(basic == nonbasic) continue;

      const Rational& coeff = (*nonbasicIter).getCoefficient();
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


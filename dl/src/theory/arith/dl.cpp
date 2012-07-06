/*********************                                                        */
/*! \file cdgraph.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Context-dependent directed graph.
 **
 ** Context dependent direct graph.
 **/

#include "theory/arith/dl.h"

namespace CVC4 {
namespace theory {
namespace arith {

bool DifferenceLogicDecisionProcedure::setTrue(EdgeId eid){
  Assert(d_gamma.completelyEmpty());
  Assert(d_piPrime.empty());

  const Edge& e = d_graph.getEdge(eid);
  VertexId u_id = e.getStart();
  VertexId v_id = e.getEnd();
  DeltaRational d = constraintValue(eid);

  Debug("dl") << "setTrue(" << eid << ") : " << u_id << " -> " << v_id
              << " [" << d << "]" << std::endl; 

  d_gamma.updateIfMin(v_id, getPi(u_id) + d - getPi(v_id), eid );
  // If this is >= 0, do nothing
  // If this is < 0, then gamma(v_id) needs to be updated
  // and everything else is implicitly 0

  while(true){
    if(d_gamma.getValue(u_id).sgn() != 0){
      return false;
    }else if(d_gamma.heapEmpty()){
      return true;
    }

    VertexId s = d_gamma.heapMinimum();
    Debug("dl") << "gamma[" << s<<"] = " << d_gamma.getValue(s) << std::endl;
    Assert(d_gamma.getValue(s).sgn() < 0);

    d_gamma.heapPop();

    d_piPrime.set(s, getPi(s) + d_gamma.getValue(s));
    d_gamma.clearValue(s); // set to 0

    const Vertex& s_node = d_graph.getVertex(s);

    const EdgeIdVector& s_outgoing = s_node.getOutgoingEdges();
    EdgeIdVector::const_iterator s_iter = s_outgoing.begin(), s_end = s_outgoing.end();
    for(; s_iter != s_end; ++s_iter){
      EdgeId currentEdgeId = *s_iter;
      const Edge& e = d_graph.getEdge(currentEdgeId);
      Assert(e.getStart() == s);
      VertexId t = e.getEnd();


      if(!d_piPrime.isKey(t)){
        DeltaRational c = constraintValue(currentEdgeId);
        DeltaRational theta = d_piPrime[s] + c - getPi(t);

        d_gamma.updateIfMin(t, theta, currentEdgeId);
      }
    }
  }
}

void DifferenceLogicDecisionProcedure::explainCycle(VertexId first, NodeBuilder<>& out){

  VertexId current = first;
  do{
    EdgeId currEdge = d_gamma.getEdgeId(current);

    Constraint c = d_graph.getEdgeAnnotation(currEdge);
    c->explainForConflict(out);
    const Edge& e = d_graph.getEdge(currEdge);

    VertexId next = e.getStart();

    current = next;
  }while(current != first);
}

DifferenceLogicDecisionProcedure::EdgeId DifferenceLogicDecisionProcedure::setupEdge(Constraint c){
  ArithVar v = c->getVariable();
  VertexId start, end;
  if(d_differenceVariables.isKey(v)){
    ArithVar x, y;
    std::pair<ArithVar, ArithVar> p = d_differenceVariables[v];
    if(c->isUpperBound()){
      // e.start - e.end <= c
      x = p.first;
      y = p.second;
    }else{
      // e.start - e.end >= c
      // e.end - e.start <= -c
      x = p.second;
      y = p.first;
    }
    setupArithVarIfNeeded(x);
    setupArithVarIfNeeded(y);

    start = arithVarToVertexId(x);
    end = arithVarToVertexId(y);
  }else{
    setupArithVarIfNeeded(v);

    if(c->isUpperBound()){
      // x <= c
      // x - ZeroVar <= c
      start = arithVarToVertexId(v);
      end = getZeroVertex();
    } else {
      // x >= c
      // ZeroVar - x <= -c
      start = getZeroVertex();
      end = arithVarToVertexId(v);
    }
  }
  EdgeId eid = d_graph.addEdge(start, end, c);
  return eid;
}

  void DifferenceLogicDecisionProcedure::setupArithVarIfNeeded(ArithVar v){
    if(d_av2vid.find(v) == d_av2vid.end()){
      VertexId vid = d_graph.addVertex(v);
      d_av2vid[v] = vid;
    }
  }

bool DifferenceLogicDecisionProcedure::check(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_dlCheckTimer);
  while(!d_queue.empty()){
    Assert(!inConflict());

    Constraint c = d_queue.front();
    d_queue.pop();

    EdgeId eid = setupEdge(c);

    bool incrementalResIsSat = setTrue(eid);

    if(incrementalResIsSat){
      summarizePiPrimeIntoPi();
      Assert(d_gamma.heapEmpty());
      d_gamma.purge();
    }else{
      NodeBuilder<> nb(kind::AND);
      VertexId start = d_graph.getEdge(eid).getStart();
      explainCycle(start, nb);
      Node conflict = nb;

      Debug("dl::conflict") << "DL conflict: " << conflict << std::endl;

      raiseConflict(conflict);

      d_piSummary.purge();
      d_piPrime.purge();
      d_gamma.purge();

      return false;
    }
  }
  return true;
}

DifferenceLogicDecisionProcedure::DifferenceLogicDecisionProcedure(context::Context* c, const ArithPartialModel& pm, NodeCallBack& raiseConflict):
    d_pm(pm),
    d_raiseConflict(raiseConflict),
    d_inConflict(c),
    d_graph(c),
    d_zeroVertex(c),
    d_queue(c),
    d_av2vid(c),
    d_gamma()
  {
  }

  DifferenceLogicDecisionProcedure::Statistics::Statistics():
    d_dlConflicts("theory::arith::dl::conflicts", 0),
    d_dlCheckTimer("theory::arith::dl::checkTimer")
  {
    StatisticsRegistry::registerStat(&d_dlConflicts);
    StatisticsRegistry::registerStat(&d_dlCheckTimer);
  }

  DifferenceLogicDecisionProcedure::Statistics::~Statistics(){
    StatisticsRegistry::unregisterStat(&d_dlConflicts);
    StatisticsRegistry::unregisterStat(&d_dlCheckTimer);
  }

 void DifferenceLogicDecisionProcedure:: raiseConflict(Node conflict){
   Assert(!inConflict());
   ++d_statistics.d_dlConflicts;
   d_raiseConflict(conflict);
   d_inConflict.raise();
 }



  

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

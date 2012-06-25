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

  d_gamma.update(v_id, getPi(u_id) + d - getPi(v_id), eid );
  // everything else is implicitly 0

  while(true){
    if(d_gamma.getValue(u_id).sgn() != 0){
      return false;
    }else if(d_gamma.heapEmpty()){
      return true;
    }

    VertexId s = d_gamma.heapMinimum();
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

        // if(d_gamma.isKey(t)){
        //   const DeltaRational& curr = d_gamma[t];
        //   if(theta < curr){
        //     d_gamma.set(t, theta);
        //     d_gammaProof.set(t, eid);
        //     if(d_gammaHeap.isMember(t)){
        //       d_gammaHeap.decrease_key(t);
        //     }else{
        //       d_gammaHeap.insert(t);
        //     }
        //   }
        // }else if(theta.sgn() < 0){
        //   d_gamma[t] = theta;
        //   d_gammaProof[t] = eid;

        //   Assert(!d_gammaHeap.isMember(t));
        //   d_gammaHeap.insert(t);
        // }
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
    Edge e = d_differenceVariables[v];
    if(c->isUpperBound()){
      // e.start - e.end <= c
      start = e.getStart();
      end = e.getEnd();
    }else{
      // e.start - e.end >= c
      // e.end - e.start <= -c
      start = e.getEnd();
      end = e.getStart();
    }
  }else{
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

bool DifferenceLogicDecisionProcedure::check(){

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

      Debug("dl::conflict") << conflict << std::endl;

      raiseConflict(conflict);

      d_piSummary.purge();
      d_piPrime.purge();
      d_gamma.purge();

      return false;
    }
  }
  return true;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

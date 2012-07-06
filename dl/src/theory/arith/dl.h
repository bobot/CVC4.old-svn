/*********************                                                        */
/*! \file dl.h
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
 ** \brief Decision procedure for difference logic.
 **
 ** Implementation of incremental Bellman-Ford potential moving decision
 ** procedure for difference logic.
 ** See Cotton and Maler.
 **/

#include "cvc4_private.h"
#pragma once

#include "context/cdgraph.h"
#include "context/cdmaybe.h"
#include "context/cdqueue.h"
#include "util/dense_map.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/constraint.h"
#include <boost/heap/pairing_heap.hpp>

namespace CVC4 {
namespace theory {
namespace arith {

class DifferenceLogicDecisionProcedure {
private:

  typedef context::EdgeId EdgeId;
  typedef context::VertexId VertexId;
  typedef context::Edge Edge;
  typedef context::Vertex Vertex;
  typedef context::EdgeIdVector EdgeIdVector;

  /** Source of the current model. */
  const ArithPartialModel& d_pm;

  /** Callback to TheoryArith to notify it of a conflict.*/
  NodeCallBack& d_raiseConflict;

  /** A Boolean flag for raising whether a conflict has been detected.*/
  context::CDRaised d_inConflict;

  bool inConflict() const {
    return d_inConflict.isRaised();
  }

  void raiseConflict(Node conflict);

  /** The difference graph. */
  context::CDGraph<ArithVar, Constraint> d_graph;

  context::CDMaybe<VertexId> d_zeroVertex;

  context::CDQueue<Constraint> d_queue;

  VertexId getZeroVertex(){
    if(!d_zeroVertex.isSet()){
      d_zeroVertex.set(d_graph.addVertex(ARITHVAR_SENTINEL));
    }
    return d_zeroVertex.get();
  }


  /** VertexId |-> ... */
  DenseMap<DeltaRational> d_piSummary;
  DenseMap<DeltaRational> d_piPrime;
  //GammaMap d_gamma;

  //ArithVar |-> VertexId
  context::CDHashMap<ArithVar, VertexId> d_av2vid;
  void setupArithVarIfNeeded(ArithVar v);

  ArithVar vertexIdToArithVar(VertexId vid) const{
    return d_graph.getVertexAnnotation(vid);
  }
  VertexId arithVarToVertexId(ArithVar var) const {
    return (*(d_av2vid.find(var))).second;
  }

  //ArithVar s |-> (x -> y) where s = x - y
  DenseMap<std::pair<ArithVar, ArithVar> > d_differenceVariables;

 public:
  void addDifference(ArithVar s, ArithVar x, ArithVar y){
    d_differenceVariables.set(s, std::make_pair(x,y));
  }
 private:
  ArithVar getPositive(ArithVar s) const{
    return d_differenceVariables[s].first;
  }
  ArithVar getNegative(ArithVar s) const{
    return d_differenceVariables[s].second;
  }

  DeltaRational getPi(VertexId vid) const {
    if(d_piSummary.isKey(vid)){
      return d_piSummary[vid];
    }else{
      ArithVar var = vertexIdToArithVar(vid);
      const DeltaRational& model = d_pm.getSafeAssignment(var);
      return (-model);
    }
  }

  class Gamma {
  private:
    struct GammaElement;
    struct GammaGreaterThan {
      int operator()(const GammaElement* a, const GammaElement* b) const;
    };

    typedef boost::heap::pairing_heap<GammaElement*, boost::heap::compare<GammaGreaterThan> > GammaHeapInternal;

    struct GammaElement {
      VertexId d_id;

      DeltaRational d_value;
      EdgeId d_edge;

      bool d_inHeap;
      GammaHeapInternal::handle_type d_heapHandle;


      GammaElement(){}

      GammaElement(VertexId vid, const DeltaRational& v, EdgeId eid):
        d_id(vid),
        d_value(v),
        d_edge(eid),
        d_inHeap(false)
      {}

      bool operator<(const GammaElement& other) const{
        return this->d_value < other.d_value;
      }
    };

    typedef DenseMap<GammaElement> GammaMap;
    GammaMap d_map;

    GammaHeapInternal d_heapInternal;

    DeltaRational d_zeroDelta;

    bool inMap(VertexId vid) const{
      return d_map.isKey(vid);
    }

    bool inHeap(VertexId vid) const{
      Assert(inMap(vid));
      return d_map[vid].d_inHeap;
    }

  public:
    Gamma() :
      d_map(),
      d_heapInternal()
    {}

    bool heapEmpty() const {
      return d_heapInternal.empty();
    }

    VertexId heapMinimum() const {
      Assert(!heapEmpty());
      GammaElement* e = d_heapInternal.top();
      return e->d_id;
    }

    void heapPop() {
      Assert(!heapEmpty());
      GammaElement* e = d_heapInternal.top();
      e->d_inHeap = false;
      d_heapInternal.pop();
    }

    void update(VertexId v, const DeltaRational& value, EdgeId eid) {
      if(!inMap(v)){
        d_map.set(v, GammaElement(v, value, eid));
        GammaElement& ge = d_map.get(v);
        ge.d_heapHandle = d_heapInternal.push(&ge);
        ge.d_inHeap = true;
      }else{
        GammaElement& ge = d_map.get(v);
        Assert(v == ge.d_id);
        ge.d_value = value;
        ge.d_edge = eid;
        if(inHeap(v)){
          d_heapInternal.update(ge.d_heapHandle);
        }else{
          ge.d_heapHandle = d_heapInternal.push(&ge);
        }
        ge.d_inHeap = true;
      }
    }
    void updateIfMin(VertexId t, const DeltaRational& theta, EdgeId eid){
      if(inMap(t)){
        const DeltaRational& curr = d_map[t].d_value;
        if(theta < curr){
          update(t, theta, eid);
        }
      }else if(theta.sgn() < 0){
        update(t, theta, eid);
      }
    }

    void purge(){
      d_map.purge();
      d_heapInternal.clear();
    }

    bool completelyEmpty() const {
      Assert(!d_map.empty() || heapEmpty());
      return d_map.empty();
    }

    const DeltaRational& getValue(VertexId vid) const{
      if(inMap(vid)){
        return d_map[vid].d_value;
      }else{
        return d_zeroDelta;
      }
    }

    EdgeId getEdgeId(VertexId vid) const{
      Assert(inMap(vid));
      return d_map[vid].d_edge;
    }

    void clearValue(VertexId vid){
      Assert(inMap(vid));
      Assert(!inHeap(vid));
      d_map.get(vid).d_value = d_zeroDelta;
    }

  } d_gamma;

 public:
  DifferenceLogicDecisionProcedure(context::Context* c, const ArithPartialModel& pm, NodeCallBack& raiseConflict);

  /** Returns Sat::Result */
  bool setTrue(EdgeId eid);

  void explainCycle(VertexId first, NodeBuilder<>& out);

  //DenseMap<Edge> d_differenceVariables;

  DeltaRational constraintValue(EdgeId eid) const {
    const Constraint c = d_graph.getEdgeAnnotation(eid);
    if(c->isLowerBound()){
      return - c->getValue();
    } else {
      return c->getValue();
    }
  }

  void initializeInputVariable(ArithVar v);
  void initializeSlack(ArithVar slack, ArithVar pos, ArithVar neg);

  EdgeId setupEdge(Constraint c);
  bool check();
#warning "support equalities"
  void enqueueConstraint(Constraint c) {
    Debug("dl::enqueue") << c << std::endl;
    d_queue.push_back(c);
  }

  void summarizePiPrimeIntoPi() {
    while(!d_piPrime.empty()){
      VertexId back = d_piPrime.back();
      d_piSummary.set(back, d_piPrime[back]);
      d_piPrime.pop_back();
    }

    Assert(d_piPrime.empty());
  }

  void printPi() const {
    for(DenseMap<DeltaRational>::const_iterator iter = d_piSummary.begin(), end = d_piSummary.end(); iter != end; ++iter){
      VertexId vid = *iter;
      std::cout << "pi[" << vid << "] -> " << d_piSummary[vid] << std::endl;
    }
  }

  class Statistics {
  public:
    IntStat d_dlConflicts;

    TimerStat d_dlCheckTimer;

    Statistics();
    ~Statistics();
  } d_statistics;
}; /* class CVC4::theory::arith::DifferenceLogicDecisionProcedure */


inline int DifferenceLogicDecisionProcedure::Gamma::GammaGreaterThan::operator()(const GammaElement* a, const GammaElement* b) const{
  return b->d_value < a->d_value;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

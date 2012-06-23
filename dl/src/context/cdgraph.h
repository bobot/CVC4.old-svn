/*********************                                                        */
/*! \file cdgraph.h
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

#include "cvc4_private.h"
#pragma once

#include "src/context/cdlist.h"
#include "src/util/index.h"
#include <vector>


namespace CVC4 {
namespace context {

typedef Index EdgeId;
typedef Index VertexId;

class Edge {
private:
  EdgeId d_id;
  VertexId d_start;
  VertexId d_end;

public:
  Edge(EdgeId eid, VertexId start, VertexId end) :
    d_id(eid), d_start(start), d_end(end)
  {}

  EdgeId getId() const {
    return d_id;
  }
  VertexId getStart() const{
    return d_start;
  }
  VertexId getEnd() const{
    return d_end;
  }

  bool operator==(const Edge& e) const {
    return
      this->getStart() == e.getStart() &&
      this->getEnd() == e.getEnd();
  }
}; /* class CVC4::context::Edge */

typedef std::vector<EdgeId> EdgeIdVector;

class Vertex {
private:
  VertexId d_id;

  EdgeIdVector d_incomingEdges;
  EdgeIdVector d_outgoingEdges;

public:
  Vertex(VertexId vid) : d_id(vid) {}

  VertexId getId() const {
    return d_id
  }

  const EdgeIdVector& getIncomingEdges() const {
    return d_incomingEdges;
  }
  const EdgeIdVector& getOutgoingEdges() const{
    return d_outgoingEdges;
  }

  bool noEdges() const {
    return d_incomingEdges.empty() && d_outgoingEdges.empty();
  }
}; /* class CVC4::context::Vertex */

template <class EdgeAnnotation>
class CDGraph {
private:
  typename std::vector<Vertex> VertexVector;
  VertexVector d_vertices;

  size_t d_permanentlyAllocatedNodes;

  /** Ensures that the VertexId v can is valid. */
  void extendVeriticesToInclude(VertexId v){
    while(d_vertices.size() <= v){
      VertexId vid = d_nodes.size();
      d_vertices.push_back(Vertex(vid));
    }
  }

  /** Garbage collects all of the nodes. */
  static void garbageCollectVectices(VertexVector& vertices){
    while(vertices.size() > d_permanentlyAllocatedNodes){
      if(vertices.back().noEdges()){
        vertices.pop_back();
      }else{
        break;
      }
    }
  }

  class EdgeCleanup{
    VertexVector& d_vertices;
    EdgeCleanup(VertexVector& vertices) :
      d_vertices(vertices)
    {}

    void operator()(Edge* e){
      Assert(d_vertices[e->getEnd()].d_incomingEdges.back() == *e);
      d_vertices[e->getEnd()].d_incomingEdges.pop_back();

      Assert(d_vertices[e->getStart()].d_outgoingEdges.back() == *e);
      d_vertices[e->getStart()].d_outgoingEdges.pop_back();

      garbageCollectVectices(d_vertices);
    }
  };

  /**
   * The list of edges in the current context.
   * This functions as a map from EdgeId to Edges.
   */
  CDList< EdgeClass, EdgeCleanup > d_edges;

  /**
   * The list of annotations to edges in the current context.
   *
   * This functions as a map from EdgeId to Edges.
   * This is kept in sync with d_edges.
   */
  CDList< EdgeAnnotation > d_annotations; //edge ids to annotation

public:
  CDGraph(Context* c, size_t permantentlyAllocatedNodes = 0) :
    d_vertices(),
    d_permantentlyAllocatedNodes(permantentlyAllocatedNodes),
    d_edges(c, callDestructor, EdgeCleanup(d_vertices))
  {
    Assert(d_vertices.size() == d_vertexSentinel);
    if(d_permantentlyAllocatedNodes > 0){
      extendVeriticesToInclude(d_permantentlyAllocatedNodes - 1);
    }
  }

  EdgeId addEdge(VertexId start, VertexId end, const EdgeAnnotation& annotation = EdgeAnnotation()){
    EdgeId eid = d_edges.size();
    d_edges.push_back(Edge(id, start, end));
    d_annotations.push_back(annotation);

    extendVeriticesToInclude( std::max(start,end) );
    Assert(d_vertices.size() > start);
    Assert(d_vertices.size() > end);

    d_nodes[start].d_outgoingEdges.push_back(eid);
    d_nodes[end].d_incomingEdges.push_back(eid);
    return eid;
  }

  const Vertex& getVertex(VertexId vid) const {
    Assert(vid < d_vertices.size());
    return d_vertices[vid];
  }

  const EdgeClass& getEdge(EdgeId eid) const{
    Assert(eid < d_edges.size());
    return d_edges[eid];
  }

  const EdgeAnnotation& getEdgeAnnotation(EdgeId eid) const{
    Assert(eid < d_annotations.size());
    return d_annotations[eid];
  }
}; /* class CVC4::context::CDGraph<EdgeAnnotation> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#include <boost/heap/pairing_heap.hpp>

namespace CVC4 {
namespace theory {
namespace arith {

/** A preliminary implementation of Cotton and Maler. */
class DifferenceLogicDecisionProcedure {
private:

  /** Source of the current model. */
  const ArithPartialModel& d_pm;

  /** Callback to TheoryArith to notify it of a conflict.*/
  NodeCallBack& d_raiseConflict;

  /** A Boolean flag for raising whether a conflict has been detected.*/
  CDRaise d_inConflict;

  /** The difference graph. */
  context::CDGraph<Constraint> d_graph;

  /**
   * The special zero node in the graph.
   * This is a permanent node in the graph.
   */
  VertexId d_zeroVertex;


  /** VertexId |-> ... */
  DenseMap<DeltaRational> d_piSummary;
  DenseMap<DeltaRational> d_piPrime;
  DenseMap<DeltaRational> d_gamma;
  DenseMap<EdgeID> d_gammaEdge;

  ArithVar vertexIdToArithVar(VertexId vid) const;
  VertexId arithVarToVertexId(ArithVar var) const;

  DeltaRational getPi(VertexId vid) const {
    if(d_piSummary.isKey(vid)){
      return d_piSummary[vid];
    }else{
      ArithVar var = vertexIdToArithVar(vid);
      const DeltaRational& model = d_pm.getAssignment(var);
      return (-model);
    }
  }

  class GammaHeap {
  private:
    struct GammaGreaterThan{
      const DenseMap<DeltaRational>& d_gamma;
      GammaGreaterThan(const DenseMap<DeltaRational>& gamma) :
        d_gamma(gamma)
      {}
      inline int cmp(VertexId v, VertexId u) const{
        Assert(d_gamma.isKey(v));
        Assert(d_gamma.isKey(u));
        const DeltaRational& gamma_v = d_gamma[v];
        const DeltaRational& gamma_u = d_gamma[u];
        return gamma_u.cmp(gamma_v);
      }
    } d_gammaGT;

    typedef pairing_heap<VertexId, > GammaHeapInternal;
    GammaHeapInternal d_heapInternal;
    DenseMap<GammaHeap::handle_type> reverseHeap;

  public:
    VertexId minimum() const;
    void remove_minimum();
    void decrease_key(VertexId v);
    void insert(VertexId v);
    bool isInHeap(VertexId v) const;

    bool isEmpty();
  } d_minGammaHeap;

  DifferenceLogicDecisionProcedure(Context* c, ArithVar zeroVariable):
    d_pm(pm),
    d_graph(c, 1),
    d_raiseConflict(raiseConflict),
    d_minGammaHeap(d_gamma){
  }

  /** Returns Sat::Result */

  bool setTrue(EdgeId eid){
    Edge e = getEdge(eid);
    VertexId u_id = e.getStart();
    VertexId v_id = e.getEnd();
    DeltaRational d = constraintValue(d_graph.getAnnotation(eid));

    d_gamma.set(v_id, getPi(u_id) + d - getPi(v_id));
    d_gammaProof[v_id] = e.getId();

    // everything else is implicitly 0
    d_gammaHeap.insert(v_id);

    while(true){
      if(d_gamma.isKey(u_iv) && d_gamma[u].sgn() != 0){
        return false;
      }else if(d_gammaHeap.empty()){
        return true;
      }

      VertexId s = d_gammaHeap.top();
      Assert(d_gamma.isKey(s));
      Assert(d_gamma[s].sgn() < 0);

      d_gammaHeap.pop();

      d_piPrime[s] = getPi(s) + d_gamma[s];
      d_gamma.remove(s); // set to 0

      const Node& s_node = d_graph.getNode(s);

      const EdgeIdVector& s_outgoing = s_node.getOutgoingEdges();
      EdgeIdVector::const_iterator s_iter = s_outgoing.begin(), s_end = s_outgoing.end();
      for(; s_iter != s_end; ++s_iter){
        EdgeId eid = *s_iter;
        const Edge& e = d_graph.getEdge(eid);
        Assert(eid.getStart() == s);
        NodeId t = e.getOutgoing();
        if(!d_piPrime.isKey(t)){
          Constraint constraint = d_graph.getAnnotation(eid);
          DeltaRational c = constraintValue(constraint);
          DeltaRational theta = d_piPrime[s] + c - getPi(t);

          if(d_gamma.isKey(t)){
            const DeltaRational& curr = d_gamma[t];
            if(theta < curr){
              d_gamma.set(t, theta);
              d_gammaProof.set(t, eid);
              if(d_gammaHeap.isMember(t)){
                d_gammaHeap.decrease_key(t);
              }else{
                d_gammaHeap.insert(t);
              }
            }
          }else if(theta.sgn() < 0){
            d_gamma[t] = theta;
            d_gammaProof[t] = eid;

            Assert(!d_gammaHeap.isMember(t));
            d_gammaHeap.insert(t);
          }
        }
      }
    }
  }

  void explainCycle(NodeId first, vector<Constraint>& out){

    NodeId current = first;
    do{
      EdgeId currEdge = d_gammaProof(current);

      out.push_back(d_graph.getExplanation(currEdge));
      const Edge& e = d_graph.getEdge(currEdge);

      NodeId next = e.getStart();

      current = next;
    }while(currStart != first);
  }

  struct DifferenceArithVar{
  private:
    ArithVar d_first;
    ArithVar d_second;
  };

  DeltaRational constraintValue(const Constraint c) const {
    if(c->isLowerBound()){
      return - c->getValue();
    } else {
      return c->getValue();
    }
  }

  void initializeInputVariable(ArithVar v);
  void initializeSlack(ArithVar slack, ArithVar pos, ArithVar neg);

  EdgeId setupEdge(Constraint c){
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
        start = arithVarToVertexId(s);
        end = d_zeroVariable;
      } else {
        // x >= c
        // ZeroVar - x <= -c
        start = d_zeroVariable;
        end = arithVarToVertexId(s);
      }
    }
    EdgeId eid = d_graph.addEdge(start, end, c);
    return eid;
  }

  bool check(){

    while(!d_queue.empty()){
      Assert(!inConflict());

      Constraint c = d_queue.front();
      d_queue.pop();

      EdgeId eid = setupEdge(c);

      bool incrementalResIsSat = setTrue(eid);

      if(incrementalResIsSat){
        summarizePiPrimeIntoPi();
        Assert(d_gammaHeap.empty());
        d_gamma.purge();
        d_gammaEdge.purge();
      }else{
        vector<Constraint> cycle;
        VertexId start = d_graph.getEdge(eid).getStart();
        explainCycle(start);
        Node conflict = Constraint::explainConflict(cycle);

        Debug("dl::conflict") << conflict << endl;

        d_inConflict.raise();
        d_raiseConflict(conflict);

        d_pi.purge();
        d_piPrime.purge();
        d_gamma.purge();
        d_gammaEdge.purge();
        d_gammaHeap.clear();

        return false;
      }
    }
    return true;
  }


  void enqueueConstraint(Constraint c) {
    Debug("dl::enqueue") << c << endl;
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
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

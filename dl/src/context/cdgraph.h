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
 ** \brief Context-dependent directed graph implemented via adjacency lists.
 **
 ** Context dependent direct graph implemented via adjacency lists.
 **
 ** The graph is technically a multigraph as multiple edges between the
 ** same ordered pairs of vertices can be added.
 **/

#pragma once

#include "cvc4_private.h"
#include "context/cdlist.h"
#include "util/index.h"
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
  Vertex(VertexId vid)
    : d_id(vid)
  {}

  VertexId getId() const {
    return d_id;
  }

  const EdgeIdVector& getIncomingEdges() const {
    return d_incomingEdges;
  }
  EdgeIdVector& getIncomingEdges() {
    return d_incomingEdges;
  }
  const EdgeIdVector& getOutgoingEdges() const{
    return d_outgoingEdges;
  }

  EdgeIdVector& getOutgoingEdges(){
    return d_outgoingEdges;
  }

  bool noEdges() const {
    return d_incomingEdges.empty() && d_outgoingEdges.empty();
  }
}; /* class CVC4::context::Vertex */

template <class VertexAnnotation, class EdgeAnnotation>
class CDGraph {
private:

  /**
   * It is cleaner to not make this based on top of a CDList as we need access
   *
   */
  typedef std::pair<Vertex, VertexAnnotation> ExtendedVertex;
  typedef std::vector< ExtendedVertex > VertexVector;
  VertexVector d_vertices;
  
  class VertexCleanup {
  private:
    VertexVector& d_vertices;
  public:
  VertexCleanup(VertexVector& vertices) : d_vertices(vertices){}

    void operator()(VertexId* vp){
      Assert( (*vp) + 1 == d_vertices.size());
      Assert(d_vertices.back().first.getId() == *vp);
      d_vertices.pop_back();
    }
  };
  typedef context::CDList<VertexId, VertexCleanup> VertexCleanupVector;
  VertexCleanupVector d_vertexCleanupVector;

  bool validVertexId(VertexId vid) const {
    return vid < d_vertices.size();
  }

  /**
   * The list of edges with annotations in the current context.
   * This functions as a map from EdgeId to Edges.
   *
   */
  typedef std::pair<Edge, EdgeAnnotation> ExtendedEdge;
  typedef std::vector<ExtendedEdge> EdgeVector;
  EdgeVector d_edges;

  /**
   * Returns true iff the EdgeId refers to an edge in the current
   * context.
  */
  bool validEdgeId(EdgeId eid) const {
    return eid < d_edges.size();
  }

  class EdgeCleanup{
  private:
    VertexVector& d_vertices;
    EdgeVector& d_edges;

  public:
    EdgeCleanup(VertexVector& vertices, EdgeVector& edges) :
      d_vertices(vertices), d_edges(edges)
    {}

    void operator()(EdgeId* ep){
      EdgeId eid = *ep;
      Assert(eid + 1 == d_edges.size());
      Edge& e = d_edges[eid].first;
      VertexId endId = e.getEnd();
      //check to be independent of deletion order
      if(endId < d_vertices.size()){
        EdgeIdVector& end_incoming = d_vertices[endId].first.getIncomingEdges();
        Assert(end_incoming.back() == eid);
        end_incoming.pop_back();
      }
      VertexId startId = e.getStart();
      //check to be independent of deletion order
      if(startId < d_vertices.size()){
        EdgeIdVector& start_outgoing = d_vertices[startId].first.getOutgoingEdges();
        Assert(start_outgoing.back() == eid);
        start_outgoing.pop_back();
      }
      d_edges.pop_back();
    }
  };

  /** A vector for backtracking the changes made to d_edges.*/
  CDList< EdgeId, EdgeCleanup > d_edgeCleanupVector;


public:
 CDGraph(context::Context* c) :
    d_vertices(),
    d_vertexCleanupVector(c, true, VertexCleanup(d_vertices)),
    d_edges(),
    d_edgeCleanupVector(c, true, EdgeCleanup(d_vertices, d_edges))
  { }

  /** Adds a vertex with a new annotation to the current context. */
  VertexId addVertex(const VertexAnnotation& annotation = VertexAnnotation()){
    VertexId vid = d_vertices.size();
    d_vertices.push_back(std::make_pair(Vertex(vid), annotation));
    d_vertexCleanupVector.push_back(vid);

    return vid;
  }

  /**
   * Adds an edge between the start and end vertex with an annotation to
   * the current context. start and end must be valid in the current context.
   * Returns the id of the new edge.
   */
  EdgeId addEdge(VertexId start, VertexId end, const EdgeAnnotation& annotation = EdgeAnnotation()){
    Assert(validVertexId(start));
    Assert(validVertexId(end));

    EdgeId eid = d_edges.size();
    d_edges.push_back(std::make_pair(Edge(eid, start, end), annotation));
    d_edgeCleanupVector.push_back(eid);

    Vertex& start_v = d_vertices[start].first;
    Vertex& end_v = d_vertices[end].first;

    EdgeIdVector& start_outgoing = start_v.getOutgoingEdges();
    EdgeIdVector& end_incoming = end_v.getIncomingEdges();
    start_outgoing.push_back(eid);
    end_incoming.push_back(eid);
    return eid;
  }

  const Vertex& getVertex(VertexId vid) const {
    Assert(validVertexId(vid));
    return d_vertices[vid].first;
  }

  const VertexAnnotation& getVertexAnnotation(VertexId vid) const {
    Assert(validVertexId(vid));
    return d_vertices[vid].second;
  }

  const Edge& getEdge(EdgeId eid) const{
    Assert(validEdgeId(eid));
    return d_edges[eid].first;
  }

  const EdgeAnnotation& getEdgeAnnotation(EdgeId eid) const{
    Assert(validEdgeId(eid));
    return d_edges[eid].second;
  }
}; /* class CVC4::context::CDGraph<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

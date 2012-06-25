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
  struct VertexCleanUp {
    void operator()(Vertex** v){
      delete *v;
    }
  };
  typedef context::CDList<Vertex*, VertexCleanUp> VertexVector;
  VertexVector d_vertices;

  context::CDList<VertexAnnotation> d_vertexAnnotations;

  bool validVertexId(VertexId vid) const {
    return vid < d_vertices.size();
  }

  class EdgeCleanup{
  private:
    VertexVector& d_vertices;

  public:
    EdgeCleanup(VertexVector& vertices) :
      d_vertices(vertices)
    {}

    void operator()(Edge* e){
      VertexId end = e->getEnd();
      //check to be independent of deletion order
      if(end < d_vertices.size()){
        Vertex* end_p = static_cast<Vertex *>(d_vertices[end]);
        EdgeIdVector& end_incoming = end_p->getIncomingEdges();
        end_incoming.pop_back();
      }
      VertexId start = e->getStart();
      //check to be independent of deletion order
      if(start < d_vertices.size()){
        Vertex* start_p = static_cast<Vertex *>(d_vertices[start]);
        EdgeIdVector& start_outgoing = start_p->getOutgoingEdges();
        start_outgoing.pop_back();
      }
    }
  };

  /**
   * The list of edges in the current context.
   * This functions as a map from EdgeId to Edges.
   */
  CDList< Edge, EdgeCleanup > d_edges;

  /**
   * The list of annotations to edges in the current context.
   *
   * This functions as a map from EdgeId to Edges.
   * This is kept in sync with d_edges.
   */
  CDList< EdgeAnnotation > d_edgeAnnotations;


  /**
   * Returns true iff the EdgeId refers to an edge in the current
   * context.
  */
  bool validEdgeId(EdgeId eid) const {
    return eid < d_edges.size();
  }

public:
  CDGraph(Context* c) :
    d_vertices(c),
    d_vertexAnnotations(c),
    d_edges(c, true, EdgeCleanup(d_vertices)),
    d_edgeAnnotations(c)
  { }

  VertexId addVertex(const VertexAnnotation& annotation = VertexAnnotation()){
    VertexId vid = d_vertices.size();
    Vertex* v = new Vertex(vid);
    d_vertices.push_back(v);
    d_vertexAnnotations.push_back(annotation);
    return vid;
  }

  EdgeId addEdge(VertexId start, VertexId end, const EdgeAnnotation& annotation = EdgeAnnotation()){
    Assert(validVertexId(start));
    Assert(validVertexId(end));

    EdgeId eid = d_edges.size();
    d_edges.push_back(Edge(eid, start, end));
    d_edgeAnnotations.push_back(annotation);

    Vertex* start_p = static_cast<Vertex *>(d_vertices[start]);
    Vertex* end_p = static_cast<Vertex *>(d_vertices[end]);

    EdgeIdVector& start_outgoing = start_p->getOutgoingEdges();
    EdgeIdVector& end_incoming = end_p->getIncomingEdges();
    start_outgoing.push_back(eid);
    end_incoming.push_back(eid);
    return eid;
  }

  const Vertex& getVertex(VertexId vid) const {
    Assert(validVertexId(vid));
    return *d_vertices[vid];
  }

  const VertexAnnotation& getVertexAnnotation(VertexId vid) const {
    Assert(validVertexId(vid));
    return d_vertexAnnotations[vid];
  }

  const Edge& getEdge(EdgeId eid) const{
    Assert(validEdgeId(eid));
    return d_edges[eid];
  }

  const EdgeAnnotation& getEdgeAnnotation(EdgeId eid) const{
    Assert(validEdgeId(eid));
    return d_edgeAnnotations[eid];
  }
}; /* class CVC4::context::CDGraph<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

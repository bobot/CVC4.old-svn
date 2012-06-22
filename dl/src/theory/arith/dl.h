
#include <boost/heap/pairing_heap.hpp>

typedef Index EdgeId;
typedef Index NodeId;

typedef std::vector<EdgeId> EdgeIdVector;

class Edge {
private:
  EdgeId d_id;
  NodeId d_start;
  NodeId d_end;

public:

  EdgeId getId() const;
  NodeId getStart() const;
  NodeId getEnd() const;
};

class Node {
private:
  NodeId d_id;

  EdgeIdVector d_incomingEdges;
  EdgeIdVector d_outgoingEdges;

public:
  NodeId getId() const;

  bool noEdges() const {
    return d_incomingEdges.empty() && d_outgoingEdges.empty();
  }

  const EdgeIdVector& getIncomingEdges() const;
  const EdgeIdVector& getOutgoingEdges() const;
};

template<class Weight, class Explanation>
class CDGraph {
  std::vector<Node> d_nodes;
  EdgeIdVector d_emptyVector;
  // Keep an empty edge id vector in case someone requests an edge id vector for a node that is not set up.

  typename EdgeClass<Weight, Explanation> EdgeClass;

  static void gcNodes(std::vector<Node>& nodes){
    while(!nodes.empty()){
      if(nodes.back().noEdges()){
        nodes.pop_back();
      }else{
        break;
      }
    }
  }

  template <class EC>
  class EdgeCleanup{
    std::vector<Node>& d_nodes;
    void operator()(EC* e){
      Assert(d_nodes[e->end].d_incomingEdges.back() == *e);
      d_nodes[e->end].d_incomingEdges.pop_back();

      Assert(d_nodes[e->start].d_outgoingEdges.back() == *e);
      d_nodes[e->start].d_outgoingEdges.pop_back();

      gcNodes(d_nodes);
    }
  };

  CDList<EdgeClass, EdgeCleanup<EdgeClass> > d_edges; //edge ids to edges

  EdgeId addEdge(ArithVar start, ArithVar end, Constraint exp){
    EdgeId eid = d_edges.size();
    d_edges.push_back(Edge(id, start, end, exp));
    ArithVar max = max(start, end);
    while(d_nodes.size() < max){
      Node nid = d_nodes.size();
      d_nodes.push_back(Node(id));
    }
    d_nodes[start].d_outgoingEdges.push_back(eid);
    d_nodes[end].d_incomingEdges.push_back(eid);
  }

  const EdgeClass& getEdge(EdgeId eid){
    Assert(eid < d_edges.size());
    return d_edges[eid];
  }

  const Node& getNode(NodeId nid){
    Assert(nid < d_nodes.size());
    return d_nodes[nid];
  }
};

class DifferenceLogicDecisionProcedure{
  /** A preliminary implementation of Cotton and Maler */

  ArithPartialModel& d_pm; /** source of input constraints */

  NodeCallBack& d_raiseConflict; /** Callback to TheoryArith to nitfy it of a conflict.*/

  ArithVar d_zeroVar;

  DenseMap<DeltaRational> d_piPrime;
  DenseMap<DeltaRational> d_gamma;
  DenseMap<EdgeID> d_gammaEdge;

  struct GammaHeap {
    struct GammaGreaterThan{
      GammaGreaterThan(const DenseMap<DeltaRational>& gamma) :
        d_gamma(gamma)
      {}

      const DenseMap<DeltaRational>& d_gamma;
      int cmp(ArithVar v, ArithVar u){
        Assert(d_gamma.isKey(v));
        Assert(d_gamma.isKey(u));
        const DeltaRational& gamma_v = d_gamma.get(v);
        const DeltaRational& gamma_u = d_gamma.get(u);
        return gamma_u.cmp(gamma_v);
      }
    } d_gammaGT;

    typedef pairing_heap<ArithVar> GammaHeapInternal;
    GammaHeapInternal d_heapInternal;
    DenseMap<GammaHeap::handle_type> reverseHeap;

    ArithVar minimum() const;
    void remove_minimum();
    void decrease_key(ArithVar v);
    void insert(ArithVar v);
    bool isInHeap(ArithVar v) const;

    bool isEmpty();
  } d_minGammaHeap;

  DifferenceLogicDecisionProcedure():
    d_pm(pm),
    d_raiseConflict(raiseConflict),
    d_minGammaHeap(d_gamma){
  }

  /** Returns Sat::Result */

  bool setTrue(EdgeId eid){

    Edge e = getEdge(eid);
    NodeId u_id = e.getStart();
    NodeId v_id = e.getEnd();
    const DeltaRational& d = ...;


    d_gamma[v_id] = getPi(u_id) + d - getPi(v_id);
    d_gammaProof[v_id] = e.getId();

    // everything else is implicitly 0
    d_gammaHeap.insert(v_id);

    while(true){
      if(d_gamma.isKey(u_iv) && d_gamma[u].sgn() != 0){
        return Result::UNSAT;
      }else if(d_gammaHeap.empty()){
        return Result::SAT;
      }

      NodeId s = d_gammaHeap.top();
      Assert(d_gamma.isKey(s));
      Assert(d_gamma[s].sgn() < 0);

      d_gammaHeap.pop();

      d_piPrime[s] = getPi(s) + d_gamma[s];
      d_gamma.remove(s); // set to 0

      const Node& s_node = d_graph.getNode(s);

      const EdgeIdVector& s_outgoing = s_node.getOutgoingEdges();
      for(EdgeIdVector::const_iterator s_iter = s_outgoing.begin(), s_end = s_outgoing.end(); s_iter != s_end; ++s_iter){
        EdgeId eid = *s_iter;
        const Edge& e = d_graph.getEdge(eid);
        Assert(eid.getStart() == s);
        NodeId t = e.getOutgoing();
        if(!d_piPrime.isKey(t)){
          const DeltRational& c = d_graph.getWeight(eid);
          DeltaRational theta = d_piPrime(s) + c - getPi(t);

          if(d_gamma.isKey(t)){
            const DeltaRational& curr = d_gamma[t];
            if(theta < curr){
              d_gamma[t] = theta;
              d_gammaProof[t] = eid;
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

  void check(){

    while(!d_queue.empty()){
      Assert(!inConflict());

      Constraint c = d_queue.front();
      d_queue.pop();

      NodeId start = getStart(c);
      NodeId end = getEnd(c);
      const DeltaRational& dr = getDeltaRational(dr);

      EdgeId e = d_graph.addEdge(start, end, dr);

      bool incrementalResIsSat = setTrue(e);

      if(incrementalResIsSat){
        summarizePiPrimeIntoPi();
      }else{
        vector<Constraint> cycle;
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

        return;
      }
    }
  }
};

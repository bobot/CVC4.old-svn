/*********************                                                        */
/*! \file cdexplain_dag.h
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
 ** \brief Datastructure for keeping track of explanations in a context dependent fashion.
 **
 ** CDExplainDag is a lazy datastructure for keeping track of explanations in a context
 ** dependent fashion.
 ** The only thing that needs to be backtracked are array lengths.
 ** CDExplainDag supports asking for a proof done in at a context level,
 ** until a write is done at a lower context.
 ** The data-structure keeps hard references to nodes to support this.
 ** The data structure lazily garbage collects.
 **/
#include "cvc4_private.h"


#ifndef __CVC4__CDEXPLAIN_DAG_H
#define __CVC4__CDEXPLAIN_DAG_H

#include <vector>
#include <ext/hash_map>

#include "context/context.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace CVC4 {
namespace context {


class CDExplainDAG : ContextNotifyObj {
public:
  typedef uint32_t ProofIndex;
  typedef uint32_t FactIndex;

private:

  const ProofIndex SENTINEL;

  enum ProofNodeType {EMPTY_NODE, LEAF, CONS};

  struct ProofLeaf {
    FactIndex d_fi;
  };

  struct ProofCons {
    ProofIndex d_car, d_cdr;
  };


  class ProofNode {
  private:
    ProofNodeType d_type;
    union {
      ProofLeaf leaf;
      ProofCons cons;
    } d_u;

  public:
    ProofNodeType getType() const{
      return d_type;
    }
    FactIndex getFactIndex() const{
      Assert(d_type == LEAF);
      return d_u.leaf.d_fi;
    }

    ProofIndex getCar() const {
      Assert(d_type == CONS);
      return d_u.cons.d_car;
    }

    ProofIndex getCdr() const {
      Assert(d_type == CONS);
      return d_u.cons.d_cdr;
    }

    ProofNode() : d_type(EMPTY_NODE) { }

    ProofNode(FactIndex fi) : d_type(LEAF) {
      d_u.leaf.d_fi = fi;
    }
    ProofNode(ProofIndex car, ProofIndex cdr) : d_type(CONS){
      d_u.cons.d_car = car;
      d_u.cons.d_cdr = cdr;
    }
  };

  typedef std::vector<ProofNode> ProofNodeVec;
  typedef std::vector<Node> FactVec;
  typedef std::vector<ProofIndex> FactToProofVec;
  typedef std::hash_map<Node, FactIndex, NodeHashFunction> PosititionMap;

  bool d_writtenSinceLastPop;

  PosititionMap d_pm;
  ProofNodeVec d_pv;
  FactVec d_fv;
  FactToProofVec d_f2pv; // The size reserved is at least as large as d_fv



  CDO<FactIndex> d_lastActiveFact;
  CDO<ProofIndex> d_lastActiveProof;

  void gc(){
    Assert(shouldGarbageCollect());

    d_pm.clear();
    for(FactIndex i = 0; i < d_lastActiveFact; i++){
      d_pm[d_fv[i]] = i;
    }

    d_fv.resize(d_lastActiveFact);
    d_f2pv.resize(d_lastActiveFact);
    d_pv.resize(d_lastActiveProof);

    Assert(d_pm.size() == d_lastActiveFact);
  }

  bool shouldGarbageCollect() const{
    return (16*((uint64_t)d_pm.size())) > (uint64_t) d_lastActiveFact;
  }

  void gcIfNeeded() {
    if(shouldGarbageCollect()){
      gc();
    }
  }

  FactIndex push_fact_internal(Node fact){
    Assert(!hasFact(fact));

    d_writtenSinceLastPop = true;

    gcIfNeeded();

    FactIndex nextFI = d_lastActiveFact+1;

    d_fv.reserve(nextFI);
    d_f2pv.reserve(nextFI);

    d_fv[nextFI] = fact;
    d_pm[fact] = nextFI;

    d_lastActiveFact = nextFI;
    return nextFI;
  }

  ProofIndex push_proof_leaf_internal(FactIndex fi){
    Assert(factIndexInRange(fi));

    d_writtenSinceLastPop = true;

    ProofIndex nextPI = d_lastActiveProof+1;

    d_pv.reserve(nextPI);

    d_pv[nextPI] = ProofNode(fi);
    d_lastActiveProof = nextPI;
    return nextPI;
  }


  ProofIndex push_proof_binary_internal(ProofIndex pi, ProofIndex pj){
    Assert(proofIndexInRange(pi));
    Assert(proofIndexInRange(pj));

    d_writtenSinceLastPop = true;

    ProofIndex nextPI = d_lastActiveProof+1;

    d_pv.reserve(nextPI);

    d_pv[nextPI] = ProofNode(pi, pj);
    d_lastActiveProof = nextPI;
    return nextPI;
  }

  ProofIndex push_proof_singleton(ProofIndex pi){
    return push_proof_binary_internal(pi, SENTINEL);
  }

  /**
   * This reduces a 
   */
  ProofIndex push_proof_large(const std::vector<ProofIndex>& pis){
    //TODO this can be made more efficient
    Assert(pis.size() >= 2);

    Assert(proofIndexInRange(pis[0]));
    Assert(proofIndexInRange(pis[1]));

    ProofIndex prev = push_proof_binary_internal(pis[0], pis[1]);

    typedef std::vector<ProofIndex>::const_iterator PIS_ITER;
    for(PIS_ITER iter = pis.begin()+2, end = pis.end(); iter != end; ++iter){
      ProofIndex curr = *iter;
      Assert(proofIndexInRange(curr));
      push_proof_binary_internal(prev, curr);
    }

    return prev;
  }

  bool mappedFact(Node fact) const {
    return d_pm.find(fact) != d_pm.end();
  }

  FactIndex mapFact(Node fact) const{
    Assert(mappedFact(fact));
    return (d_pm.find(fact))->second;
  }

  void enqueueLeaves(ProofIndex start, NodeBuilder<>& nb) const;


  bool proofIndexInRange(ProofIndex i) const{
    return i <= d_lastActiveProof;
  }
  bool factIndexInRange(FactIndex i) const{
    return i <= d_lastActiveProof;
  }

public:
  CDExplainDAG(Context* c);

  ~CDExplainDAG() throw() {  }

  void notify() {
    d_writtenSinceLastPop = false;
  }

  /**
   * See the comments for explain(Node fact).
   */
  Node explain(ProofIndex start) const{
    Assert(!d_writtenSinceLastPop || factIndexInRange(start));

    NodeBuilder<> nb(kind::AND);
    enqueueLeaves(start, nb);
    if(nb.getNumChildren() == 1){
      return nb[0];
    }else{
      return nb;
    }
  }


  /**
   * Returns the explanation for a Node in the current context or
   * there have been no writes to the DAG since the last context.
   * The explanation is a flat (and [e_i]) node.
   * Each e_i node is self explaining, i.e. it was asserted using push_fact(Node fact).
   * This explanation may contain duplicates.
   */
  Node explain(Node fact) const {
    Assert(mappedFact(fact));

    ProofIndex start = d_f2pv[mapFact(fact)];
    return explain(start);
  }


  /**
   * Returns true if fact is a member of the DAG in context.
   */
  bool hasFact(Node fact) const{
    if(mappedFact(fact)){
      FactIndex i = mapFact(fact);
      return factIndexInRange(i) && d_fv[i] == fact;
    }else{
      return false;
    }
  }

  /**
   * Returns the FactIndex of a node in the DAG.
   */
  FactIndex getFactIndex(Node fact) const{
    Assert(hasFact(fact));
    return mapFact(fact);
  }

  /**
   * Returns the ProofIndex of a node in the DAG.
   */
  ProofIndex getProofIndex(Node fact) const{
    Assert(hasFact(fact));
    return d_f2pv[getFactIndex(fact)];
  }


  /**
   * Add the node, fact, to the DAG with the explanation fact,
   * i.e. fact is it's own explanation.
   * fact cannot already be a member of the DAG.
   */
  ProofIndex push_fact(Node fact){
    FactIndex fi = push_fact_internal(fact);
    ProofIndex pi = push_proof_leaf_internal(fi);
    d_f2pv[fi] = pi;
    return pi;
  }

  /**
   * Add the node, phi, to the DAG with the explanation a.
   * phi cannot already be a member of the DAG.
   */
  ProofIndex push_implication(Node phi, ProofIndex a){
    Assert(!hasFact(phi));
    Assert(proofIndexInRange(a));

    FactIndex fi = push_fact(phi);
    ProofIndex pi = push_proof_singleton(a);
    d_f2pv[fi] = pi;
    return pi;
  }

  /**
   * Add the node, phi, to the DAG with the explanation (and a b).
   * phi cannot already be a member of the DAG.
   */
  ProofIndex push_implication(Node phi, ProofIndex a, ProofIndex b){
    Assert(!hasFact(phi));
    Assert(proofIndexInRange(a));
    Assert(proofIndexInRange(b));

    FactIndex fi = push_fact_internal(phi);
    ProofIndex pi = push_proof_binary_internal(a,b);
    d_f2pv[fi] = pi;
    return pi;
  }

  /**
   * Add the node, phi, to the DAG with the explanation (and [pis]).
   * [pis] must have at least one element.
   * ()
   *
   * phi cannot already be a member of the DAG.
   */
  ProofIndex push_implication(Node phi, const std::vector<ProofIndex>& pis){
    Assert(pis.size() >= 1);
    switch(pis.size()){
    case 1:
      return push_implication(phi, pis[0]);
    case 2:
      return push_implication(phi, pis[0], pis[1]);
    default:
      {
        FactIndex fi = push_fact_internal(phi);
        ProofIndex pi = push_proof_large(pis);
        d_f2pv[fi] = pi;
        return pi;
      }
    }
  }

};


}/* context namespace */

}/* CVC4 namespace */

#endif /* __CVC4__EXPLANATION_FOREST_H */

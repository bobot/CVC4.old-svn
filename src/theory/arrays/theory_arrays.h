/*********************                                                        */
/*! \file theory_arrays.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of arrays.
 **
 ** Theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H

#include "theory/theory.h"
#include "theory/arrays/union_find.h"
#include "util/congruence_closure.h"
#include <ext/hash_set>
#include <iostream>
#include <map>
namespace CVC4 {
namespace theory {
namespace arrays {

class TheoryArrays : public Theory {

private:
  class CongruenceChannel {
    TheoryArrays* d_arrays;

  public:
    CongruenceChannel(TheoryArrays* arrays) : d_arrays(arrays) {}
    void notifyCongruent(TNode a, TNode b) {
      d_arrays->notifyCongruent(a, b);
    }
  }; /* class CongruenceChannel*/
  friend class CongruenceChannel;

  /**
   * Output channel connected to the congruence closure module.
   */
  CongruenceChannel d_ccChannel;

  /**
   * Instance of the congruence closure module.
   */
  CongruenceClosure<CongruenceChannel, CONGRUENCE_OPERATORS_2 (kind::SELECT, kind::STORE)> d_cc;

  /**
   * Union find for storing the equalities.
   */

  UnionFind<Node, NodeHashFunction> d_unionFind;

  /**
   * Received a notification from the congruence closure algorithm that the two nodes
   * a and b have been merged.
   */

  /**
   * set of store terms
   */
  std::set<TNode> d_stores;

  /**
   * set of select terms
   */

  std::set<TNode> d_selects;

  void notifyCongruent(TNode a, TNode b);

  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > CTNodeListAlloc;
  typedef context::CDList<TNode> CTNodeList;
  typedef context::CDMap<Node, CTNodeListAlloc*, NodeHashFunction> CNodeTNodesMap;

  /**
   * List of all disequalities this theory has seen.
   * Maintaints the invariant that if a is in the
   * disequality list of b, then b is in that of a.
   * */
  CNodeTNodesMap d_disequalities;

  /** List of all (potential) equalities to be propagated. */
  CNodeTNodesMap d_equalities;

  /**
   * stores the conflicting disequality (still need to call construct
   * conflict to get the actual explanation)
   */
  Node d_conflict;

  /**
   * true constant (sometimes check gets called on a CONST_BOOLEAN)
   */
  Node d_true_const;


  /**
   * Small class encapsulating the information
   * in the map. It's a class and not a struct to
   * call the destructor.
   */

  class Info {
  public:
    CTNodeList* indices;
    CTNodeList* eq_stores;
    CTNodeList* in_stores; //FIXME: maybe need only one store list
    Info(context::Context* c) {
      indices = new(true)CTNodeList(c);
      eq_stores = new(true)CTNodeList(c);
      in_stores = new(true)CTNodeList(c);
    }
    ~Info() {
      indices->deleteSelf();
      eq_stores->deleteSelf();
      in_stores->deleteSelf();
    }

    /**
     * debug method to print a lsit
     */

    static void printList(CTNodeList* list) {
      CTNodeList::const_iterator it = list->begin();
      Debug("arrays-mergei")<<"   [ ";
      for(; it != list->end(); it++ ) {
        Debug("arrays-mergei")<<(*it)<<" ";
      }
      Debug("arrays-mergei")<<"] \n";
    }

    void print() {
      Assert(indices != NULL && eq_stores!= NULL && in_stores != NULL);
      Debug("arrays-mergei")<<"  indices   ";
      printList(indices);
      Debug("arrays-mergei")<<"  eq_stores ";
      printList(eq_stores);
      Debug("arrays-mergei")<<"  in_stores ";
      printList(in_stores);
    }
  };

  /**
   * Structure keeping track of the following information for canonical
   * representatives of type array [a] :
   *    indices at which it is being read (all i for which there is a
   *            term of the form SELECT a i)
   *    all store terms in the congruence class
   *    stores in which it appears (terms of the form STORE a _ _ )
   *
   */
  class ArrayInfo {
  private:
    context::Context* ct;
    typedef context::CDMap <Node, Info*, NodeHashFunction> CNodeInfoMap;
    CNodeInfoMap info_map;
    CTNodeList* emptyList;

    /**
     * checks if a certain element is in the list l
     */
    bool inList(CTNodeList* l, TNode el) {
      CTNodeList::const_iterator it = l->begin();
      for ( ; it!= l->end(); it ++) {
        if(*it == el)
          return true;
      }
      return false;
    }

    /**
     * helper method that merges two lists into the first
     * without adding duplicates
     */
    void mergeLists(CTNodeList* la, CTNodeList* lb) {
      std::set<TNode> temp;
      CTNodeList::const_iterator it;
      for(it = la->begin() ; it != la->end(); it++ ) {
        temp.insert((*it));
      }

      for(it = lb->begin() ; it!= lb->end(); it++ ) {
        if(temp.count(*it) == 0) {
          la->push_back(*it);
        }
      }
    }

  public:
    ArrayInfo(context::Context* c): ct(c), info_map(ct) {
      emptyList = new(true) CTNodeList(ct);
    }
    ~ArrayInfo(){
      CNodeInfoMap::iterator it = info_map.begin();
      for( ; it != info_map.end(); it++ ) {
        delete (*it).second;
      }
      emptyList->deleteSelf();
    };

    /**
     * adds the node a to the map if it does not exist
     * and it initializes the info. checks for duplicate i's
     */
    void addIndex(const Node a, const TNode i) {
      Assert(a.getType().isArray());
      Assert(!i.getType().isArray()); // temporary for flat arrays

      CTNodeList* temp_indices;
      Info* temp_info;

      CNodeInfoMap::iterator it = info_map.find(a);
      if(it == info_map.end()) {
        temp_indices = new(true) CTNodeList(ct);
        temp_indices->push_back(i);

        temp_info = new Info(ct);
        temp_info->indices = temp_indices;

        info_map.insert(a, temp_info);
      } else {
        temp_indices = (*it).second->indices;
        if(! inList(temp_indices, i)) {
          temp_indices->push_back(i);
        }
      }

    }

    void addEqStore(const Node a, const TNode st){
      Assert(a.getType().isArray());
      Assert(st.getKind()== kind::STORE); // temporary for flat arrays

      CTNodeList* temp_eqstore;
      Info* temp_info;

      CNodeInfoMap::iterator it = info_map.find(a);
      if(it == info_map.end()) {
        temp_eqstore = new(true) CTNodeList(ct);
        temp_eqstore->push_back(st);

        temp_info = new Info(ct);
        temp_info->eq_stores = temp_eqstore;
        info_map.insert(a, temp_info);
      } else {
        temp_eqstore = (*it).second->eq_stores;
        if(! inList(temp_eqstore, st)) {
          temp_eqstore->push_back(st);
        }
      }
    };

    void addInStore(const Node a, const TNode st){
      Assert(a.getType().isArray());
      Assert(st.getKind()== kind::STORE); // temporary for flat arrays

      CTNodeList* temp_instore;
      Info* temp_info;

      CNodeInfoMap::iterator it = info_map.find(a);
      if(it == info_map.end()) {
        temp_instore = new(true) CTNodeList(ct);
        temp_instore->push_back(st);

        temp_info = new Info(ct);
        temp_info->in_stores = temp_instore;
        info_map.insert(a, temp_info);
      } else {
        temp_instore = (*it).second->in_stores;
        if(! inList(temp_instore, st)) {
          temp_instore->push_back(st);
        }
      }
    };


    /**
     * returns the
     */

    CTNodeList* getIndices(TNode a) {
      CNodeInfoMap::iterator it = info_map.find(a);
      if(it!= info_map.end()) {
        return (*it).second->indices;
      }
      return emptyList;
    }

    CTNodeList* getInStores(TNode a) {
      CNodeInfoMap::iterator it = info_map.find(a);
      if(it!= info_map.end()) {
        return (*it).second->in_stores;
      }
      return emptyList;
    }

    CTNodeList* getEqStores(TNode a) {
      CNodeInfoMap::iterator it = info_map.find(a);
      if(it!= info_map.end()) {
        return (*it).second->eq_stores;
      }
      return emptyList;
    }



    /**
     * merges the information of  nodes a and b
     * the nodes do not have to actually be in the map.
     * pre-condition
     *  a should be the canonical representative of b
     */
    void mergeInfo(TNode a, TNode b){
      // can't have assertion that find(b) = a !

      Debug("arrays-mergei")<<"Arrays::mergeInfo merging "<<a<<"\n";
      Debug("arrays-mergei")<<"                      and "<<b<<"\n";


      CNodeInfoMap::iterator ita = info_map.find(a);
      CNodeInfoMap::iterator itb = info_map.find(b);
      if(ita != info_map.end()) {
        Debug("arrays-mergei")<<"Arrays::mergeInfo info "<<a<<"\n";
        (*ita).second->print();
        if(itb != info_map.end()) {
          Debug("arrays-mergei")<<"Arrays::mergeInfo info "<<b<<"\n";
          (*itb).second->print();
          CTNodeList* lista_i = (*ita).second->indices;
          CTNodeList* lista_inst = (*ita).second->in_stores;
          CTNodeList* lista_eqst = (*ita).second->eq_stores;

          CTNodeList* listb_i = (*itb).second->indices;
          CTNodeList* listb_inst = (*itb).second->in_stores;
          CTNodeList* listb_eqst = (*itb).second->eq_stores;

          mergeLists(lista_i, listb_i);
          mergeLists(lista_inst, listb_inst);
          mergeLists(lista_eqst, listb_eqst);
        }
      }
      Debug("arrays-mergei")<<"Arrays::mergeInfo merged info \n";
      (*ita).second->print();
    };
  };



ArrayInfo d_infoMap;

/**
 * must be called before a and b have been merged
 * i.e. before setCanon(a,b)
 */

void checkLemmas(const Node a, const Node b) {
  CTNodeList* i_a = d_infoMap.getIndices(a);
  CTNodeList* inst_b = d_infoMap.getInStores(b);
  CTNodeList* eqst_b = d_infoMap.getEqStores(b);

  CTNodeList::const_iterator it = i_a->begin();
  CTNodeList::const_iterator its;

  for( ; it != i_a->end(); it++ ) {
    TNode i = *it;
    its = inst_b->begin();
    for ( ; its != inst_b->end(); its++) {
      TNode store = *its;
      Assert(store.getKind() == kind::STORE);
      TNode j = store[1];
      TNode c = store[0];

      NodeManager* nm = NodeManager::currentNM();
      TNode eq1 = nm->mkNode(kind::EQUAL, i, j);
      TNode cj = nm->mkNode(kind::SELECT, c, j);
      TNode aj = nm->mkNode(kind::SELECT, a, j);
      TNode eq2 = nm->mkNode(kind::EQUAL, cj, aj);

      // TODO add check if lemma exists and if any of the disjuncts are already
      // true
      addLemma(nm->mkNode(kind::OR, eq1, eq2));
    }

    its = eqst_b->begin();
    for ( ; its != eqst_b->end(); its++) {
      TNode store = *its;
      Assert(store.getKind() == kind::STORE);
      TNode j = store[1];
      TNode c = store[0];

      NodeManager* nm = NodeManager::currentNM();
      TNode eq1 = nm->mkNode(kind::EQUAL, i, j);
      TNode cj = nm->mkNode(kind::SELECT, c, j);
      TNode aj = nm->mkNode(kind::SELECT, a, j);
      TNode eq2 = nm->mkNode(kind::EQUAL, cj, aj);

      // TODO add check if lemma exists and if any of the disjuncts are already
      // true
      addLemma(nm->mkNode(kind::OR, eq1, eq2));
    }


  }

}

  /**
   * Marking stores and reads that have been already registered
   */
  //struct ArrayPreRegisteredId {};
  //typedef expr::Attribute<ArrayPreRegisteredId, bool> ArrayRegistered;

  /*
   * Helper methods
   */

  void addDiseq(TNode diseq);
  void appendToDiseqList(TNode of, TNode eq);
  void appendToEqList(TNode of, TNode eq);
  Node constructConflict(TNode diseq);

  /**
   * Merges two congruence classes in the internal
   * union-find and checks for a conflict.
   */

  void merge(TNode a, TNode b);
  inline TNode find(TNode a);
  inline TNode debugFind(TNode a) const;

  inline void setCanon(TNode a, TNode b);
  inline void addLemma(TNode lem) {
    Debug("arrays-lem")<<"TheoryArrays::addLemma "<<lem<<"\n";
    d_out->lemma(lem);
  }


public:
  TheoryArrays(context::Context* c, OutputChannel& out);
  ~TheoryArrays();

  void preRegisterTerm(TNode n) {
    Debug("arrays-preregister")<<"TheoryArrays::preRegisterTerm "<<n<<"\n";

    switch(n.getKind()) {
    case kind::SELECT:
      //d_selects.insert(n);
      d_infoMap.addIndex(n[0], n[1]);
      break;
    case kind::STORE:
    {
      //d_stores.insert(n);
      d_infoMap.addEqStore(n, n);
      d_infoMap.addInStore(n[0], n);

      //FIXME: maybe can keep track of these
      TNode b = n[0];
      TNode i = n[1];
      TNode v = n[2];
      NodeManager* nm = NodeManager::currentNM();
      Node ni = nm->mkNode(kind::SELECT, n, i);
      Node eq = nm->mkNode(kind::EQUAL, ni, v);
      addLemma(eq);
      d_cc.addEquality(eq);
      break;
    }
    default:
      Debug("darrays")<<"Arrays::preRegisterTerm \n";
    }

  }

  void registerTerm(TNode n) {
    Debug("arrays-register")<<"TheoryArrays::registerTerm "<<n<<"\n";
  }

  void presolve() { }

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void check(Effort e);
  void propagate(Effort e) { }
  void explain(TNode n) { }
  Node getValue(TNode n, Valuation* valuation);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryArrays"); }
};/* class TheoryArrays */

inline void TheoryArrays::setCanon(TNode a, TNode b) {
  d_unionFind.setCanon(a, b);
}

inline TNode TheoryArrays::find(TNode a) {
  return d_unionFind.find(a);
}

inline TNode TheoryArrays::debugFind(TNode a) const {
  return d_unionFind.debugFind(a);
}



}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H */

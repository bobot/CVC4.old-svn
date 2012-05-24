/*********************                                                        */
/*! \file theory_uf.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__THEORY_UF_H
#define __CVC4__THEORY__UF__THEORY_UF_H

#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/symmetry_breaker.h"

#include "context/cdo.h"
#include "context/cdhashset.h"

namespace CVC4 {
namespace theory {
namespace uf {

class UfTermDb;
class InstantiatorTheoryUf;
class StrongSolverTheoryUf;

class TheoryUF : public Theory {
  friend class InstantiatorTheoryUf;
  friend class StrongSolverTheoryUf;
public:

  class NotifyClass : public eq::EqualityEngineNotify {
    TheoryUF& d_uf;
  public:
    NotifyClass(TheoryUF& uf): d_uf(uf) {}

    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      Debug("uf") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
      if (value) {
        return d_uf.propagate(equality);
      } else {
        // We use only literal triggers so taking not is safe
        return d_uf.propagate(equality.notNode());
      }
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Debug("uf") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false" )<< ")" << std::endl;
      if (value) {
        return d_uf.propagate(predicate);
      } else {
       return d_uf.propagate(predicate.notNode());
      }
    }

    //AJR-hack
    void notifyEqClass( TNode t ){
      d_uf.notifyEqClass( t );
    }
    void preNotifyMerge( TNode t1, TNode t2 ){
      d_uf.preNotifyMerge( t1, t2 );
    }
    void postNotifyMerge( TNode t1, TNode t2 ){
      d_uf.postNotifyMerge( t1, t2 );
    }
    void notifyDisequal( TNode t1, TNode t2, TNode reason ){
      d_uf.notifyDisequal( t1, t2, reason );
    }
    //AJR-hack-end

    bool eqNotifyTriggerTermEquality(TNode t1, TNode t2, bool value) {
      Debug("uf") << "NotifyClass::eqNotifyTriggerTermMerge(" << t1 << ", " << t2 << std::endl;
      if (value) {
        return d_uf.propagate(t1.eqNode(t2));
      } else {
        return d_uf.propagate(t1.eqNode(t2).notNode());
      }
    }

    bool eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      Debug("uf") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << std::endl;
      if (Theory::theoryOf(t1) == THEORY_BOOL) {
        return d_uf.propagate(t1.iffNode(t2));
      } else {
        return d_uf.propagate(t1.eqNode(t2));
      }
    }
  };

private:

  /** The notify class */
  NotifyClass d_notify;

  //AJR-hack
  /** associated theory strong solver */
  StrongSolverTheoryUf* d_thss;
  //AJR-hack-end

  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;

  /** Are we in conflict */
  context::CDO<bool> d_conflict;

  /** The conflict node */
  Node d_conflictNode;

  /**
   * Should be called to propagate the literal. We use a node here 
   * since some of the propagated literals are not kept anywhere. 
   */
  bool propagate(TNode literal);

  /**
   * Explain why this literal is true by adding assumptions
   */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  /** All the function terms that the theory has seen */
  context::CDList<TNode> d_functionsTerms;

  /** Symmetry analyzer */
  SymmetryBreaker d_symb;

//AJR-hack
  /** called when a new equivalance class is created */
  void notifyEqClass( TNode t );

  /** called when two equivalance classes will merge */
  void preNotifyMerge( TNode t1, TNode t2 );

  /** called when two equivalance classes have merged */
  void postNotifyMerge( TNode t1, TNode t2 );

  /** called when two equivalence classes are made disequal */
  void notifyDisequal( TNode t1, TNode t2, TNode reason );
//AJR-hack-end
public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUF(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe);

  void check(Effort);
  void propagate(Effort);
  void preRegisterTerm(TNode term);
  Node explain(TNode n);

  void ppStaticLearn(TNode in, NodeBuilder<>& learned);
  void presolve();

  void addSharedTerm(TNode n);
  void computeCareGraph();

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  std::string identify() const {
    return "THEORY_UF";
  }

  //AJR-hack
  eq::EqualityEngine* getEqualityEngine() { return &d_equalityEngine; }
  StrongSolverTheoryUf* getStrongSolver() { return d_thss; }
  //AJR-hack-end


  //FB-hack
  Node ppRewrite(TNode node);

  class PpRewrite {
  public:
    virtual Node ppRewrite(TNode node) = 0;

  };

  typedef std::hash_map< Node, PpRewrite*, NodeHashFunction > RegisterPpRewrite;
   RegisterPpRewrite d_registeredPpRewrite;

  void registerPpRewrite(TNode op, PpRewrite * callback){
    d_registeredPpRewrite.insert(std::make_pair(op,callback));
  }

  ~TheoryUF(){
    for(RegisterPpRewrite::iterator i = d_registeredPpRewrite.begin();
        i != d_registeredPpRewrite.end(); ++i)
      delete(i->second);
  }
  //FB-hack-end

};/* class TheoryUF */

class EqClassesIterator
{
private:
  eq::EqualityEngine* d_ee;
  size_t d_it;
public:
  EqClassesIterator(){}
  EqClassesIterator( eq::EqualityEngine* ee ) : d_ee( ee ){
    d_it = 0;
    //for( int i=0; i<(int)d_ee->d_nodesCount; i++ ){
    //  std::cout << "{" << d_ee->d_nodes[i] << "}";
    //}
    //std::cout << std::endl;
    if( d_it<d_ee->d_nodesCount && d_ee->getRepresentative( d_ee->d_nodes[d_it] )!= d_ee->d_nodes[d_it] ){
      (*this)++;
    }
  }
  Node operator*() { return d_ee->d_nodes[d_it]; }
  bool operator==(const EqClassesIterator& i) {
    return d_ee == i.d_ee && d_it == i.d_it;
  }
  bool operator!=(const EqClassesIterator& i) {
    return !(*this == i);
  }
  EqClassesIterator& operator++() {
    Node orig = d_ee->d_nodes[d_it];
    ++d_it;
    while( d_it<d_ee->d_nodesCount && ( d_ee->getRepresentative( d_ee->d_nodes[d_it] )!= d_ee->d_nodes[d_it] ||
           d_ee->d_nodes[d_it]==orig ) ){    //this line is necessary for ignoring duplicates
      ++d_it;
    }
    return *this;
  }
  EqClassesIterator operator++(int) {
    EqClassesIterator i = *this;
    ++*this;
    return i;
  }
  bool isFinished() { return d_it>=d_ee->d_nodesCount; }
};

class EqClassIterator
{
private:
  Node d_rep;
  eq::EqualityNode d_curr;
  Node d_curr_node;
  eq::EqualityEngine* d_ee;
public:
  EqClassIterator(){}
  EqClassIterator( Node eqc, eq::EqualityEngine* ee ) : d_ee( ee ){
    Assert( d_ee->getRepresentative( eqc )==eqc );
    d_rep = eqc;
    d_curr_node = eqc;
    d_curr = d_ee->getEqualityNode( eqc );
  }
  Node operator*() { return d_curr_node; }
  bool operator==(const EqClassIterator& i) {
    return d_ee == i.d_ee && d_curr_node == i.d_curr_node;
  }
  bool operator!=(const EqClassIterator& i) {
    return !(*this == i);
  }
  EqClassIterator& operator++() {
    Node next = d_ee->d_nodes[ d_curr.getNext() ];
    Assert( d_rep==d_ee->getRepresentative( next ) );
    if( d_rep!=next ){    //we end when we have cycled back to the original representative
      d_curr_node = next;
      d_curr = d_ee->getEqualityNode( d_curr.getNext() );
    }else{
      d_curr_node = Node::null();
    }
    return *this;
  }
  EqClassIterator operator++(int) {
    EqClassIterator i = *this;
    ++*this;
    return i;
  }
  bool isFinished() { return d_curr_node==Node::null(); }
};


}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_H */

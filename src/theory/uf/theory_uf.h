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
    void eqNotifyNewClass( TNode t ){
      d_uf.eqNotifyNewClass( t );
    }
    void eqNotifyPreMerge( TNode t1, TNode t2 ){
      d_uf.eqNotifyPreMerge( t1, t2 );
    }
    void eqNotifyPostMerge( TNode t1, TNode t2 ){
      d_uf.eqNotifyPostMerge( t1, t2 );
    }
    void eqNotifyDisequal( TNode t1, TNode t2, TNode reason ){
      d_uf.eqNotifyDisequal( t1, t2, reason );
    }
    //AJR-hack-end

    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
      Debug("uf") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << std::endl;
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
  void eqNotifyNewClass( TNode t );

  /** called when two equivalance classes will merge */
  void eqNotifyPreMerge( TNode t1, TNode t2 );

  /** called when two equivalance classes have merged */
  void eqNotifyPostMerge( TNode t1, TNode t2 );

  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal( TNode t1, TNode t2, TNode reason );
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

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_H */

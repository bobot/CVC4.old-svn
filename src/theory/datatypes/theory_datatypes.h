/*********************                                                        */
/*! \file theory_datatypes.h
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
 ** \brief Theory of datatypes.
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H
#define __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H

#include "theory/theory.h"
#include "util/congruence_closure.h"
#include "theory/datatypes/union_find.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {
namespace theory {
namespace datatypes {

class TheoryDatatypes : public Theory {
private:
  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > EqList;
  typedef context::CDMap<Node, EqList*, NodeHashFunction> EqLists;

  //a list of types with the list of constructors for that type
  std::map<TypeNode, std::vector<TypeNode> > d_cons;
  //a list of types with the list of constructors for that type
  std::map<TypeNode, std::vector<TypeNode> > d_testers;
  // the distinguished ground term for each type
  std::map< TypeNode, Node > d_distinguishTerms;
  //finite datatypes/constructor
  std::map< TypeNode, bool > d_finite;
  //well founded datatypes/constructor
  std::map< TypeNode, bool > d_wellFounded;
  //whether we need to check finite and well foundedness
  bool requiresCheckFiniteWellFounded;
  //Type getType( TypeNode t );
  int getConstructorIndex( TypeNode t, TypeNode t );
  int getTesterIndex( TypeNode t, TypeNode t );
  bool isDatatype( TypeNode t ) { return d_cons.find( t )!=d_cons.end(); }
  void checkFiniteWellFounded();

  //for possible constructors, map from terms to tester asserted for that term
  EqLists d_labels;

  class CongruenceChannel {
    TheoryDatatypes* d_datatypes;

  public:
    CongruenceChannel(TheoryDatatypes* datatypes) : d_datatypes(datatypes) {}
    void notifyCongruent(TNode a, TNode b) {
      d_datatypes->notifyCongruent(a, b);
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
  CongruenceClosure<CongruenceChannel, CONGRUENCE_OPERATORS_2 (kind::APPLY_CONSTRUCTOR, kind::APPLY_SELECTOR)> d_cc;

  /**
   * Union find for storing the equalities.
   */
  UnionFind<Node, NodeHashFunction> d_unionFind;

  /**
   * Received a notification from the congruence closure algorithm that the two nodes
   * a and b have been merged.
   */
  void notifyCongruent(TNode a, TNode b);

  /**
   * List of all disequalities this theory has seen.
   * Maintaints the invariant that if a is in the
   * disequality list of b, then b is in that of a.
   * */
  EqLists d_disequalities;

  /** List of all (potential) equalities to be propagated. */
  EqLists d_equalities;

  /**
   * stores the conflicting disequality (still need to call construct
   * conflict to get the actual explanation)
   */
  Node d_conflict;
public:
  TheoryDatatypes(int id, context::Context* c, OutputChannel& out);
  ~TheoryDatatypes();
  void preRegisterTerm(TNode n) { }
  void registerTerm(TNode n) { }

  RewriteResponse preRewrite(TNode in, bool topLevel);
  RewriteResponse postRewrite(TNode in, bool topLevel);

  void presolve();

  void addDatatypeDefinitions( std::vector<std::pair< Type, std::vector<Type> > >& cons,
                               std::vector<std::pair< Type, std::vector<Type> > >& testers );

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void check(Effort e);
  void propagate(Effort e) { }
  void explain(TNode n, Effort e) { }
  Node getValue(TNode n, TheoryEngine* engine);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryDatatypes"); }

  /* Helper methods */
  void checkTester( Effort e, Node tassertion, Node assertion );

  /* from uf_morgan */
  void merge(TNode a, TNode b);
  inline TNode find(TNode a);
  inline TNode debugFind(TNode a) const;
  void appendToDiseqList(TNode of, TNode eq);
  void appendToEqList(TNode of, TNode eq);
  void addDisequality(TNode eq);
  void registerEqualityForPropagation(TNode eq);
  Node constructConflict(TNode diseq);

};/* class TheoryDatatypes */

inline TNode TheoryDatatypes::find(TNode a) {
  return d_unionFind.find(a);
}

inline TNode TheoryDatatypes::debugFind(TNode a) const {
  return d_unionFind.debugFind(a);
}


}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H */

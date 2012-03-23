/*********************                                                        */
/*! \file constraint.h
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
 ** \brief Defines Constraint and ConstraintDatabase which is the internal representation of variables in arithmetic
 **
 ** This file defines Constraint and ConstraintDatabase.
 ** A Constraint is the internal representation of literals in TheoryArithmetic.
 ** Constraints are fundamentally a triple:
 **  - ArithVar associated with the constraint,
 **  - a DeltaRational value,
 **  - and a ConstraintType.
 **
 ** Literals:
 **   The constraint may also keep track of a node corresponding to the Constraint.
 **   This can be accessed by getLiteral() in O(1) if it has been set.
 **   This node must be in normal form and may be used for communication with the TheoryEngine.
 **
 ** In addition, Constraints keep track of the following:
 **  - A Constrain that is the negation of the Constraint.
 **  - An iterator into a set of Constraints for the ArithVar sorted by DeltaRational value.
 **  - A context dependent internal proof of the node that can be used for explanations.
 **  - Whether an equality/disequality has been split in the user context via a lemma.
 **  - Whether a constraint, be be used in explanations sent to the context
 **
 ** Looking up constraints:
 **  - All of the Constraints with associated nodes in the ConstraintDatabase can be accessed via
 **    a single hashtable lookup until the Constraint is removed.
 **  - Nodes that have not been associated to a constraints can be inserted/associated to existing nodes in O(log n) time.
 **
 ** Implications:
 **  - A Constraint can be used to find unate implications.
 **  - A unate implication is an implication based purely on the ArithVar matching and the DeltaRational value.
 **    (implies (<= x c) (<= x d)) given c <= d
 **  - This is done using the iterator into the sorted set of constraints.
 **  - Given a tight constraint and previous tightest constraint, this will efficiently propagate internally.
 **
 ** Additing and Removing Constraints
 **  - Adding Constraints takes O(log n) time where n is the number of constraints associated with the ArithVar.
 **  - Removing Constraints takes O(1) time.
 **
 ** Internals:
 **  - Constraints are pointers to ConstraintValues.
 **  - Undefined Constraints are NullConstraint.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__CONSTRAINT_H
#define __CVC4__THEORY__ARITH__CONSTRAINT_H

#include "expr/node.h"

#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"

#include "theory/arith/arithvar.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/arith/delta_rational.h"

#include <vector>
#include <list>
#include <set>
#include <ext/hash_map>

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * The types of constraints.
 * The convex constraints are the constraints are LowerBound, Equality, and UpperBound.
 */
enum ConstraintType {LowerBound, Equality, UpperBound, Disequality};

/** Given a simplifiedKind this returns the corresponding ConstraintType. */
ConstraintType constraintTypeOfLiteral(Kind k);

class ConstraintValue;
typedef ConstraintValue* Constraint;
static Constraint NullConstraint = NULL;

typedef __gnu_cxx::hash_map<Node, Constraint, NodeHashFunction> NodetoConstraintMap;

class ConstraintDatabase;

typedef size_t ProofId;
static ProofId ProofIdSentinel = std::numeric_limits<ProofId>::max();

/** A ValueCollection binds together convex constraints that have the same delta rational value. */
class ValueCollection {
private:

  Constraint d_lowerBound;
  Constraint d_upperBound;
  Constraint d_equality;
  Constraint d_disequality;

public:
  ValueCollection()
    : d_lowerBound(NullConstraint),
      d_upperBound(NullConstraint),
      d_equality(NullConstraint),
      d_disequality(NullConstraint)
  {}

  static ValueCollection mkFromConstraint(Constraint c);

  bool hasLowerBound() const{
    return d_lowerBound != NullConstraint;
  }
  bool hasUpperBound() const{
    return d_upperBound != NullConstraint;
  }
  bool hasEquality() const{
    return d_equality != NullConstraint;
  }
  bool hasDisequality() const {
    return d_disequality != NullConstraint;
  }

  bool hasConstraintType(ConstraintType t) const;

  Constraint getLowerBound() const {
    Assert(hasLowerBound());
    return d_lowerBound;
  }
  Constraint getUpperBound() const {
    Assert(hasUpperBound());
    return d_upperBound;
  }
  Constraint getEquality() const {
    Assert(hasEquality());
    return d_equality;
  }
  Constraint getDisequality() const {
    Assert(hasDisequality());
    return d_disequality;
  }

  Constraint getConstraint(ConstraintType t) const;

  /** Returns true if any of the constraints are non-null. */
  bool empty() const;

  /**
   * Remove the constraint of the type t from the collection.
   * Returns true if the ValueCollection is now empty.
   * If true is returned, d_value is now NULL.
   */
  void remove(ConstraintType t);

  /**
   * Adds a constraint to the set.
   * The collection must not have a constraint of that type already.
   */
  void add(Constraint c);

  void push_into(std::vector<Constraint>& vec) const;


  Constraint nonNull() const;

  ArithVar getVariable() const;
  const DeltaRational& getValue() const;
};

/**
 * A Map of ValueCollections sorted by the associated DeltaRational values.
 *
 * Discussion:
 * While it is more natural to consider this a set, this cannot be a set as in sets
 * the type of both iterator and const_iterator in sets are "constant iterators".
 * We require iterators that dereference to ValueCollection&.
 *
 * See:
 * http://gcc.gnu.org/onlinedocs/libstdc++/ext/lwg-defects.html#103
 */
typedef std::map<DeltaRational, ValueCollection> SortedConstraintMap;
typedef SortedConstraintMap::iterator SortedConstraintMapIterator;

/** A Pair associating a variables and a Sorted ConstraintSet. */
struct PerVariableDatabase{
  ArithVar d_var;
  SortedConstraintMap d_constraints;

  // x ? c_1, x ? c_2, x ? c_3, ...
  // where ? is a non-empty subset of {lb, ub, eq}
  // c_1 < c_2 < c_3 < ...

  PerVariableDatabase(ArithVar v) : d_var(v), d_constraints() {}

  bool empty() const {
    return d_constraints.empty();
  }

  static bool IsEmpty(const PerVariableDatabase& p){
    return p.empty();
  }
};

class ConstraintValue {
private:
  /** The ArithVar associated with the constraint. */
  const ArithVar d_variable;

  /** The type of the Constraint. */
  const ConstraintType d_type;

  /** The DeltaRational value with the constraint. */
  const DeltaRational d_value;

  /** A pointer to the associated database for the Constraint. */
  ConstraintDatabase * d_database;

  /**
   * The node to be communicated with the TheoryEngine.
   *
   * This is not context dependent, but may be set once.
   *
   * This must be set if the constraint is preregistered.
   * This must be set if the constraint isSelfExplaining().
   * Otherwise, this may be null().
   */
  Node d_literal;

  /** Pointer to the negation of the Constraint. */
  Constraint d_negation;

  /**
   * This is true if the associated node has been preregistered.
   * Sat Context Dependent.
   * This is initially false.
   */
  bool d_preregistered;

  /**
   * This points at the proof for the constraint in the current context.
   * Sat Context Dependent.
   * This is initially ProofIdSentinel.
   */
  ProofId d_proof;

  /**
   * True if the equality has been split.
   * Only meaningful if ContraintType == Equality.
   * User Context Dependent.
   * This is initially false.
   */
  bool d_split;

  /**
   * Position in sorted constraint set for the variable.
   * Unset if d_type is Disequality.
   */
  SortedConstraintMapIterator d_variablePosition;

  friend class ConstraintDatabase;

  /**
   * This begins construction of a minimal constraint.
   *
   * This should only be called by ConstraintDatabase.
   *
   * Because of circular dependencies a Constraint is not fully valid until
   * initialize has been called on it.
   */
  ConstraintValue(ArithVar x,  ConstraintType t, const DeltaRational& v);

  /**
   * Destructor for a constraint.
   * This should only be called if safeToGarbageCollect() is true.
   */
  ~ConstraintValue();

  bool initialized() const;

  /**
   * This initializes the fields that cannot be set in the constructor due to
   * circular dependencies.
   */
  void initialize(ConstraintDatabase* db, SortedConstraintMapIterator v, Constraint negation);

  /**
   * Upon destruction this sets the d_proof field back to ProofIdSentinel.
   * While a constraint has a proof in the current sat context, it cannot be destroyed.
   */
  class ProofWatch {
  private:
    Constraint d_constraint;
  public:
    ProofWatch(Constraint c) : d_constraint(c) {}
    ~ProofWatch(){
      Assert(d_constraint->d_proof != ProofIdSentinel);
      d_constraint->d_proof = ProofIdSentinel;
    }
  };

  /**
   * Upon destruction this sets the d_preregistered field back to false.
   * While a constraint has been preregistered in the current sat context, it cannot be destroyed.
   */
  class PreregisteredWatch {
  private:
    Constraint d_constraint;
  public:
    PreregisteredWatch(Constraint c) : d_constraint(c) {}
    ~PreregisteredWatch(){
      Assert(d_constraint->d_preregistered);
      d_constraint->d_preregistered = false;
    }
  };

  /**
   * Upon destruction this sets the d_split field back to false.
   * While a constraint has been split in the current user context, it cannot be destroyed.
   */
  class SplitWatch {
  private:
    Constraint d_constraint;
  public:
    SplitWatch(Constraint c) : d_constraint(c){}
    ~SplitWatch(){
      Assert(d_constraint->d_split);
      d_constraint->d_split = false;
    }
  };

  /**
   * The internal assistance method for explain.
   * Pushes back an explanation that is acceptable to send to the sat solver.
   * nb is assumed to be an AND.
   */
  static void recExplain(NodeBuilder<>& nb, const ConstraintValue* const c);

  /** Returns true if the node is safe to garbage collect. */
  bool safeToGarbageCollect() const;

  /** Returns true if the node correctly corresponds to the constraint that is being set.*/
  bool sanityChecking(Node n) const;

  /** Returns a reference to the map for d_variable. */
  SortedConstraintMap& constraintSet();

public:

  ConstraintType getType() const {
    return d_type;
  }

  ArithVar getVariable() const {
    return d_variable;
  }

  const DeltaRational& getValue() const {
    return d_value;
  }

  bool isEquality() const{
    return d_type == Equality;
  }
  bool isDisequality() const{
    return d_type == Disequality;
  }
  bool isLowerBound() const{
    return d_type == LowerBound;
  }
  bool isUpperBound() const{
    return d_type == UpperBound;
  }

  bool isSplit() const {
    return d_split;
  }

  /**
   * Splits the node in the user context.
   * Returns a lemma that is assumed to be true fro the rest of the user context.
   * Constraint must be an equality or disequality.
   */
  Node split();

  bool isPreregistered() const {
    return d_preregistered;
  }


  void setPreregistered();


  bool hasLiteral() const {
    return !d_literal.isNull();
  }

  void setLiteral(Node n);

  Node getLiteral() const {
    Assert(hasLiteral());
    return d_literal;
  }

  bool isSelfExplaining() const;

  Node explain() const;

  bool hasProof() const {
    return d_proof != ProofIdSentinel;
  }
  bool negationHasProof() const {
    return d_negation->hasProof();
  }

  bool truthIsUnknown() const {
    return !hasProof() && !negationHasProof();
  }

private:
  /**
   * Marks the node as having a proof and being selfExplaining.
   * Neither the node nor its negation can have a proof.
   */
  void markAsTrue();

  /** Marks the node as having a proof a. */
  void markAsTrue(Constraint a);
  void markAsTrue(Constraint a, Constraint b);
  void markAsTrue(const std::vector<Constraint>& b);

  /** If the node has a proof do nothing, otherwise mark the node.*/
  void internalPropagate(Constraint a);

}; /* class ConstraintValue */

std::ostream& operator<<(std::ostream& o, const ConstraintValue& c);
std::ostream& operator<<(std::ostream& o, const Constraint c);
std::ostream& operator<<(std::ostream& o, const ConstraintType t);
std::ostream& operator<<(std::ostream& o, const ValueCollection& c);

class ConstraintDatabase {
private:
  /**
   * The map from ArithVars to their unique databases.
   * When the vector changes size, we cannot allow the maps to move so this
   * is a vector of pointers.
   */
  std::vector<PerVariableDatabase*> d_varDatabases;

  SortedConstraintMap& getVariableSCM(ArithVar v){
    Assert(variableDatabaseIsSetup(v));
    return d_varDatabases[v]->d_constraints;
  }

  /** Maps literals to constraints.*/
  NodetoConstraintMap d_nodetoConstraintMap;

  /**
   * A queue of propagated constraints.
   *
   * As Constraint are pointers, the elements of the queue do not require destruction.
   */
  context::CDQueue<Constraint> d_toPropagate;

  /**
   * Proof Lists.
   * Proofs are lists of valid constraints terminated by the first smaller sentinel value
   * in the proof list.
   * The proof at p in d_proofs[p] of length n is
   *  (NullConstraint, d_proofs[p-(n-1)], ... , d_proofs[p-1], d_proofs[p])
   * The proof at p corresponds to the conjunction:
   *  (and x_i)
   *
   * So the proof of a Constraint c corresponds to the horn clause:
   *  (implies (and x_i) c)
   * where (and x_i) is the proof at c.d_proofs.
   *
   * Constraints are pointers so this list is designed not to require any destruction.
   */
  context::CDList<Constraint> d_proofs;

  /** This is a special empty proof that is always a member of the list. */
  ProofId d_emptyProof;

  /**
   * The watch lists are collected together as they need to be garbage collected
   * carefully.
   */
  struct Watches{
    /**
     * Contains the exact list of atoms that have a proof.
     */
    context::CDList<ConstraintValue::ProofWatch> d_proofWatches;

    /**
     * Contains the exact list of atoms that have been preregistered.
     * This is a pointer as it must be destroyed before the elements of d_varDatabases.
     */
    context::CDList<ConstraintValue::PreregisteredWatch> d_preregisteredWatches;

    /**
     * Contains the exact list of atoms that have been preregistered.
     * This is a pointer as it must be destroyed before the elements of d_varDatabases.
     */
    context::CDList<ConstraintValue::SplitWatch> d_splitWatches;
    Watches(context::Context* satContext, context::Context* userContext);
  };
  Watches* d_watches;
  
  void pushPreregisteredWatch(Constraint c){
    d_watches->d_preregisteredWatches.push_back(ConstraintValue::PreregisteredWatch(c));
  }
  
  void pushSplitWatch(Constraint c){
    d_watches->d_splitWatches.push_back(ConstraintValue::SplitWatch(c));
  }

  void pushProofWatch(Constraint c){
    d_watches->d_proofWatches.push_back(ConstraintValue::ProofWatch(c));
  }

  /** Returns true if all of the entries of the vector are empty. */
  static bool emptyDatabase(const std::vector<PerVariableDatabase>& vec);

  /** Map from nodes to arithvars. */
  const ArithVarNodeMap& d_av2nodeMap;

  const ArithVarNodeMap& getArithVarNodeMap() const{
    return d_av2nodeMap;
  }

  Constraint allocateConstraintForLiteral(ArithVar v, Node literal);

  const context::Context * const d_satContext;
  const int d_satAllocationLevel;

  friend class ConstraintValue;

public:

  ConstraintDatabase( context::Context* satContext, context::Context* userContext, const ArithVarNodeMap& av2nodeMap);

  ~ConstraintDatabase();

  Constraint addLiteral(TNode lit);
  Constraint addAtom(TNode atom);

  /**
   * If hasLiteral() is true, returns the constraint.
   * Otherwise, returns NullConstraint.
   */
  Constraint lookup(TNode literal) const;

  /**
   * Returns true if the literal has been added to the database.
   * This is a hash table lookup.
   * It does not look in the database for an equivalent corresponding constraint.
   */
  bool hasLiteral(TNode literal) const;
  
  bool hasMorePropagations() const{
    return !d_toPropagate.empty();
  }

  TNode nextPropagation(){
    Assert(hasMorePropagations());

    Constraint p = d_toPropagate.front();
    d_toPropagate.pop();

    return p->getLiteral();
  }

  void addVariable(ArithVar v);
  bool variableDatabaseIsSetup(ArithVar v);
}; /* ConstraintDatabase */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__CONSTRAINT_H */

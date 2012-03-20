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
 ** This defines ArithVar which is the internal representation of variables in
 ** arithmetic. This is a typedef from uint32_t to ArithVar.
 ** This file also provides utilities for ArithVars.
 **/

/** Requirements:
 * Every atom:
 *  Assign a unique id to every atom.
 *  Store a proof of all atoms (in context).
 *  A context level for when it was last preregistered.
 *  Provide fast access to its negation.
 *  Produce explanations (in context).
 *
 * For each variable:
 *  A sorted set of bounds in the current context.
 *  This is ordered by DeltaRational values.
 *
 * For equalities:
 *  A bit stating whether it has been split (in the current context).
 *  A list of shared equalities that correspond to the atom.
 */

/**
 * The types of constraints.
 * The convex constraints are the constraints are LowerBound, Equality, and UpperBound.
 */
enum ConstraintType {LowerBound, Equality, UpperBound, Disequality};

class ConstraintValue;
typedef ConstraintValue* Constraint;
typedef std::list<Constraint> ConstraintList;
typedef ConstraintList::iterator ConstraintListIterator;


typedef hash_map<Node, Constraint> NodetoConstraintMap;
NodetoConstraintMap d_nodetoConstraintMap;

static Constraint NullConstraint = NULL;

typedef size_t ProofId;
static ProofId ProofIdSentinel = std::numeric_limits<ProofId>::max();

/** A ValueCollection binds together convex constraints that have the same delta rational value. */
struct ValueCollection {
public:
  const DeltaRational* d_value;

  Constraint d_lowerBound;
  Constraint d_upperBound;
  Constraint d_equality;

  ValueCollection(const DeltaRational& dr) : d_value(&d_dr) {}


  bool operator<(const ValueCollection& other) const {
    return (*d_value) < (*(other.d_value));
  }

  bool hasLowerBound() const{
    return d_lowerBound == NullConstraint;
  }
  bool hasUpperBound() const{
    return d_upperBound == NullConstraint;
  }
  bool hasEquality() const{
    return d_equality == NullConstraint;
  }

  static ValueCollection mkFromLowerBound(Constraint lb);
  static ValueCollection mkFromUpperBound(Constraint ub);
  static ValueCollection mkFromEquality(Constraint eq);

  static ValueCollection mkFromConstraint(Constraint c);
};

typedef std::set<ValueCollection> SortedConstraintSet;
typedef SortedConstraintSet::iterator SortedConstraintSetIterator;

class ConstraintDatabase;

class ConstraintValue {
private:

  /** The type of the Constraint. */
  ConstraintType d_type;

  /** The ArithVar associated with the constraint. */
  ArithVar d_variable;


  /** The DeltaRational value with the constraint. */
  DeltaRational d_value;

  /** A pointer to the associated database for the Constraint. */
  ConstraintDatabase* d_database;

  /**
   * The position of the constraint in the d_database.d_constraints.
   * The ConstraintValue must have this for efficient garbage collection.
   */
  ConstraintListIterator d_pos;

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
  SortedConstraintSetIterator d_variablePosition;

  friend class ConstraintDatabase;

  /**
   * This begins construction of a minimal constraint.
   *
   * This should only be called by ConstraintDatabase.
   *
   * Because of circular depdendencies a Constraint is not fully valid until
   * initialize has been called on it.
   */
  Constraint(ConstraintDatabase* db, ArithVar x, const DeltaRational& v, ConstraintType t);

  /** This initializes the fields that cannot be set in the constructor due to circular dependencies.*/
  void initialize(SortedConstraintSetIterator v, ConstraintListIterator pos, Constraint negation){
    d_variablePosition = v;
    d_pos = pos;
    d_negation = negation;
  }

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
      d_constraint->d_proof = ProofIDSentinel;
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
      d_constraint->d_split = false;
    }
  };

  static void recExplain(NodeBuilder<>& nb, Constraint c);

  /** Returns true if the node is safe to garbage collect. */
  bool safeToGarbageCollect() const;

public:

  ConstraintType getType() const {
    return d_type;
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


  void setPreregistered() {
    Assert(d_preregistered = false);
    d_database->d_preregisteredList.push_back(PreregisteredWatch(this));
    d_preregistered = true;
  }


  bool hasLiteral() const {
    return !d_literal.isNull();
  }

  void setLiteral(Node n) const {
    Assert(!hasLiteral());
    Assert(sanityChecking());
    d_literal = n;
  }

  Node getLiteral() const {
    Assert(hasLiteral());
    return d_literal;
  }

  bool isSelfExplaining() const {
    return d_proof != ProofSentinel && d_database->d_proofs[d_proof] == NullConstraint;
  }

  Node explain() const;


  const DeltaRational& getValue() const {
    return d_value;
  }
};

class ConstraintDatabase {
private:
  /** The list of constraints associated with the database. */
  ConstraintList d_constraints;

  /**
   * A queue of propagated constraints.
   *
   * As Constraint are pointers, the elements of the queue do not require destruction.
   */
  CDQueue<Constraint> d_toPropagate;

  /**
   * Proof Lists.
   * Proofs are lists of valid constraints terminated by the first smaller sentinel value
   * in the proof list.
   * The proof at p in d_proofs[p] is
   *  (NullConstraint, d_proofs[p-n], ... , d_proofs[p-1], d_proofs[p])
   * The proof at p corresponds to the conjunction:
   *  (and x_i)
   *
   * So the proof of a Constraint c corresponds to the horn clause:
   *  (implies (and x_i) c)
   * where (and x_i) is the proof at c.d_proofs.
   *
   * Constraints are pointers so this list is designed not to require any destruction.
   */
  CDList<Constraint> d_proofs;

  /** This is a special empty proof that is always a member of the list. */
  ProofId d_emptyProof;

  /** Contains the exact list of atoms that have a proof. */
  CDList<Constraint::ProofWatch> d_proofWatches;

  /** Contains the exact list of atoms that have been preregistered. */
  CDList<Constraint::PreregisterWatch> d_preregisteredWatches;

  /** Contains the exact list of atoms that have been preregistered. */
  CDList<Constraint::SplitWatch> d_splitWatches;

  struct PerVariableDatabase{
    ArithVar d_var;
    SortedConstraintSet d_constraints;

    // x ? c_1, x ? c_2, x ? c_3, ...
    // where ? is a non-empty subset of {lb, ub, eq}
    // c_1 < c_2 < c_3 < ...
  };
  std::vector<PerVariableDatabase> d_varDatabases;

  friend class ConstraintValue;

public:

  ConstraintDatabase(context::Context* cxt);

  Constraint addLiteral(TNode lit, ArithVar v);
  Constraint addAtom(TNode atom, ArithVar v);
  Constraint lookup(TNode literal);



  bool variableDatabaseIsSetup(ArithVar v);


};

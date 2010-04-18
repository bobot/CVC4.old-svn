
namespace CVC4 {
namespace theory {
namespace arith {

struct AssignmentAttrID;
typedef expr::Attribute<AssignmentAttrID, ExtendedRational> Assignment;

struct LowerBoundAttrID;
typedef expr::CDAttribute<LowerBoundAttrID,ExtendedRational> LowerBound;

struct UpperBoundAttrID;
typedef expr::CDAttribute<UpperBoundAttrID, ExtendedRational> UpperBound;

struct LowerConstraintAttrID;
typedef expr::CDAttribute<LowerConstraintAttrID,TNode> LowerConstraint;

struct UpperConstraintAttrID;
typedef expr::CDAttribute<UpperConstraintAttrID,TNode> UpperConstraint;

typedef CVC4::CDList<TNode> BoundsList;

struct BoundsListCleanupStrategy{
  static void cleanup(BoundsList* bl){
    Debug("arithgc") << "cleaning up  " << bl << "\n";
    dl->deleteSelf();
  }
};


/** Unique name to use for constructing ECAttr. */
struct BoundsListID;

/**
 * BoundsListAttr is the attribute that maps a node to atoms .
 */
typedef expr::Attribute<BoundsListID,
                        BoundsList*,
                        BoundsListCleanupStrategy> BoundsListAttr;


typedef TheoryArithPropagatedID;
typedef expr::CDAttribute<TheoryArithmeticPropagatedID, bool> TheoryArithPropagated;

/**
 * Validates that a node constraint has the following form:
 *   constraint: x |><| c
 * where |><| is either <, <=, ==, >=, LT and c is a constant rational.
 */
bool validateConstraint(TNode constraint){
  switch(constaint.getKind()){
  case LT:case LEQ: case EQ: case GEQ: case GT: break;
  default: false;
  }

  if(contraint[0].getMetaKind() != VARIABLE) return false;
  return contraint[1].getKind() == CONST_RATIONAL;
}

void addBound(TNode constraint){
  Assert(validateConstraint(constraint));
  TNode x = constraint[0];

  BoundsList* bl;
  if(!x.getAttribute(BoundsListAttr(), bl)){
    bl = new (true) BoundsList(getContext());
    x.setAttribute(BoundsListAttr(), bl);
  }
  bl->push_back(constraint);
}

inline int deltaCoeff(Kind k){
  switch(k){
  case LT: -1;
  case GT: 1;
  default: return 0;
  }
}


inline void propogateUpperBoundConstraint(TNode constraint, OutputChannel& oc){
  /* [x <= u && u < c] \=> x <  c
   * [x <= u && u < c] \=> x <= c
   * [x <= u && u < c] \=> !(x == c)
   * [x <= u && u < c] \=> !(x >= c)
   * [x <= u && u < c] \=> !(x >  c)
   */
  switch(constraint.getKind()){
  case LT:
  case LEQ:
    oc.propagate(constraint,false);
    break;
  case EQ:
  case GEQ:
  case GT:
    oc.propagate(constraint.negate(),false);
    break;
  }
  constaint.setAttribute(TheoryArithPropagated(),true);
}

inline void propogateLowerBoundConstraint(TNode constraint, OutputChannel& oc){
  /**
   * [x >= l && l > c] \=> x > c
   * [x >= l && l > c] \=> x >= c
   * [x >= l && l > c] \=> !(x == c)
   * [x >= l && l > c] \=> !(x <= c)
   * [x >= l && l > c] \=> !(x < c)
   */
  switch(constraint.getKind()){
  case GT:
  case GEQ:
    oc.propagate(constraint,false);
    break;
  case EQ:
  case LEQ:
  case LT:
    oc.propagate(constraint.negate(),false);
    break;
  }
}

void propagateBoundConstraints(TNode x, OutputChannel& oc){
  Assert(x.getMetaKind() == VARIABLE);

  ExtendedRational l;
  ExtendedRational u;
  bool hasLowerBound = x.getAttribute(LowerBound(), l);
  bool hasUpperBound = x.getAttribute(UpperBound(), u);

  if(!(hasLowerBound || hasUpperBound)) return;
  BoundsList* bl;

  if(!x.getAttribute(BoundsList(), bl)) return;

  for(BoundsList::iterator iter = bl->begin(); iter != bl->end(); ++iter){
    TNode constraint = *iter;
    if(contraint.hasAttribute(TheoryArithPropagated())){
      continue;
    }
    Rational& c = contraint[1].getConst<CONST_RATIONAL>();
    ExtendedRational ec(c, deltaCoeff(c.getKind()))
    if(hasUpperBound && u < ec ){
      constaint.setAttribute(TheoryArithPropagated(),true);
      propogateUpperBoundConstraint(constraint, oc);
    }
    if(hasLowerBound && l > ec ){
      constaint.setAttribute(TheoryArithPropagated(),true);
      propogateLowerBoundConstraint(constraint, oc);
    }
  }
}



void setAssignment(TNode x, DeltaRational& r){
  Assert(x.getMetaKind() == VARIABLE);
  x.setAttribute(Attribute(), r);
}

DeltaRational getAssignment(TNode x){
  Assert(x.getMetaKind() == VARIABLE);

  DeltaRational assign;
  AlwaysAssert(x.getAttribute(Assignment(),assign));
  return assign;
}



}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */



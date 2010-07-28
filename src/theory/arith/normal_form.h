
#include "expr/node.h"
#include "util/rational.h"
#include "theory/arith/arith_constants.h"

#ifndef __CVC4__THEORY__ARITH__NORMAL_FORM_H
#define __CVC4__THEORY__ARITH__NORMAL_FORM_H

namespace CVC4 {
namespace theory {
namespace arith {


/***********************************************/
/***************** Normal Form *****************/
/***********************************************/
/***********************************************/

/**
 * The normal form is defined by the following BNFs with guards:
 *
 * variable := n
 *   guards
 *     n.getMetaKind() == metakind::VARIABLE

 * constant := n
 *   guards
 *     n.getKind() == kind::CONST_RATIONAL

 * monomial := variable | (* [variable])
 *   guards
 *     len [variable] >= 2
 *     isSorted nodeOrder (getMList monomial)


 * coeff_mono := monomial | (* coeff monomial)
 *   guards
 *     coeff is renaming for constant
 *     coeff \not\in {0,1}

 * sum := coeff_mono | (+ [coeff_mono])
 *   guards
 *     len [coeff_mono] >= 2
 *     isStronglySorted cmono_cmp [coeff_mono]

 * cons_sum := sum |  (+ constant_1 sum) | constant_0
 *   guards
 *     constant_1, constant_0 are accepted by constant
 *     constant_1 != 0

 * comparison := leads_with_one |><| constant
 *   guards
 *     |><| is GEQ, EQ, LEQ
 *     leads with_one is a subexpression of sum s.t. it is also accepted by
 *     leads_with_one :=  monomial | (+ monomial [coeff_monomial])

 * Normal Form for terms := cons_sum
 * Normal Form for atoms := TRUE | FALSE | comparison | (not comparison)
 */

/**
 * Important Notes:
 *
 *  The languages for each are stratified. i.e. it is either the case that
 *  they or all of their children belong to a language that is strictly
 *  smaller according to the following partial order.
 *    constant -> monomial -> coeff_mono -> sum -> cons_sum
 *    variable                                     comparison
 *  This partial order is not unique, but it is simple.
 *
 *  This gives rise to the notion of the tightest language that accepts a node,
 *  which is simply the least according to the stratification order above.
 *
 *  Each subexpression of a normal form is also a normal form.
 *
 *  The tightest language that accepts a node does not always indicate the
 *  tighest language of the children:
 *     (+ v1 (* v1 v2) (* 2 (* v1 v2 v2)))
 */

/**
 * TAGGING:
 *  A node in normal form is tagged with the tightest binding above that
 *  accepts/generates it.
 *  All subexpressions are also in normal form and are also tagged.
 */
enum ArithNormalFormTag
  {VARIABLE,
   CONSTANT,
   MONOMIAL,
   COEFFICIENT_MONOMIAL,
   SUM,
   CONSTANT_SUM};


/** Sets and gets the tag on a node. */
inline ArithNormalFormTag getNFTag(TNode x);

/** Debug mode enforces that the tag is tight. */
inline void setNFTag(TNode x, ArithNormalFormTag tag);

/** Compares 2 monomials by lexigraphical order. */
inline int compareMonomial(TNode x, TNode y);

/** Conversion functions between integers and normal form tags */
inline uint8_t arithTagToInt(ArithNormalFormTag tag);
inline ArithNormalFormTag intToArithTag(uint8_t intTag);

/** Decomposes a constant sum term.*/
inline Node getConstantFromConstantSum(TNode x);
/** Returns null if there are no variables.*/
inline Node getSumFromConstantSum(TNode x);

inline TNode getMonomialFromCoefficientMonomial(TNode x);
inline Node getCoefficientFromCoefficientMonomial(TNode x);

namespace normal_form{

/**
 * The check functions are (potentially) full tree traversing calls that
 * check whether the formula belongs to a language.
 */
bool checkTag(TNode x, ArithNormalFormTag tag);
bool checkIsVariable(TNode x);
bool checkIsConstant(TNode x);
bool checkIsMonomial(TNode x);
bool checkIsCoefficientMonomial(TNode x);
bool checkIsSum(TNode x);
bool checkIsConstantSum(TNode x);
bool checkIsComparison(TNode x);
bool checkIsNormalFormTerm(TNode x);
bool checkIsNormalFormAtom(TNode x);

/**
 * checks if the tag is as tight as possible.
 * precondition: checkTag(x, tag) is true
 */
bool checkTagIsTight(TNode x, ArithNormalFormTag tag);



/**
 * Auxillary
 * let rec tuple_cmp elem_cmp pairs_list =
 *      match pair_list with
 *       [] -> 0
 *       |(x,y)::ps -> let cmp_res = elem_cmp x y in
 *                      if cmp_res <> 0
 *                      then cmp_res
 *                      else tuple_cmp elem_cmp ps
 *
 * let lex_cmp elem_cmp l0 l1 =
 *     if len l0 == len l1
 *     then tuple_cmp elem_cmp (zip l0 l1)
 *     else (len l0) - (len l1)
 *
 * let rec adjacent l =
 *     mathc l with
 *      a::b::xs -> (a,b)::(adjacent b::xs)
 *     | _ -> []

 * let isWeaklySorted cmp l =
 *     forall (fun (x,y) -> cmp x y <= 0) (adjacent l)

 * let isStronglySorted cmp l =
 *     forall (fun (x,y) -> cmp x y < 0) (adjacent l)

 * let getMList monomial =
 *        match monomial with
 *          variable -> [variable]
 *         |(* [variable]) -> [variable]

 * let drop_coeff coeff_mono =
 *      match coeff_mono in
 *         monomial -> monomial
 *        |(* coeff monomial) -> monomial

 * let mono_cmp m0 m1 = lex_cmp nodeOrder (getMList m0) (getMList m1)
 * let cmono_cmp cm0 cm1 = mono_cmp (drop_coeff cm0) (drop_coeff cm1)
 */


inline int compareMonomial(TNode x, TNode y){
  Assert(checkIsMonomial(x));
  Assert(checkIsMonomial(y));

  bool xIsMult = x.getKind() == MULT;
  bool yIsMult = y.getKind() == MULT;

  if(xIsMult && yIsMult){
    if(x.getNumChildren() == y.getNumChildren() ){
      for(TNode::iterator i = x.begin(), j = y.begin(),
            xEnd = x.end(), yEnd = y.end(); i != end; ++i, ++j){
        TNode xCurr = *i;
        TNode yCurr = *j;
        if(xCurr < yCurr){
          return -1;
        }else if(xCurr > yCurr){
          return 1;
        }
      }
      return 0;
    }else{
      return x.getNumChildren() - y.getNumChildren();
    }
  }else if( xIsMult && !yIsMult){
    return 1;
  }else if(!xIsMult &&  yIsMult){
    return -1;
  }else{
    return compare(x,y);
  }
}



inline uint8_t arithTagToInt(ArithNormalFormTag tag){
  switch(tag){
  case VARIABLE: return 1;
  case CONSTANT: return 2;
  case MONOMIAL: return 3;
  case COEFFICIENT_MONOMIAL: return 4;
  case SUM: return 5;
  case CONSTANT_SUM: return 6;
  default: Unreachable();
  }
}

inline ArithNormalFormTag intToArithTag(uint8_t intTag){
  switch(intTag){
  case 1: return VARIABLE;
  case 2: return CONSTANT;
  case 3: return MONOMIAL;
  case 4: return COEFFICIENT_MONOMIAL;
  case 5: return SUM;
  case 6: return CONSTANT_SUM;
  default: Unreachable();
  }
}


struct ArithNFTagID;
typedef expr::Attribute<ArithNFTagID, uint64_t> ArithNFTag;

}; /* namesapce normal_form */

inline ArithNormalFormTag getNFTag(TNode x){
  return intToArithTag(x.getAttribute(normal_form::ArithNFTag()));
}

inline void setNFTag(TNode x, ArithNormalFormTag tag){
  Assert(checkTag(x,tag));
  Assert(checkTagIsTight(x,tag));

  x.setAttribute(normal_form::ArithNFTag(), arithTagToInt(tag));
}



inline TNode getMonomialFromCoefficientMonomial(TNode x){
  Assert(checkIsCoefficientMonomial(x));

  if(x.getKind() == kind::MULT){
    if(x.getNumChildren() == 2 && x[0].getKind() == kind::CONST_RATIONAL){
      return x[1];
    }
  }
  return x;
}

inline Node getCoefficientFromCoefficientMonomial(TNode x){
  if(x.getKind() == kind::MULT){
    if(x.getNumChildren() == 2 && x[0].getKind() == kind::CONST_RATIONAL){
      return x[0];
    }
  }

  return NodeManager::currentNM()->mkConst<Rational>(Rational(1));
}

inline Node getSumFromConstantSum(TNode x){
  if(x.getKind() == kind::CONST_RATIONAL){
    return Node::null();
  }else if(x.getKind() == kind::PLUS){
    if(x.getNumChildren() == 2 && x[0].getKind() == kind::CONST_RATIONAL){
      return x[1];
    }
  }

  return x;
}

inline Node getConstantFromConstantSum(TNode x){
  if(x.getKind() == kind::CONST_RATIONAL){
    return x;
  }else if(x.getKind() == kind::PLUS){
    if(x.getNumChildren() == 2 && x[0].getKind() == kind::CONST_RATIONAL){
      return x[0];
    }
  }

  return NodeManager::currentNM()->mkConst<Rational>(Rational(0));
}

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__NORMAL_FORM_H */

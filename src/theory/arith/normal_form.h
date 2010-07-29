
#include "expr/node.h"
#include "util/rational.h"
#include "theory/arith/arith_constants.h"

#include <vector>

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
namespace normal_form {

enum ArithNormalFormTag
  {VARIABLE             = 0b0101111,
   MONOMIAL             = 0b0101110,
   COEFFICIENT_MONOMIAL = 0b0101100,
   SUM                  = 0b0101000,
   CONSTANT             = 0b0110000,
   CONSTANT_SUM         = 0b0100000};


struct ArithNFTagID;
typedef expr::Attribute<ArithNFTagID, uint64_t> ArithNFTag;

};

/** Returns true if the language for tag0 is a subset of the language for tag1. */
inline bool subformRelation(normal_form::ArithNormalFormTag tag0,
                            normal_form::ArithNormalFormTag tag1){
  return (tag0 & tag1) == tag1;
}

class ArithNormalForm {
public:
  /** Gets the tag on a node. */
  static inline normal_form::ArithNormalFormTag getTag(TNode x);

private:
  /**
   * Sets the tag on a node.
   * This does not enforce the strictness or correctness of the tag.
   * This is private so that only the mkX() functions can use this.
   */
  static inline void setNFTag(TNode x, normal_form::ArithNormalFormTag tag);

public:

  /**
   * Returns true if the tag on a node belongs to the language of tag.
   * precondition: x is tagged.
   */
  static inline bool isForm(TNode x, normal_form::ArithNormalFormTag tag){
    Assert(x.hasAttribute(normal_form::ArithNFTag()));
    return subformRelation(tag, getTag(x));
  }

  /**
   * Correct by construction builders for expressions in the normal form.
   * The output is guarenteed to belong to the corresponding language.
   * If the result would not belong to the language this cannot be used.
   * i.e. mkCoefficientSum(0, mkMonomial([x])) is not allowed but
   *      mkCoefficientSum(1, mkMonomial([x])) == mkMonomial([x]) holds.
   * Debug mode assures that the construction is locally correct i.e.
   * all of the children are correctly tagged.
   */
  static inline Node mkConstant(const Rational& value);
  static inline Node mkVariable(TNode x);
  static inline Node mkMonomial(std::vector<TNode>& variables);
  static inline Node mkCoefficientMonomial(const Rational& coeff, TNode monomial);
  static inline Node mkSum(const std::vector<TNode>& variables);
  static inline Node mkConstantSum(const Rational& constant, TNode sum);

  /** Decomposes a constant sum term.*/
  static inline Node getConstantFromConstantSum(TNode x);
  /** Returns null if there are no variables.*/
  static inline Node getSumFromConstantSum(TNode x);

  /** Compares 2 monomials by lexigraphical order. */
  static inline int compareMonomial(TNode x, TNode y);

  static inline TNode getMonomialFromCoefficientMonomial(TNode x);
  static inline Node getCoefficientFromCoefficientMonomial(TNode x);

private:
  /**
   * The check functions are calls that check whether the formula belongs to a language.
   * These are NOT efficient ways of determining the language of a tagged formula.
   *
   * If checkChildren is true, a full recursive check is called.
   *
   * The checks are language strict.
   * Does not assume the node is tagged.
   * Does assume the children are tagged.
   * If !checkChildren, assumes that the children are correctly tagged.
   */
  static bool checkIsVariable(TNode x, bool checkChildren);
  static bool checkIsConstant(TNode x, bool checkChildren);
  static bool checkIsMonomial(TNode x, bool checkChildren);
  static bool checkIsCoefficientMonomial(TNode x, bool checkChildren);
  static bool checkIsSum(TNode x, bool checkChildren);
  static bool checkIsConstantSum(TNode x, bool checkChildren);
  static bool checkIsComparison(TNode x, bool checkChildren);
  static bool checkIsNormalFormTerm(TNode x, bool checkChildren);
  static bool checkIsNormalFormAtom(TNode x, bool checkChildren);

public:
  /** Similar to the check calls on an aribitrary tagged node. */
  static bool checkTaggedTerm(TNode x, bool checkChildren);

};

inline Node ArithNormalForm::mkConstant(const Rational& value){
  Node constant = NodeManager::currentNM()->mkConst<Rational>(value);
  setNFTag(constant, normal_form::CONSTANT);

  checkTaggedTerm(constant, false);
  return constant;
}


inline Node ArithNormalForm::mkVariable(TNode x){
  setNFTag(x, normal_form::VARIABLE);
  checkTaggedTerm(constant, false);
  return x;
}

inline Node ArithNormalForm::mkMonomial(const std::vector<TNode>& variables){
  Assert(variables.size() >= 1);

  if(variables.size() == 1){
    TNode var = variables.front();
    Assert(isForm(var, VARIABLE));
    return var;
  }else{
    std::sort(variables.begin(), variables.end());
    NodeBuilder<> nb(kind::MULT);
    for(std::vector<TNode>::iterator i; i != variables.end(); ++i){
      TNode var = (*i);
      Assert(isForm(var, VARIABLE));
      nb << var;
    }

    Node monomial(nb);
    setNFTag(monomial, MONOMIAL);
    checkTaggedTerm(monomial, false);
    return monomial;
  }
}

inline Node ArithNormalForm::mkCoefficientMonomial(const Rational& coeff, TNode monomial){
  Assert(coeff != 0);
  if(coeff == 1){
    checkTaggedTerm(monomial, false);
    return monomial;
  }else{
    Node coefficient = mkConstant(coeff);
    Node coeffMono = NodeManager::currentNM()->mkNode(kind::MULT, coefficient, monomial);
    setNFTag(coeffMono, COEFFICIENT_MONOMIAL);
    checkTaggedTerm(coeffMono, false);
    return coeffMono;
  }
}
inline Node ArithNormalForm::mkMonomial(const std::vector<TNode>& cMonomials){
  Assert(cMonomials.size() >= 1);

  if(cMonomials.size() == 1){
    TNode var = variables.front();
    Assert(isForm(var, VARIABLE));
    return var;
  }else{
    sum = mkNode(kind::PLUS, total.begin(),total.end());
    setNFTag(sum, SUM);

    std::sort(variables.begin(), variables.end());
    NodeBuilder<> nb(kind::PLUS);
    for(std::vector<TNode>::iterator i; i != variables.end(); ++i){
      TNode var = (*i);
      Assert(isForm(var, VARIABLE));
      nb << var;
    }

    Node monomial(nb);
    setNFTag(monomial, MONOMIAL);
    checkTaggedTerm(monomial, false);
    return monomial;
  }
}

inline Node ArithNormalForm::mkCoefficientMonomial(const Rational& coeff, TNode monomial){
  Assert(coeff != 0);


  if(coeff == 1){
    checkTaggedTerm(monomial, false);
    return monomial;
  }else{
    Node coefficient = mkConstant(coeff);
    Node coeffMono = NodeManager::currentNM()->mkNode(kind::MULT, coefficient, monomial);
    setNFTag(coeffMono, COEFFICIENT_MONOMIAL);
    checkTaggedTerm(coeffMono, false);
    return coeffMono;
  }
}

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
  Assert(checkIsMonomial(x, false));
  Assert(checkIsMonomial(y, false));

  bool xIsMult = x.getKind() == kind::MULT;
  bool yIsMult = y.getKind() == kind::MULT;

  if(xIsMult && yIsMult){
    if(x.getNumChildren() == y.getNumChildren() ){
      for(TNode::iterator i = x.begin(), j = y.begin(),
            xEnd = x.end(), yEnd = y.end(); i != xEnd; ++i, ++j){
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
    if(x < y){
      return -1;
    }else if(x == y){
      return 0;
    }else{
      return 1;
    }
  }
}
inline int compareCoefficientMonomial(TNode x, TNode y){
  return compareMonomial(getMonomialFromCoefficientMonomial(x),
                         getMonomialFromCoefficientMonomial(y));
}



}; /* namesapce normal_form */

inline ArithNormalFormTag getNFTag(TNode x){
  return (ArithNormalFormTag)(x.getAttribute(normal_form::ArithNFTag()));
}

inline void setNFTag(TNode x, ArithNormalFormTag tag){
  x.setAttribute(normal_form::ArithNFTag(), (uint64_t)tag);
}



inline TNode getMonomialFromCoefficientMonomial(TNode x){
  Assert(normal_form::checkIsCoefficientMonomial(x, true));

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

inline bool subformRelation(ArithNormalFormTag tag0, ArithNormalFormTag tag1){
  return (tag0 & tag1) == tag1;
}

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__NORMAL_FORM_H */

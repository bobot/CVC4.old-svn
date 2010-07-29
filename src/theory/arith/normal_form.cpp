
#include "theory/arith/normal_form.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

bool normal_form::checkTag(TNode x, ArithNormalFormTag tag){
  switch(tag){
  case VARIABLE:
    return checkIsVariable(x);
  case CONSTANT:
    return checkIsConstant(x);
  case MONOMIAL:
    return checkIsMonomial(x);
  case COEFFICIENT_MONOMIAL:
    return checkIsCoefficientMonomial(x);
  case SUM:
    return checkIsSum(x);
  case CONSTANT_SUM:
    return checkIsConstantSum(x);
  default:
    Unimplemented();
  }
}


bool normal_form::checkTagIsTight(TNode x, ArithNormalFormTag tag){
  //Assumes checkTag(x,tag)
  switch(tag){
  case VARIABLE:
  case CONSTANT:
    return true;
  case MONOMIAL:
    return !checkIsVariable(x);
  case COEFFICIENT_MONOMIAL:
    return !checkIsMonomial(x);
  case SUM:
    return !checkIsCoefficientMonomial(x);
  case CONSTANT_SUM:
    return !checkIsSum(x);
  default:
    Unimplemented();
  }
}


bool normal_form::checkIsVariable(TNode x){
  return x.getMetaKind() == kind::metakind::VARIABLE;
}

bool normal_form::checkIsConstant(TNode x){
  return x.getKind() == kind::CONST_RATIONAL;
}


bool normal_form::checkIsMonomial(TNode x){
  if(x.getKind() == kind::MULT){
    Assert(x.getNumChildren() >= 2);
    TNode::iterator i = x.begin();
    TNode prev = *i;
    if(!normal_form::checkIsVariable(prev)) return false;
    ++i;
    for(TNode::iterator end = x.end(); i != end; ++i){
      TNode curr = *i;
      if(!checkIsVariable(prev)) return false;
      if(prev > curr) return false;
      prev = curr;
    }
    return true;
  }else{
    return normal_form::checkIsVariable(x);
  }
}


bool normal_form::checkIsCoefficientMonomial(TNode x){
  if(x.getKind() == kind::MULT){
    Assert(x.getNumChildren() >= 2);
    if(x.getNumChildren() == 2 && x[0].getKind() == kind::CONST_RATIONAL){
      const Rational& coeff = (x[0]).getConst<Rational>();
      if(coeff == 0 || coeff == 1){
        return false;
      }
      return checkIsMonomial(x[1]);
    }else{
      return checkIsMonomial(x);
    }
  }else{
    return checkIsMonomial(x);
  }
}



bool normal_form::checkIsSum(TNode x){
  if(x.getKind() == kind::PLUS){
    Assert(x.getNumChildren() >= 2);
    TNode::iterator i = x.begin();
    TNode prev = *i;
    if(!checkIsCoefficientMonomial(prev)) return false;
    ++i;
    for(TNode::iterator end = x.end(); i != end; ++i){
      TNode curr = *i;
      if(!normal_form::checkIsCoefficientMonomial(curr)) return false;
      if(compareCoefficientMonomial(prev,curr) >= 0) return false;
      prev = curr;
    }
  }else{
    return checkIsCoefficientMonomial(x);
  }
}


bool normal_form::checkIsConstantSum(TNode x){
  if(x.getKind() == kind::CONST_RATIONAL){
    return true;
  }else if(x.getKind() == kind::PLUS &&
           x.getNumChildren() == 2 &&
           x[0].getKind() == kind::CONST_RATIONAL){

      const Rational& coeff = (x[0]).getConst<Rational>();
      if(coeff == 0){
        return false;
      }
      return normal_form::checkIsSum(x[1]);
  }else{
    return normal_form::checkIsSum(x);
  }
}


bool normal_form::checkIsComparison(TNode x){
  if(x.getKind() == kind::GEQ ||
     x.getKind() == kind::LEQ ||
     x.getKind() == kind::EQUAL){
    Assert(x.getNumChildren() == 2);

    if((x[1]).getKind() != kind::CONST_RATIONAL) return false;

    TNode left = x[0];
    if(left.getKind() == kind::PLUS){
      if(! checkIsMonomial(left[0])) return false;

      return checkIsSum(left);
    }else{
      return checkIsMonomial(left);
    }
  }
  return false;
}


inline bool normal_form::checkIsNormalFormTerm(TNode x){
  return normal_form::checkIsConstantSum(x);
}

inline bool normal_form::checkIsNormalFormAtom(TNode x){
  switch(x.getKind()){
  case kind::CONST_BOOLEAN: return true;
  case kind::NOT: return normal_form::checkIsComparison(x[0]);
  default: return normal_form::checkIsComparison(x);
  }
}

/*********************                                                        */
/*! \file delta_rational.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/delta_rational.h"

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& os, const DeltaRational& dq){
  return os << "(" << dq.getNoninfinitesimalPart()
            << "," << dq.getInfinitesimalPart() << ")";
}


std::string DeltaRational::toString() const {
  return "(" + getNoninfinitesimalPart().toString() + "," +
    getInfinitesimalPart().toString() + ")";
}

void DeltaRational::seperatingDelta(Rational& res, const DeltaRational& a, const DeltaRational& b){
  Assert(res.sgn() > 0);

  int cmp = a.cmp(b);
  if(cmp != 0){
    bool aLeqB = cmp < 0;

    const DeltaRational& min = aLeqB ? a : b;
    const DeltaRational& max = aLeqB ? b : a;

    const Rational& pinf = min.getInfinitesimalPart();
    const Rational& cinf = max.getInfinitesimalPart();

    const Rational& pmaj = min.getNoninfinitesimalPart();
    const Rational& cmaj = max.getNoninfinitesimalPart();

    if(pmaj == cmaj){
      Assert(pinf < cinf);
      // any value of delta preserves the order
    }else if(pinf == cinf){
      Assert(pmaj < cmaj);
      // any value of delta preserves the order
    }else{
      Assert(pinf != cinf && pmaj != cmaj);
      Rational denDiffAbs = (cinf - pinf).abs();

      Rational numDiff = (cmaj - pmaj);
      Assert(numDiff.sgn() >= 0);
      Assert(denDiffAbs.sgn() > 0);
      Rational ratio = numDiff / denDiffAbs;
      Assert(ratio.sgn() > 0);

      if(ratio < res){
        res = ratio;
      }
    }
  }
}


DeltaRationalException::DeltaRationalException(const char* op, const DeltaRational& a, const DeltaRational& b) throw (){
    std::stringstream ss;
    ss << "Operation [" << op << "] between DeltaRational values ";
    ss << a << " and " << b << " is not a DeltaRational.";
    setMessage(ss.str());
}

DeltaRationalException::~DeltaRationalException() throw () { }


Integer DeltaRational::floorDivideQuotient(const DeltaRational& y) const throw(DeltaRationalException){
  if(isIntegral() && y.isIntegral()){
    Integer ti = floor();
    Integer yi = y.floor();
    return ti.floorDivideQuotient(yi);
  }else{
    throw DeltaRationalException("floorDivideQuotient", *this, y);
  }
}

Integer DeltaRational::floorDivideRemainder(const DeltaRational& y) const throw(DeltaRationalException){
  if(isIntegral() && y.isIntegral()){
    Integer ti = floor();
    Integer yi = y.floor();
    return ti.floorDivideRemainder(yi);
  }else{
    throw DeltaRationalException("floorDivideRemainder", *this, y);
  }
}

}/* CVC4 namespace */

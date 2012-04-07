/*********************                                                        */
/*! \file arith_prop_manager.cpp
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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/arith_prop_manager.h"

#include "theory/arith/arith_utilities.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"

using namespace CVC4::kind;
using namespace std;


namespace CVC4 {
namespace theory {
namespace arith {

// bool APM::isAsserted(TNode n) const{
//   Node satValue = d_valuation.getSatValue(n);
//   if(satValue.isNull()){
//     return false;
//   }else{
//     //Assert(satValue.getConst<bool>());
//     return true;
//   }
// }


// Node APM::strictlyWeakerAssertedUpperBound(ArithVar v, const DeltaRational& b) const{
//   Node bound = boundAsNode(true, v, b);

//   Assert(b.getInfinitesimalPart() <= 0);
//   bool largeEpsilon = (b.getInfinitesimalPart() < -1);

//   Node weaker = bound;
//   do {
//     if(largeEpsilon){
//       weaker = d_atomDatabase.getBestImpliedUpperBound(weaker);
//       largeEpsilon = false;
//     }else{
//       weaker = d_atomDatabase.getWeakerImpliedUpperBound(weaker);
//     }
//   }while(!weaker.isNull() && !isAsserted(weaker));
//   return weaker;
// }

// Node APM::strictlyWeakerAssertedLowerBound(ArithVar v, const DeltaRational& b) const{
//   Debug("APM") << "strictlyWeakerAssertedLowerBound" << endl;
//   Node bound = boundAsNode(false, v, b);

//   Assert(b.getInfinitesimalPart() >= 0);
//   bool largeEpsilon = (b.getInfinitesimalPart() > 1);

//   Node weaker = bound;
//   Debug("APM") << bound << b << endl;
//   do {
//     if(largeEpsilon){
//       weaker = d_atomDatabase.getBestImpliedLowerBound(weaker);
//       largeEpsilon = false;
//     }else{
//       weaker = d_atomDatabase.getWeakerImpliedLowerBound(weaker);
//     }
//   }while(!weaker.isNull() && !isAsserted(weaker));
//   Debug("APM") << "res: " << weaker << endl;
//   return weaker;
// }

// Node APM::getBestImpliedLowerBound(ArithVar v, const DeltaRational& b) const{
//   Node bound = boundAsNode(false, v, b);
//   return d_atomDatabase.getBestImpliedLowerBound(bound);
// }
// Node APM::getBestImpliedUpperBound(ArithVar v, const DeltaRational& b) const{
//   Node bound = boundAsNode(true, v, b);
//   return d_atomDatabase.getBestImpliedUpperBound(bound);
// }

// Node APM::boundAsNode(bool upperbound, ArithVar var, const DeltaRational& b) const {
//   Assert((!upperbound) || (b.getInfinitesimalPart() <= 0) );
//   Assert(upperbound || (b.getInfinitesimalPart() >= 0) );

//   Node varAsNode = d_arithvarNodeMap.asNode(var);
//   Kind kind;
//   bool negate;
//   if(upperbound){
//     negate = b.getInfinitesimalPart() < 0;
//     kind = negate ? GEQ : LEQ;
//   } else{
//     negate = b.getInfinitesimalPart() > 0;
//     kind = negate ? LEQ : GEQ;
//   }

//   Node righthand = mkRationalNode(b.getNoninfinitesimalPart());
//   Node bAsNode = NodeBuilder<2>(kind) << varAsNode << righthand;

//   if(negate){
//     bAsNode = NodeBuilder<1>(NOT) << bAsNode;
//   }

//   return bAsNode;
// }

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

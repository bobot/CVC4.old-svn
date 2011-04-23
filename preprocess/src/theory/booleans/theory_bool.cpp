/*********************                                                        */
/*! \file theory_bool.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory of booleans.
 **
 ** The theory of booleans.
 **/

#include "theory/theory.h"
#include "theory/booleans/theory_bool.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {
namespace booleans {

Node TheoryBool::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {
  case kind::VARIABLE:
    // case for Boolean vars is implemented in TheoryEngine (since it
    // appeals to the PropEngine to get the value)
    Unreachable();

  case kind::EQUAL: // 2 args
    // should be handled by IFF
    Unreachable();

  case kind::NOT: // 1 arg
    return nodeManager->mkConst(! d_valuation.getValue(n[0]).getConst<bool>());

  case kind::AND: { // 2+ args
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      if(! d_valuation.getValue(*i).getConst<bool>()) {
        return nodeManager->mkConst(false);
      }
    }
    return nodeManager->mkConst(true);
  }

  case kind::IFF: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() ==
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::IMPLIES: // 2 args
    return nodeManager->mkConst( (! d_valuation.getValue(n[0]).getConst<bool>()) ||
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::OR: { // 2+ args
    for(TNode::iterator i = n.begin(),
            iend = n.end();
          i != iend;
          ++i) {
      if(d_valuation.getValue(*i).getConst<bool>()) {
        return nodeManager->mkConst(true);
      }
    }
    return nodeManager->mkConst(false);
  }

  case kind::XOR: // 2 args
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() !=
                                 d_valuation.getValue(n[1]).getConst<bool>() );

  case kind::ITE: // 3 args
    // all ITEs should be gone except (bool,bool,bool) ones
    Assert( n[1].getType() == nodeManager->booleanType() &&
            n[2].getType() == nodeManager->booleanType() );
    return nodeManager->mkConst( d_valuation.getValue(n[0]).getConst<bool>() ?
                                 d_valuation.getValue(n[1]).getConst<bool>() :
                                 d_valuation.getValue(n[2]).getConst<bool>() );

  default:
    Unhandled(n.getKind());
  }
}
void TheoryBool::staticLearning(TNode n, TheoryPreprocessor& p){
  if((n.getKind() == kind::EQUAL || n.getKind() == kind::IFF) && n[0].getType().isBoolean()){
    if(n[0].getMetaKind() == kind::metakind::VARIABLE){
      Node preprocessRight = p.replaceAndRewrite(n[1]);
      Debug("bool") << "replacing " << n[0] << " with " << preprocessRight << std::endl;
      if(preprocessRight.getKind() == kind::CONST_BOOLEAN){

        p.requestReplacement(n[0], preprocessRight);
      }
    }else if(n[1].getMetaKind() == kind::metakind::VARIABLE){
      Node preprocessLeft = p.replaceAndRewrite(n[0]);
      Debug("bool") << "replacing " << n[1] << " with " << preprocessLeft << std::endl;
      if(preprocessLeft.getKind() == kind::CONST_BOOLEAN){

        p.requestReplacement(n[1], preprocessLeft);
      }
    }
  }
}
}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

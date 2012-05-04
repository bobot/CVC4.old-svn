/*********************                                                        */
/*! \file valuation.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): barrett, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A "valuation" proxy for TheoryEngine
 **
 ** Implementation of Valuation class.
 **/

#include "expr/node.h"
#include "theory/valuation.h"
#include "theory/theory_engine.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {

bool equalityStatusCompatible(EqualityStatus s1, EqualityStatus s2) {
 switch (s1) {
 case EQUALITY_TRUE:
 case EQUALITY_TRUE_IN_MODEL:
 case EQUALITY_TRUE_AND_PROPAGATED:
   switch (s2) {
   case EQUALITY_TRUE:
   case EQUALITY_TRUE_IN_MODEL:
   case EQUALITY_TRUE_AND_PROPAGATED:
     return true;
   default:
     return false;
   }
   break;
 case EQUALITY_FALSE:
 case EQUALITY_FALSE_IN_MODEL:
 case EQUALITY_FALSE_AND_PROPAGATED:
   switch (s2) {
   case EQUALITY_FALSE:
   case EQUALITY_FALSE_IN_MODEL:
   case EQUALITY_FALSE_AND_PROPAGATED:
     return true;
   default:
     return false;
   }
   break;
 default:
   return false;
 }
}


Node Valuation::getValue(TNode n) const {
  return d_engine->getValue(n);
}

bool Valuation::isSatLiteral(TNode n) const {
  return d_engine->getPropEngine()->isSatLiteral(n);
}

Node Valuation::getSatValue(TNode n) const {
  if(n.getKind() == kind::NOT) {
    Node atomRes = d_engine->getPropEngine()->getValue(n[0]);
    if(atomRes.getKind() == kind::CONST_BOOLEAN) {
      return NodeManager::currentNM()->mkConst(!atomRes.getConst<bool>());
    } else {
      Assert(atomRes.isNull());
      return atomRes;
    }
  } else {
    return d_engine->getPropEngine()->getValue(n);
  }
}

bool Valuation::hasSatValue(TNode n, bool& value) const {
  //  Node normalized = Rewriter::rewrite(n);
  if (d_engine->getPropEngine()->isSatLiteral(n)) {
    return d_engine->getPropEngine()->hasValue(n, value);
  } else {
    return false;
  }
}

EqualityStatus Valuation::getEqualityStatus(TNode a, TNode b) {
  return d_engine->getEqualityStatus(a, b);
}

Node Valuation::ensureLiteral(TNode n) {
  Debug("ensureLiteral") << "rewriting: " << n << std::endl;
  Node rewritten = Rewriter::rewrite(n);
  Debug("ensureLiteral") << "      got: " << rewritten << std::endl;
  Node preprocessed = d_engine->preprocess(rewritten);
  Debug("ensureLiteral") << "preproced: " << preprocessed << std::endl;
  d_engine->getPropEngine()->ensureLiteral(preprocessed);
  return preprocessed;
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

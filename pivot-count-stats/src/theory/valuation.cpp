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

namespace CVC4 {
namespace theory {

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
  return d_engine->getPropEngine()->hasValue(n, value);
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
/*********************                                                        */
/*! \file theory_builtin.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the builtin theory.
 **
 ** Implementation of the builtin theory.
 **/

#include "theory/builtin/theory_builtin.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include "theory/model.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace builtin {

void TheoryBuiltin::collectModelInfo( Model* m ){

}

bool TheoryBuiltin::hasInterpretedValue( TNode n, Model* m ){
  return n.getKind()==kind::TUPLE;
}

Node TheoryBuiltin::getInterpretedValue( TNode n, Model* m ){
  switch(n.getKind()) {
  case kind::TUPLE: { // 2+ args
    NodeBuilder<> nb(kind::TUPLE);
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      nb << m->getValue(*i);
    }
    return Node(nb);
  }
  default:
    // all other "builtins" should have been rewritten away or handled
    // by the valuation, or handled elsewhere.
    Unhandled(n.getKind());
  }
}

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory */
}/* CVC4 namespace */

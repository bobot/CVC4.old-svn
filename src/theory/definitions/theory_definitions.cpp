/*********************                                                        */
/*! \file theory_definition.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of uninterpreted functions.
 **
 ** Implementation of the theory of uninterpreted functions.
 **/

#include "theory/definition/theory_definition.h"
#include "expr/kind.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::definition;

TheoryDefinitions::TheoryDefinitions(Context* c, UserContext* u, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_DEFINITIONS, c, u, out, valuation) {

}

TheoryDefinitions::~TheoryDefinitions() {
}

void TheoryDefinitions::preRegisterTerm(TNode n) {
  Debug("definitions") << "definitions: begin preRegisterTerm(" << n << ")" << std::endl;
  Debug("definitions") << "definitions: end preRegisterTerm(" << n << ")" << std::endl;
}

void TheoryDefinitions::registerTerm(TNode n) {

  Debug("definitions") << "definitions: begin registerTerm(" << n << ")" << std::endl;

}


void TheoryDefinitions::check(Effort level) {
  /*
  Debug("definitions") << "definitions: begin check(" << level << ")" << std::endl;

  while(!done()) {
    Node assertion = get();
    Debug("definitions") << "TheoryDefinitions::check(): " << assertion << std::endl;

    switch(assertion.getKind()) {
    case EQUAL:
      d_assertions.push_back(assertion);
      d_pending.push_back(assertion);
      merge();
      break;
    case NOT:
      Assert(assertion[0].getKind() == EQUAL,
             "predicates not supported in this DEFINITIONS implementation");
      d_disequality.push_back(assertion[0]);
      break;
    case APPLY_DEFINITIONS:
      Unhandled("predicates not supported in this DEFINITIONS implementation");
    default:
      Unhandled(assertion.getKind());
    }

    Debug("definitions") << "TheoryDefinitions::check(): done = " << (done() ? "true" : "false") << std::endl;
  }
  */

  if (level == FULL_EFFORT) {
    Notice() << "Called with full effort" << std::endl;
  }

  Debug("definitions") << "definitions: end check(" << level << ")" << std::endl;
}

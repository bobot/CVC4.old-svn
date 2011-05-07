/*********************                                                        */
/*! \file theory_builtin.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Built-in theory.
 **
 ** Built-in theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H
#define __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H

#include "theory/theory.h"
#include "util/lemma_input_channel.h"

namespace CVC4 {
namespace theory {
namespace builtin {

class TheoryBuiltin : public Theory {
public:
  TheoryBuiltin(context::Context* c, OutputChannel& out, Valuation valuation) :
    Theory(THEORY_BUILTIN, c, out, valuation) {}
  Node simplify(TNode in, Substitutions& outSubstitutions);
  Node getValue(TNode n);
  std::string identify() const { return std::string("TheoryBuiltin"); }
};/* class TheoryBuiltin */

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H */

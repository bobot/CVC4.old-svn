/*********************                                                        */
/*! \file theory_datatypes.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of datatypes.
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H
#define __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H

#include "theory/theory.h"

#include <iostream>

namespace CVC4 {
namespace theory {
namespace datatypes {

class TheoryDatatypes : public Theory {
private:
  //a list of types with the list of constructors for that type
  std::vector<std::pair<Type, std::vector<Type> > > d_defs;
public:
  TheoryDatatypes(int id, context::Context* c, OutputChannel& out);
  ~TheoryDatatypes();
  void preRegisterTerm(TNode n) { }
  void registerTerm(TNode n) { }

  RewriteResponse preRewrite(TNode in, bool topLevel) {
    Debug("datatypes-rewrite") << "pre-rewriting " << in
                            << " topLevel==" << topLevel << std::endl;
    return RewriteComplete(in);
  }

  RewriteResponse postRewrite(TNode in, bool topLevel) {
    Debug("datatypes-rewrite") << "post-rewriting " << in
                            << " topLevel==" << topLevel << std::endl;
    return RewriteComplete(in);
  }

  void presolve();

  void addConstructorDefinitions( std::vector<std::pair<Type, std::vector<Type> > >& defs );

  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void check(Effort e);
  void propagate(Effort e) { }
  void explain(TNode n, Effort e) { }
  Node getValue(TNode n, TheoryEngine* engine);
  void shutdown() { }
  std::string identify() const { return std::string("TheoryDatatypes"); }
};/* class TheoryDatatypes */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H */

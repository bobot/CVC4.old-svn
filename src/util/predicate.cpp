/*********************                                                        */
/*! \file predicate.cpp
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
 ** \brief Representation of predicates for predicate subtyping
 **
 ** Simple class to represent predicates for predicate subtyping.
 ** Instances of this class are carried as the payload of
 ** the CONSTANT-metakinded SUBTYPE_TYPE types.
 **/

#include "expr/expr.h"
#include "util/predicate.h"
#include "util/Assert.h"

using namespace std;

namespace CVC4 {

Predicate::Predicate(Expr e) throw(IllegalArgumentException) : d_predicate(e) {
  CheckArgument(! e.isNull(), e, "Predicate cannot be null");
  CheckArgument(e.getType().isPredicate(), e, "Expression given is not predicate");
  CheckArgument(FunctionType(e.getType()).getArgTypes().size() == 1, e, "Expression given is not predicate of a single argument");
}

Predicate::operator Expr() const {
  return d_predicate;
}

bool Predicate::operator==(const Predicate& p) const {
  return d_predicate == p.d_predicate;
}

std::ostream&
operator<<(std::ostream& out, const Predicate& p) {
  return out << p.d_predicate;
}

size_t PredicateHashStrategy::hash(const Predicate& p) {
  return ExprHashFunction()(p.d_predicate);
}

}/* CVC4 namespace */

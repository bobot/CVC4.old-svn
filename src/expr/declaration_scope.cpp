/*********************                                                        */
/** declaration_scope.cpp
 ** Original author: cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Convenience class for scoping variable and type declarations (implementation)
 **/

#include "declaration_scope.h"
#include "expr.h"

#include "context/cdmap.h"
#include "context/context.h"

#include <string>

namespace CVC4 {

using namespace context;

namespace expr {

DeclarationScope::DeclarationScope() :
  d_context(new Context()),
  d_map(new (true) CDMap<std::string,Expr,StringHashFunction>(d_context)) {
}

DeclarationScope::~DeclarationScope() {
  d_map->deleteSelf();
  delete d_context;
}

void DeclarationScope::bind(const std::string& name, const Expr& obj) throw () {
  d_map->insert(name,obj);
}

bool DeclarationScope::isBound(const std::string& name) const throw () {
  return d_map->find(name) != d_map->end();
}

Expr DeclarationScope::lookup(const std::string& name) const throw () {
  return (*d_map->find(name)).second;

}
void DeclarationScope::popScope() throw () {
  d_context->pop();
}
void DeclarationScope::pushScope() throw () {
  d_context->push();
}

} // namespace expr
} // namespace CVC4

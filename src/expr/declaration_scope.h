/*********************                                                        */
/** context.h
 ** Original author: cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Convenience class for scoping variable and type declarations.
 **/

#ifndef DECLARATION_SCOPE_H_
#define DECLARATION_SCOPE_H_

#include "expr.h"

#include <ext/hash_map>

namespace CVC4 {
namespace context {

class Context;

template <class Key, class Data, class HashFcn>
class CDMap;

} //namespace context

namespace expr {

struct StringHashFunction {
  size_t operator()(const std::string& str) const {
    return __gnu_cxx::hash<const char*>()(str.c_str());
  }
};

class CVC4_PUBLIC DeclarationScope {
  context::Context *d_context;
  context::CDMap<std::string,CVC4::Expr,StringHashFunction> *d_map;

public:
  DeclarationScope();
  ~DeclarationScope();
  void bind(const std::string& name, const Expr& obj) throw ();
  bool isBound(const std::string& name) const throw ();
  Expr lookup(const std::string& name) const throw ();
  void popScope() throw ();
  void pushScope() throw ();
};


} // namespace expr
} // namespace CVC4

#endif /* DECLARATION_SCOPE_H_ */

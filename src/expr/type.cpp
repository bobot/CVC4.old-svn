/*********************                                                        */
/** type.cpp
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Implementation of expression types 
 **/

#include "expr/node_manager.h"
#include "expr/type.h"
#include "expr/type_constant.h"
#include "util/Assert.h"
#include <string>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Type& e) {
  e.toStream(out);
  return out;
}

Type::Type(NodeManager* nm, NodeTemplate<true>* node)
: d_typeNode(node),
  d_nodeManager(nm)
{
}

Type::~Type() {
  NodeManagerScope nms(d_nodeManager);
  delete d_typeNode;
}

Type::Type()
: d_typeNode(new Node()),
  d_nodeManager(NULL)
{
}

Type::Type(uintptr_t n)
: d_typeNode(NULL),
  d_nodeManager(NULL) {
  AlwaysAssert(n == 0);
}

Type::Type(const Type& t)
: d_typeNode(t.d_typeNode),
  d_nodeManager(t.d_nodeManager)
{
}

Type& Type::operator=(const Type& t) {
  if (this != &t) {
    *d_typeNode = *t.d_typeNode;
    d_nodeManager = t.d_nodeManager;
  }
  return *this;
}

bool Type::operator==(const Type& t) const {
  return *d_typeNode == *t.d_typeNode;
}

bool Type::operator!=(const Type& t) const {
  return *d_typeNode != *t.d_typeNode;
}

void Type::toStream(std::ostream& out) const {
  out << *d_typeNode;
}

/** Is this the Boolean type? */
bool Type::isBoolean() const {
  return d_typeNode->getKind() == kind::TYPE_CONSTANT
      && d_typeNode->getConst<TypeConstant>() == BOOLEAN_TYPE;
}

/** Cast to a Boolean type */
Type::operator BooleanType() const {
  Assert(isBoolean());
  return BooleanType(*this);
}

/** Is this a function type? */
bool Type::isFunction() const {
  return d_typeNode->getKind() == kind::FUNCTION_TYPE;
}

/** Is this a predicate type? NOTE: all predicate types are also
    function types. */
bool Type::isPredicate() const {
  // TODO: Check the last child for range
  return isFunction();
}

/** Cast to a function type */
Type::operator FunctionType() const {
  Assert(isFunction());
  return FunctionType(*this);
}

/** Is this a kind type (i.e., the type of a type)? */
bool Type::isKind() const {
  return d_typeNode->getKind() == kind::TYPE_CONSTANT
      && d_typeNode->getConst<TypeConstant>() == KIND_TYPE;
}

/** Cast to a kind type */
Type::operator KindType() const {
  Assert(isKind());
  return KindType(*this);
}

/** Is this a sort kind */
bool Type::isSort() const {
  return d_typeNode->getKind() == kind::SORT_TYPE;
}

/** Cast to a sort type */
Type::operator SortType() const {
  Assert(isSort());
  return SortType(*this);
}

std::vector<Type> FunctionType::getArgTypes() const {
  std::vector<Type> args;
  for (unsigned i = 0, i_end = d_typeNode->getNumChildren() - 1; i < i_end; ++ i) {
    args.push_back(d_nodeManager->getType((*d_typeNode)[i]));
  }
  return args;
}

Type FunctionType::getRangeType() const {
  return d_nodeManager->getType(*d_typeNode->end());
}

void FunctionType::toStream(std::ostream& out) const {
  unsigned arity = d_typeNode->getNumChildren();

  if(arity > 2) {
    out << "(";
  }
  unsigned int i;
  for(i=0; i < arity - 1; ++i) {
    if(i > 0) {
      out << ",";
    }
    (*d_typeNode)[i].toStream(out);
  }
  if(arity > 2) {
    out << ")";
  }
  out << " -> ";
  (*d_typeNode)[i].toStream(out);
}

BooleanType::BooleanType(const Type& t) : Type(t) {}
FunctionType::FunctionType(const Type& t) : Type(t) {}
KindType::KindType(const Type& t) : Type(t) {}
SortType::SortType(const Type& t) : Type(t) {}

}/* CVC4 namespace */

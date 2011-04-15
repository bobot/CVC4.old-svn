/*********************                                                        */
/*! \file datatype.cpp
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
 ** \brief A class representing a Datatype definition
 **
 ** A class representing a Datatype definition for the theory of
 ** inductive datatypes.
 **/

#include "util/datatype.h"
#include "expr/type.h"
#include "expr/expr_manager.h"

namespace CVC4 {

void Datatype::resolve(ExprManager* em, DatatypeType self) {
  CheckArgument(em != NULL, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!d_resolved, "cannot resolve a Datatype twice");
  d_resolved = true;
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    (*i).resolve(em, self);
  }
}

Datatype::Datatype(std::string name) :
  d_name(name),
  d_constructors(),
  d_resolved(false) {
}

void Datatype::addConstructor(const Constructor& c) {
  CheckArgument(!d_resolved, this,
                "cannot add a constructor to a finalized Datatype");
  d_constructors.push_back(c);
}

std::string Datatype::getName() const throw() {
  return d_name;
}

size_t Datatype::getNumConstructors() const throw() {
  return d_constructors.size();
}

bool Datatype::operator==(const Datatype& other) const throw() {
  // two datatypes are == iff the name is the same and they have
  // exactly matching constructors (in the same order)
  if(d_name != other.d_name ||
     getNumConstructors() != other.getNumConstructors()) {
    return false;
  }
  for(const_iterator i = begin(), j = other.begin(); i != end(); ++i, ++j) {
    Assert(j != other.end());
    if(*i != *j) {
      return false;
    }
  }
  return true;
}

bool Datatype::operator!=(const Datatype& other) const throw() {
  return !(*this == other);
}

Datatype::iterator Datatype::begin() throw() {
  return d_constructors.begin();
}

Datatype::iterator Datatype::end() throw() {
  return d_constructors.end();
}

Datatype::const_iterator Datatype::begin() const throw() {
  return d_constructors.begin();
}

Datatype::const_iterator Datatype::end() const throw() {
  return d_constructors.end();
}

void Datatype::Constructor::resolve(ExprManager* em, DatatypeType self) {
  CheckArgument(em != NULL, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!d_resolved,
                "cannot resolve a Datatype constructor twice; "
                "perhaps the same constructor was added twice, "
                "or to two datatypes?");
  d_resolved = true;
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if((*i).d_selector.isNull()) {
      (*i).d_selector = em->mkVar(em->mkSelectorType(self, self));
    } else {
      (*i).d_selector = em->mkVar(em->mkSelectorType(self, (*i).d_selector.getType()));
    }
  }
}

Datatype::Constructor::Constructor(std::string name, Expr tester) :
  d_name(name),
  d_tester(tester),
  d_args(),
  d_resolved(false) {
  CheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
  CheckArgument(!tester.isNull(), tester, "cannot construct a datatype constructor without a tester");
}

void Datatype::Constructor::addArg(std::string selectorName, Type selectorType) {
  CheckArgument(!d_resolved, this, "cannot modify a finalized Datatype constructor");
  CheckArgument(!selectorType.isNull(), selectorType, "cannot add a null selector type");
  d_args.push_back(Arg(selectorName, selectorType.getExprManager().mkVar(selectorType)));
}

void Datatype::Constructor::addArg(std::string selectorName, Datatype::SelfType) {
  CheckArgument(!d_resolved, this, "cannot modify a finalized Datatype constructor");
  d_args.push_back(Arg(selectorName, Type::null()));
}

std::string Datatype::Constructor::getName() const throw() {
  return d_name;
}

Expr Datatype::Constructor::getTester() const throw() {
  return d_tester;
}

size_t Datatype::Constructor::getNumArgs() const throw() {
  return d_args.size();
}

bool Datatype::Constructor::operator==(const Constructor& other) const throw() {
  // two constructors are == iff they have the same name, their
  // testers are equal and they have exactly matching args (in the
  // same order)
  if(d_name != other.d_name ||
     getTester() != other.getTester() ||
     getNumArgs() != other.getNumArgs()) {
    return false;
  }
  for(const_iterator i = begin(), j = other.begin(); i != end(); ++i, ++j) {
    Assert(j != other.end());
    if(*i != *j) {
      return false;
    }
  }
  return true;
}

bool Datatype::Constructor::operator!=(const Constructor& other) const throw() {
  return !(*this == other);
}

Datatype::Constructor::iterator Datatype::Constructor::begin() throw() {
  return d_args.begin();
}

Datatype::Constructor::iterator Datatype::Constructor::end() throw() {
  return d_args.end();
}

Datatype::Constructor::const_iterator Datatype::Constructor::begin() const throw() {
  return d_args.begin();
}

Datatype::Constructor::const_iterator Datatype::Constructor::end() const throw() {
  return d_args.end();
}

Datatype::Constructor::Arg::Arg(std::string name, Expr selector) :
  d_name(name),
  d_selector(selector) {
  CheckArgument(name != "", name, "cannot construct a datatype constructor arg without a name");
  CheckArgument(!selector.isNull(), selector, "cannot construct a datatype constructor arg without a selector");
}

std::string Datatype::Constructor::Arg::getName() const throw() {
  return d_name;
}

Expr Datatype::Constructor::Arg::getSelector() const throw() {
  return d_selector;
}

bool Datatype::Constructor::Arg::operator==(const Arg& other) const throw() {
  // two args are == iff they have the same name and selector
  return getName() == other.getName() && getSelector() == other.getSelector();
}

bool Datatype::Constructor::Arg::operator!=(const Arg& other) const throw() {
  return !(*this == other);
}

std::ostream& operator<<(std::ostream& os, const Datatype& dt) {
  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << "DATATYPE " << dt.getName() << " =" << std::endl;
  Datatype::const_iterator i = dt.begin(), i_end = dt.end();
  if(i != i_end) {
    os << "  ";
    do {
      os << *i << std::endl;
      if(++i != i_end) {
        os << "| ";
      }
    } while(i != i_end);
  }
  os << "END;" << std::endl;

  return os;
}

std::ostream& operator<<(std::ostream& os, const Datatype::Constructor& ctor) {
  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << ctor.getName();

  Datatype::Constructor::const_iterator i = ctor.begin(), i_end = ctor.end();
  if(i != i_end) {
    os << "(";
    do {
      os << *i;
      if(++i != i_end) {
        os << ", ";
      }
    } while(i != i_end);
    os << ")";
  }

  return os;
}

std::ostream& operator<<(std::ostream& os, const Datatype::Constructor::Arg& arg) {
  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  Type t = SelectorType(arg.getSelector().getType()).getRangeType();

  os << arg.getName() << ": ";
  if(t.isDatatype()) {
    os << DatatypeType(t).getDatatype().getName();
  } else {
    os << t;
  }

  return os;
}

}/* CVC4 namespace */

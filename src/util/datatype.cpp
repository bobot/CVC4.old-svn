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

Datatype::UnresolvedType::UnresolvedType(std::string name) :
  d_name(name) {
}

std::string Datatype::UnresolvedType::getName() const throw() {
  return d_name;
}

void Datatype::resolve(ExprManager* em, std::map<std::string, DatatypeType>& resolutions) {
  CheckArgument(em != NULL, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!d_resolved, "cannot resolve a Datatype twice");
  CheckArgument(resolutions.find(d_name) != resolutions.end(), "Datatype::resolve(): resolutions doesn't contain me!");
  DatatypeType self = (*resolutions.find(d_name)).second;
  CheckArgument(&self.getDatatype() == this, "Datatype::resolve(): resolutions doesn't contain me!");
  d_resolved = true;
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    (*i).resolve(em, self, resolutions);
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
    // two constructors are == iff they have the same name, their
    // testers are equal and they have exactly matching args (in the
    // same order)
    if((*i).getName() != (*j).getName() ||
       (*i).getNumArgs() != (*j).getNumArgs()) {
      return false;
    }
    // testers are harder b/c constructors might not be resolved yet
#   warning fix tester equality
    for(Constructor::const_iterator k = (*i).begin(), l = (*j).begin(); k != (*i).end(); ++k, ++l) {
      Assert(l != (*j).end());
      if((*k).getName() != (*l).getName()) {
        return false;
      }
#     warning fix selector equality
    }
  }
  return true;
}

bool Datatype::operator!=(const Datatype& other) const throw() {
  return !(*this == other);
}

bool Datatype::isResolved() const throw() {
  return d_resolved;
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

bool Datatype::Constructor::isResolved() const {
  return !d_tester.isNull();
}

void Datatype::Constructor::resolve(ExprManager* em, DatatypeType self, std::map<std::string, DatatypeType>& resolutions) {
  CheckArgument(em != NULL, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!isResolved(),
                "cannot resolve a Datatype constructor twice; "
                "perhaps the same constructor was added twice, "
                "or to two datatypes?");
  d_tester = em->mkVar(d_name.substr(d_name.find('\0') + 1), em->mkTesterType(self));
  d_name.resize(d_name.find('\0'));
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if((*i).d_selector.isNull()) {
      (*i).d_selector = em->mkVar(em->mkSelectorType(self, self));
    } else {
      (*i).d_selector = em->mkVar(em->mkSelectorType(self, (*i).d_selector.getType()));
    }
  }
}

Datatype::Constructor::Constructor(std::string name, std::string tester) :
  // We sdon't want to introduce a new data member, because eventually we're
  // going to be a constant stuffed inside a node.  So we stow the tester
  // name away inside the constructor name until resolution.
  d_name(name + '\0' + tester),
  d_tester(),
  d_args() {
  CheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
  CheckArgument(!tester.empty(), tester, "cannot construct a datatype constructor without a tester");
}

void Datatype::Constructor::addArg(std::string selectorName, Type selectorType) {
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  CheckArgument(!selectorType.isNull(), selectorType, "cannot add a null selector type");
  d_args.push_back(Arg(selectorName, selectorType.getExprManager()->mkVar(selectorType)));
}

void Datatype::Constructor::addArg(std::string selectorName, Datatype::UnresolvedType type) {
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
# warning do something with unresolved type
  d_args.push_back(Arg(selectorName, Expr()));
}

std::string Datatype::Constructor::getName() const throw() {
  std::string name = d_name;
  if(!isResolved()) {
    name.resize(name.find('\0'));
  }
  return name;
}

Expr Datatype::Constructor::getTester() const throw() {
  CheckArgument(isResolved(), this, "this datatype constructor not yet resolved");
  return d_tester;
}

size_t Datatype::Constructor::getNumArgs() const throw() {
  return d_args.size();
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
}

std::string Datatype::Constructor::Arg::getName() const throw() {
  return d_name;
}

Expr Datatype::Constructor::Arg::getSelector() const throw() {
  return d_selector;
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

  Expr selector = arg.getSelector();
  std::string name = arg.getName();
  os << arg.getName() << ": ";
  if(selector.isNull()) {
    os << "[self]";
  } else {
    Type t = selector.getType();
    if(t.isSelector()) { // not actually a selector until resolution
      t = SelectorType(t).getRangeType();
    }
    if(t.isDatatype()) {
      os << DatatypeType(t).getDatatype().getName();
    } else {
      os << t;
    }
  }

  return os;
}

}/* CVC4 namespace */

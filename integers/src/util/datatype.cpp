/*********************                                                        */
/*! \file datatype.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: ajreynol
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

#include <string>
#include <sstream>

#include "util/datatype.h"
#include "expr/type.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/node_manager.h"
#include "expr/node.h"
#include "util/recursion_breaker.h"
#include "util/matcher.h"

using namespace std;

namespace CVC4 {

namespace expr {
  namespace attr {
    struct DatatypeIndexTag {};
    struct DatatypeFiniteTag {};
    struct DatatypeWellFoundedTag {};
    struct DatatypeFiniteComputedTag {};
    struct DatatypeWellFoundedComputedTag {};
    struct DatatypeGroundTermTag {};
  }/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */

typedef expr::Attribute<expr::attr::DatatypeIndexTag, uint64_t> DatatypeIndexAttr;
typedef expr::Attribute<expr::attr::DatatypeFiniteTag, bool> DatatypeFiniteAttr;
typedef expr::Attribute<expr::attr::DatatypeWellFoundedTag, bool> DatatypeWellFoundedAttr;
typedef expr::Attribute<expr::attr::DatatypeFiniteComputedTag, bool> DatatypeFiniteComputedAttr;
typedef expr::Attribute<expr::attr::DatatypeWellFoundedComputedTag, bool> DatatypeWellFoundedComputedAttr;
typedef expr::Attribute<expr::attr::DatatypeGroundTermTag, Node> DatatypeGroundTermAttr;

const Datatype& Datatype::datatypeOf(Expr item) {
  ExprManagerScope ems(item);
  TypeNode t = Node::fromExpr(item).getType();
  switch(t.getKind()) {
  case kind::CONSTRUCTOR_TYPE:
    return DatatypeType(t[t.getNumChildren() - 1].toType()).getDatatype();
  case kind::SELECTOR_TYPE:
  case kind::TESTER_TYPE:
    return DatatypeType(t[0].toType()).getDatatype();
  default:
    Unhandled("arg must be a datatype constructor, selector, or tester");
  }
}

size_t Datatype::indexOf(Expr item) {
  ExprManagerScope ems(item);
  AssertArgument(item.getType().isConstructor() ||
                 item.getType().isTester() ||
                 item.getType().isSelector(),
                 item,
                 "arg must be a datatype constructor, selector, or tester");
  TNode n = Node::fromExpr(item);
  if( item.getKind()==kind::APPLY_TYPE_ASCRIPTION ){
    return indexOf( item[0] );
  }else{
    Assert(n.hasAttribute(DatatypeIndexAttr()));
    return n.getAttribute(DatatypeIndexAttr());
  }
}

void Datatype::resolve(ExprManager* em,
                       const std::map<std::string, DatatypeType>& resolutions,
                       const std::vector<Type>& placeholders,
                       const std::vector<Type>& replacements,
                       const std::vector< SortConstructorType >& paramTypes,
                       const std::vector< DatatypeType >& paramReplacements)
  throw(AssertionException, DatatypeResolutionException) {

  AssertArgument(em != NULL, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!d_resolved, "cannot resolve a Datatype twice");
  AssertArgument(resolutions.find(d_name) != resolutions.end(),
                "Datatype::resolve(): resolutions doesn't contain me!");
  AssertArgument(placeholders.size() == replacements.size(), placeholders,
                "placeholders and replacements must be the same size");
  CheckArgument(getNumConstructors() > 0, *this, "cannot resolve a Datatype that has no constructors");
  DatatypeType self = (*resolutions.find(d_name)).second;
  AssertArgument(&self.getDatatype() == this, "Datatype::resolve(): resolutions doesn't contain me!");
  d_resolved = true;
  size_t index = 0;
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    (*i).resolve(em, self, resolutions, placeholders, replacements, paramTypes, paramReplacements);
    Assert((*i).isResolved());
    Node::fromExpr((*i).d_constructor).setAttribute(DatatypeIndexAttr(), index);
    Node::fromExpr((*i).d_tester).setAttribute(DatatypeIndexAttr(), index++);
  }
  d_self = self;
  Assert(index == getNumConstructors());
}

void Datatype::addConstructor(const Constructor& c) {
  CheckArgument(!d_resolved, this,
                "cannot add a constructor to a finalized Datatype");
  d_constructors.push_back(c);
}

Cardinality Datatype::getCardinality() const throw(AssertionException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");
  RecursionBreaker<const Datatype*, DatatypeHashFunction> breaker(__PRETTY_FUNCTION__, this);
  if(breaker.isRecursion()) {
    return Cardinality::INTEGERS;
  }
  Cardinality c = 0;
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    c += (*i).getCardinality();
  }
  return c;
}

bool Datatype::isFinite() const throw(AssertionException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_self);

  TypeNode self = TypeNode::fromType(d_self);

  // is this already in the cache ?
  if(self.getAttribute(DatatypeFiniteComputedAttr())) {
    return self.getAttribute(DatatypeFiniteAttr());
  }

  Cardinality c = 0;
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if(! (*i).isFinite()) {
      self.setAttribute(DatatypeFiniteComputedAttr(), true);
      self.setAttribute(DatatypeFiniteAttr(), false);
      return false;
    }
  }
  self.setAttribute(DatatypeFiniteComputedAttr(), true);
  self.setAttribute(DatatypeFiniteAttr(), true);
  return true;
}

bool Datatype::isWellFounded() const throw(AssertionException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_self);

  TypeNode self = TypeNode::fromType(d_self);

  // is this already in the cache ?
  if(self.getAttribute(DatatypeWellFoundedComputedAttr())) {
    return self.getAttribute(DatatypeWellFoundedAttr());
  }

  RecursionBreaker<const Datatype*, DatatypeHashFunction> breaker(__PRETTY_FUNCTION__, this);
  if(breaker.isRecursion()) {
    // This *path* is cyclic, so may not be well-founded.  The
    // datatype itself might still be well-founded, though (we'll find
    // the well-foundedness along another path).
    return false;
  }

  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if((*i).isWellFounded()) {
      self.setAttribute(DatatypeWellFoundedComputedAttr(), true);
      self.setAttribute(DatatypeWellFoundedAttr(), true);
      return true;
    }
  }

  self.setAttribute(DatatypeWellFoundedComputedAttr(), true);
  self.setAttribute(DatatypeWellFoundedAttr(), false);
  return false;
}

Expr Datatype::mkGroundTerm( Type t ) const throw(AssertionException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_self);

  TypeNode self = TypeNode::fromType(d_self);

  // is this already in the cache ?
  Expr groundTerm = self.getAttribute(DatatypeGroundTermAttr()).toExpr();
  if(!groundTerm.isNull()) {
    Debug("datatypes") << "\nin cache: " << d_self << " => " << groundTerm << std::endl;
  } else {
    Debug("datatypes") << "\nNOT in cache: " << d_self << std::endl;
    // look for a nullary ctor and use that
    for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
      // prefer the nullary constructor
      if( groundTerm.isNull() && (*i).getNumArgs() == 0) {
        groundTerm = d_constructors[indexOf((*i).getConstructor())].mkGroundTerm( t );
        //groundTerm = (*i).getConstructor().getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, (*i).getConstructor());
        self.setAttribute(DatatypeGroundTermAttr(), groundTerm);
        Debug("datatypes-gt") << "constructed nullary: " << getName() << " => " << groundTerm << std::endl;
      }
    }
    // No ctors are nullary, but we can't just use the first ctor
    // because that might recurse!  In fact, since this datatype is
    // well-founded by assumption, we know that at least one constructor
    // doesn't contain a self-reference.  We search for that one and use
    // it to construct the ground term, as that is often a simpler
    // ground term (e.g. in a tree datatype, something like "(leaf 0)"
    // is simpler than "(node (leaf 0) (leaf 0))".
    //
    // Of course this check doesn't always work, if the self-reference
    // is through other Datatypes (or other non-Datatype types), but it
    // does simplify a common case.  It requires a bit of extra work,
    // but since we cache the results of these, it only happens once,
    // ever, per Datatype.
    //
    // If the datatype is not actually well-founded, something below
    // will throw an exception.
    for(const_iterator i = begin(), i_end = end();
        i != i_end;
        ++i) {
      if( groundTerm.isNull() ){
        Constructor::const_iterator j = (*i).begin(), j_end = (*i).end();
        for(; j != j_end; ++j) {
          SelectorType stype((*j).getSelector().getType());
          if(stype.getDomain() == stype.getRangeType()) {
            Debug("datatypes") << "self-reference, skip " << getName() << "::" << (*i).getName() << std::endl;
            // the constructor contains a direct self-reference
            break;
          }
        }

        if(j == j_end && (*i).isWellFounded()) {
          groundTerm = (*i).mkGroundTerm( t );
          // Constructor::mkGroundTerm() doesn't ever return null when
          // called from the outside.  But in recursive invocations, it
          // can: say you have dt = a(one:dt) | b(two:INT), and you ask
          // the "a" constructor for a ground term.  It asks "dt" for a
          // ground term, which in turn asks the "a" constructor for a
          // ground term!  Thus, even though "a" is a well-founded
          // constructor, it cannot construct a ground-term by itself.  We
          // have to skip past it, and we do that with a
          // RecursionBreaker<> in Constructor::mkGroundTerm().  In the
          // case of recursion, it returns null.
          if(!groundTerm.isNull()) {
            // we found a ground-term-constructing constructor!
            self.setAttribute(DatatypeGroundTermAttr(), groundTerm);
            Debug("datatypes") << "constructed: " << getName() << " => " << groundTerm << std::endl;
          }
        }
      }
    }
  }
  if( groundTerm.isNull() ){
    // if we get all the way here, we aren't well-founded
    CheckArgument(false, *this, "this datatype is not well-founded, cannot construct a ground term!");
  }else{
    return groundTerm;
  }
}

DatatypeType Datatype::getDatatypeType() const throw(AssertionException) {
  CheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  Assert(!d_self.isNull() && !DatatypeType(d_self).isParametric());
  return DatatypeType(d_self);
}

DatatypeType Datatype::getDatatypeType(const std::vector<Type>& params)
  const throw(AssertionException) {
  CheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  Assert(!d_self.isNull() && DatatypeType(d_self).isParametric());
  return DatatypeType(d_self).instantiate(params);
}

bool Datatype::operator==(const Datatype& other) const throw() {
  // two datatypes are == iff the name is the same and they have
  // exactly matching constructors (in the same order)

  if(this == &other) {
    return true;
  }

  if(isResolved() != other.isResolved()) {
    return false;
  }

  if(d_name != other.d_name ||
     getNumConstructors() != other.getNumConstructors()) {
    return false;
  }
  for(const_iterator i = begin(), j = other.begin(); i != end(); ++i, ++j) {
    Assert(j != other.end());
    // two constructors are == iff they have the same name, their
    // constructors and testers are equal and they have exactly
    // matching args (in the same order)
    if((*i).getName() != (*j).getName() ||
       (*i).getNumArgs() != (*j).getNumArgs()) {
      return false;
    }
    // testing equivalence of constructors and testers is harder b/c
    // this constructor might not be resolved yet; only compare them
    // if they are both resolved
    Assert(isResolved() == !(*i).d_constructor.isNull() &&
           isResolved() == !(*i).d_tester.isNull() &&
           (*i).d_constructor.isNull() == (*j).d_constructor.isNull() &&
           (*i).d_tester.isNull() == (*j).d_tester.isNull());
    if(!(*i).d_constructor.isNull() && (*i).d_constructor != (*j).d_constructor) {
      return false;
    }
    if(!(*i).d_tester.isNull() && (*i).d_tester != (*j).d_tester) {
      return false;
    }
    for(Constructor::const_iterator k = (*i).begin(), l = (*j).begin(); k != (*i).end(); ++k, ++l) {
      Assert(l != (*j).end());
      if((*k).getName() != (*l).getName()) {
        return false;
      }
      // testing equivalence of selectors is harder b/c args might not
      // be resolved yet
      Assert(isResolved() == (*k).isResolved() &&
             (*k).isResolved() == (*l).isResolved());
      if((*k).isResolved()) {
        // both are resolved, so simply compare the selectors directly
        if((*k).d_selector != (*l).d_selector) {
          return false;
        }
      } else {
        // neither is resolved, so compare their (possibly unresolved)
        // types; we don't know if they'll be resolved the same way,
        // so we can't ever say unresolved types are equal
        if(!(*k).d_selector.isNull() && !(*l).d_selector.isNull()) {
          if((*k).d_selector.getType() != (*l).d_selector.getType()) {
            return false;
          }
        } else {
          if((*k).isUnresolvedSelf() && (*l).isUnresolvedSelf()) {
            // Fine, the selectors are equal if the rest of the
            // enclosing datatypes are equal...
          } else {
            return false;
          }
        }
      }
    }
  }
  return true;
}

const Datatype::Constructor& Datatype::operator[](size_t index) const {
  CheckArgument(index < getNumConstructors(), index, "index out of bounds");
  return d_constructors[index];
}

const Datatype::Constructor& Datatype::operator[](std::string name) const {
  for(const_iterator i = begin(); i != end(); ++i) {
    if((*i).getName() == name) {
      return *i;
    }
  }
  CheckArgument(false, name, "No such constructor `%s' of datatype `%s'", name.c_str(), d_name.c_str());
}

Expr Datatype::getConstructor(std::string name) const {
  return (*this)[name].getConstructor();
}

void Datatype::Constructor::resolve(ExprManager* em, DatatypeType self,
                                    const std::map<std::string, DatatypeType>& resolutions,
                                    const std::vector<Type>& placeholders,
                                    const std::vector<Type>& replacements,
                                    const std::vector< SortConstructorType >& paramTypes,
                                    const std::vector< DatatypeType >& paramReplacements)
  throw(AssertionException, DatatypeResolutionException) {

  AssertArgument(em != NULL, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!isResolved(),
                "cannot resolve a Datatype constructor twice; "
                "perhaps the same constructor was added twice, "
                "or to two datatypes?");
  size_t index = 0;
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if((*i).d_selector.isNull()) {
      // the unresolved type wasn't created here; do name resolution
      string typeName = (*i).d_name.substr((*i).d_name.find('\0') + 1);
      (*i).d_name.resize((*i).d_name.find('\0'));
      if(typeName == "") {
        (*i).d_selector = em->mkVar((*i).d_name, em->mkSelectorType(self, self));
      } else {
        map<string, DatatypeType>::const_iterator j = resolutions.find(typeName);
        if(j == resolutions.end()) {
          stringstream msg;
          msg << "cannot resolve type \"" << typeName << "\" "
              << "in selector \"" << (*i).d_name << "\" "
              << "of constructor \"" << d_name << "\"";
          throw DatatypeResolutionException(msg.str());
        } else {
          (*i).d_selector = em->mkVar((*i).d_name, em->mkSelectorType(self, (*j).second));
        }
      }
    } else {
      // the type for the selector already exists; may need
      // complex-type substitution
      Type range = (*i).d_selector.getType();
      if(!placeholders.empty()) {
        range = range.substitute(placeholders, replacements);
      }
      if(!paramTypes.empty() ) {
        range = doParametricSubstitution( range, paramTypes, paramReplacements );
      }
      (*i).d_selector = em->mkVar((*i).d_name, em->mkSelectorType(self, range));
    }
    Node::fromExpr((*i).d_selector).setAttribute(DatatypeIndexAttr(), index++);
    (*i).d_resolved = true;
  }

  Assert(index == getNumArgs());

  // Set constructor/tester last, since Constructor::isResolved()
  // returns true when d_tester is not the null Expr.  If something
  // fails above, we want Constuctor::isResolved() to remain "false".
  // Further, mkConstructorType() iterates over the selectors, so
  // should get the results of any resolutions we did above.
  d_tester = em->mkVar(d_name.substr(d_name.find('\0') + 1), em->mkTesterType(self));
  d_name.resize(d_name.find('\0'));
  d_constructor = em->mkVar(d_name, em->mkConstructorType(*this, self));
  //associate constructor with all selectors
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    (*i).d_constructor = d_constructor;
  }
}

Type Datatype::Constructor::doParametricSubstitution( Type range,
                                  const std::vector< SortConstructorType >& paramTypes,
                                  const std::vector< DatatypeType >& paramReplacements ) {
  TypeNode typn = TypeNode::fromType( range );
  if(typn.getNumChildren() == 0) {
    return range;
  } else {
    std::vector< Type > origChildren;
    std::vector< Type > children;
    for(TypeNode::const_iterator i = typn.begin(), iend = typn.end();i != iend; ++i) {
      origChildren.push_back( (*i).toType() );
      children.push_back( doParametricSubstitution( (*i).toType(), paramTypes, paramReplacements ) );
    }
    for( int i=0; i<(int)paramTypes.size(); i++ ) {
      if( paramTypes[i].getArity()==origChildren.size() ) {
        Type tn = paramTypes[i].instantiate( origChildren );
        if( range==tn ) {
          return paramReplacements[i].instantiate( children );
        }
      }
    }
    NodeBuilder<> nb(typn.getKind());
    for( int i=0; i<(int)children.size(); i++ ) {
      nb << TypeNode::fromType( children[i] );
    }
    return nb.constructTypeNode().toType();
  }
}

Datatype::Constructor::Constructor(std::string name, std::string tester) :
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the tester name away inside the constructor name until
  // resolution.
  d_name(name + '\0' + tester),
  d_tester(),
  d_args() {
  CheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
  CheckArgument(!tester.empty(), tester, "cannot construct a datatype constructor without a tester");
}

void Datatype::Constructor::addArg(std::string selectorName, Type selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away inside a var until resolution (when we can
  // create the proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  CheckArgument(!selectorType.isNull(), selectorType, "cannot add a null selector type");
  Expr type = selectorType.getExprManager()->mkVar(selectorType);
  Debug("datatypes") << type << endl;
  d_args.push_back(Arg(selectorName, type));
}

void Datatype::Constructor::addArg(std::string selectorName, Datatype::UnresolvedType selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away after a NUL in the name string until
  // resolution (when we can create the proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  CheckArgument(selectorType.getName() != "", selectorType, "cannot add a null selector type");
  d_args.push_back(Arg(selectorName + '\0' + selectorType.getName(), Expr()));
}

void Datatype::Constructor::addArg(std::string selectorName, Datatype::SelfType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we mark
  // the name string with a NUL to indicate that we have a
  // self-selecting selector until resolution (when we can create the
  // proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  d_args.push_back(Arg(selectorName + '\0', Expr()));
}

std::string Datatype::Constructor::getName() const throw() {
  string name = d_name;
  if(!isResolved()) {
    name.resize(name.find('\0'));
  }
  return name;
}

Expr Datatype::Constructor::getConstructor() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_constructor;
}

Type Datatype::Constructor::getSpecializedConstructorType(Type returnType) const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  const Datatype& dt = Datatype::datatypeOf(d_constructor);
  CheckArgument(dt.isParametric(), this, "this datatype constructor is not yet resolved");
  DatatypeType dtt = DatatypeType(dt.d_self);
  Matcher m(dtt);
  m.doMatching( TypeNode::fromType(dtt), TypeNode::fromType(returnType) );
  vector<Type> subst;
  m.getMatches(subst);
  vector<Type> params = dt.getParameters();
  return d_constructor.getType().substitute(params, subst);
}

Expr Datatype::Constructor::getTester() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_tester;
}

Cardinality Datatype::Constructor::getCardinality() const throw(AssertionException) {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");

  Cardinality c = 1;

  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    c *= SelectorType((*i).getSelector().getType()).getRangeType().getCardinality();
  }

  return c;
}

bool Datatype::Constructor::isFinite() const throw(AssertionException) {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_constructor);

  TNode self = Node::fromExpr(d_constructor);

  // is this already in the cache ?
  if(self.getAttribute(DatatypeFiniteComputedAttr())) {
    return self.getAttribute(DatatypeFiniteAttr());
  }

  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if(! SelectorType((*i).getSelector().getType()).getRangeType().getCardinality().isFinite()) {
      self.setAttribute(DatatypeFiniteComputedAttr(), true);
      self.setAttribute(DatatypeFiniteAttr(), false);
      return false;
    }
  }

  self.setAttribute(DatatypeFiniteComputedAttr(), true);
  self.setAttribute(DatatypeFiniteAttr(), true);
  return true;
}

bool Datatype::Constructor::isWellFounded() const throw(AssertionException) {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_constructor);

  TNode self = Node::fromExpr(d_constructor);

  // is this already in the cache ?
  if(self.getAttribute(DatatypeWellFoundedComputedAttr())) {
    return self.getAttribute(DatatypeWellFoundedAttr());
  }

  RecursionBreaker<const Datatype::Constructor*, DatatypeHashFunction> breaker(__PRETTY_FUNCTION__, this);
  if(breaker.isRecursion()) {
    // This *path* is cyclic, sso may not be well-founded.  The
    // constructor itself might still be well-founded, though (we'll
    // find the well-foundedness along another path).
    return false;
  }

  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if(! SelectorType((*i).getSelector().getType()).getRangeType().isWellFounded()) {
      /* FIXME - we can't cache a negative result here, because a
         Datatype might tell us it's not well founded along this
         *path*, due to recursion, when it really is well-founded.
         This should be fixed by creating private functions to do the
         recursion here, and leaving the (public-facing)
         isWellFounded() call as the base of that recursion.  Then we
         can distinguish the cases.
      */
      /*
      self.setAttribute(DatatypeWellFoundedComputedAttr(), true);
      self.setAttribute(DatatypeWellFoundedAttr(), false);
      */
      return false;
    }
  }

  self.setAttribute(DatatypeWellFoundedComputedAttr(), true);
  self.setAttribute(DatatypeWellFoundedAttr(), true);
  return true;
}

Expr Datatype::Constructor::mkGroundTerm( Type t ) const throw(AssertionException) {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_constructor);

  TNode self = Node::fromExpr(d_constructor);

  // is this already in the cache ?
  Expr groundTerm = self.getAttribute(DatatypeGroundTermAttr()).toExpr();
  if(!groundTerm.isNull()) {
    return groundTerm;
  }

  RecursionBreaker<const Datatype::Constructor*, DatatypeHashFunction> breaker(__PRETTY_FUNCTION__, this);
  if(breaker.isRecursion()) {
    // Recursive path, we should skip and go to the next constructor;
    // see lengthy comments in Datatype::mkGroundTerm().
    return Expr();
  }

  std::vector<Expr> groundTerms;
  groundTerms.push_back(getConstructor());

  // for each selector, get a ground term
  Assert( t.isDatatype() );
  std::vector< Type > instTypes;
  std::vector< Type > paramTypes;
  if( DatatypeType(t).isParametric() ){
    paramTypes = DatatypeType(t).getDatatype().getParameters();
    instTypes = DatatypeType(t).getParamTypes();
  }
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type selType = SelectorType((*i).getSelector().getType()).getRangeType();
    if( DatatypeType(t).isParametric() ){
      selType = selType.substitute( paramTypes, instTypes );
    }
    groundTerms.push_back(selType.mkGroundTerm());
  }
  
  groundTerm = getConstructor().getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, groundTerms);
  if( groundTerm.getType()!=t ){
    Assert( Datatype::datatypeOf( d_constructor ).isParametric() );
    //type is ambiguous, must apply type ascription
    Debug("datatypes-gt") << "ambiguous type for " << groundTerm << ", ascribe to " << t << std::endl;
    groundTerms[0] = getConstructor().getExprManager()->mkExpr(kind::APPLY_TYPE_ASCRIPTION,
                       getConstructor().getExprManager()->mkConst(AscriptionType(getSpecializedConstructorType(t))),
                       groundTerms[0]);
    groundTerm = getConstructor().getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, groundTerms);
  }
  self.setAttribute(DatatypeGroundTermAttr(), groundTerm);
  return groundTerm;
}

const Datatype::Constructor::Arg& Datatype::Constructor::operator[](size_t index) const {
  CheckArgument(index < getNumArgs(), index, "index out of bounds");
  return d_args[index];
}

const Datatype::Constructor::Arg& Datatype::Constructor::operator[](std::string name) const {
  for(const_iterator i = begin(); i != end(); ++i) {
    if((*i).getName() == name) {
      return *i;
    }
  }
  CheckArgument(false, name, "No such arg `%s' of constructor `%s'", name.c_str(), d_name.c_str());
}

Expr Datatype::Constructor::getSelector(std::string name) const {
  return (*this)[name].getSelector();
}

Datatype::Constructor::Arg::Arg(std::string name, Expr selector) :
  d_name(name),
  d_selector(selector),
  d_resolved(false) {
  CheckArgument(name != "", name, "cannot construct a datatype constructor arg without a name");
}

std::string Datatype::Constructor::Arg::getName() const throw() {
  string name = d_name;
  const size_t nul = name.find('\0');
  if(nul != string::npos) {
    name.resize(nul);
  }
  return name;
}

Expr Datatype::Constructor::Arg::getSelector() const {
  CheckArgument(isResolved(), this, "cannot get a selector for an unresolved datatype constructor");
  return d_selector;
}

Expr Datatype::Constructor::Arg::getConstructor() const {
  CheckArgument(isResolved(), this,
                "cannot get a associated constructor for argument of an unresolved datatype constructor");
  return d_constructor;
}

Type Datatype::Constructor::Arg::getSelectorType() const {
  return getSelector().getType();
}

bool Datatype::Constructor::Arg::isUnresolvedSelf() const throw() {
  return d_selector.isNull() && d_name.size() == d_name.find('\0') + 1;
}

static const int s_printDatatypeNamesOnly = std::ios_base::xalloc();

std::string Datatype::Constructor::Arg::getSelectorTypeName() const {
  Type t;
  if(isResolved()) {
    t = SelectorType(d_selector.getType()).getRangeType();
  } else {
    if(d_selector.isNull()) {
      string typeName = d_name.substr(d_name.find('\0') + 1);
      return (typeName == "") ? "[self]" : typeName;
    } else {
      t = d_selector.getType();
    }
  }

  // Unfortunately, in the case of complex selector types, we can
  // enter nontrivial recursion here.  Make sure that doesn't happen.
  stringstream ss;
  ss << Expr::setlanguage(language::output::LANG_CVC4);
  ss.iword(s_printDatatypeNamesOnly) = 1;
  t.toStream(ss);
  return ss.str();
}

std::ostream& operator<<(std::ostream& os, const Datatype& dt) {
  // These datatype things are recursive!  Be very careful not to
  // print an infinite chain of them.
  long& printNameOnly = os.iword(s_printDatatypeNamesOnly);
  Debug("datatypes-output") << "printNameOnly is " << printNameOnly << std::endl;
  if(printNameOnly) {
    return os << dt.getName();
  }

  class Scope {
    long& d_ref;
    long d_oldValue;
  public:
    Scope(long& ref, long value) : d_ref(ref), d_oldValue(ref) { d_ref = value; }
    ~Scope() { d_ref = d_oldValue; }
  } scope(printNameOnly, 1);
  // when scope is destructed, the value pops back

  Debug("datatypes-output") << "printNameOnly is now " << printNameOnly << std::endl;

  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << "DATATYPE " << dt.getName() << " =" << endl;
  Datatype::const_iterator i = dt.begin(), i_end = dt.end();
  if(i != i_end) {
    os << "  ";
    do {
      os << *i << endl;
      if(++i != i_end) {
        os << "| ";
      }
    } while(i != i_end);
  }
  os << "END;" << endl;

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

  os << arg.getName() << ": " << arg.getSelectorTypeName();

  return os;
}

}/* CVC4 namespace */

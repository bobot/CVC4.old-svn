/*********************                                                        */
/*! \file datatype.h
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

#include "cvc4_public.h"

#ifndef __CVC4__DATATYPE_H
#define __CVC4__DATATYPE_H

#include <iostream>
#include <string>
#include <vector>
#include <map>

namespace CVC4 {
  // messy; Expr needs Datatype (because it's the payload of a
  // CONSTANT-kinded expression), and Datatype needs Expr.
  class CVC4_PUBLIC Datatype;
}/* CVC4 namespace */

#include "expr/expr.h"
#include "expr/type.h"
#include "util/Assert.h"
#include "util/output.h"
#include "util/hash.h"
#include "util/exception.h"

namespace CVC4 {

class CVC4_PUBLIC ExprManager;

/**
 * An exception that is thrown when a datatype resolution fails.
 */
class CVC4_PUBLIC DatatypeResolutionException : public Exception {
public:
  inline DatatypeResolutionException(std::string msg);
};/* class DatatypeResolutionException */

/**
 * The representation of an inductive datatype.
 *
 * This is far more complicated than it first seems.  Consider this
 * datatype definition:
 *
 *   DATATYPE nat =
 *     succ(pred: nat)
 *   | zero
 *   END;
 *
 * You cannot define "nat" until you have a Type for it, but you
 * cannot have a Type for it until you fill in the type of the "pred"
 * selector, which needs the Type.  So we have a chicken-and-egg
 * problem.  It's even more complicated when we have mutual recusion
 * between datatypes, since the CVC presentation language does not
 * require forward-declarations.  Here, we define trees of lists that
 * contain trees of lists (etc):
 *
 *   DATATYPE
 *     tree = node(left: tree, right: tree) | leaf(list),
 *     list = cons(car: tree, cdr: list) | nil
 *   END;
 *
 * Note that while parsing the "tree" definition, we have to take it
 * on faith that "list" is a valid type.  We build Datatype objects to
 * describe "tree" and "list", and their constructors and constructor
 * arguments, but leave any unknown types (including self-references)
 * in an "unresolved" state.  After parsing the whole DATATYPE block,
 * we create a DatatypeType through
 * ExprManager::mkMutualDatatypeTypes().  The ExprManager creates a
 * DatatypeType for each, but before "releasing" this type into the
 * wild, it does a round of in-place "resolution" on each Datatype by
 * calling Datatype::resolve() with a map of string -> DatatypeType to
 * allow the datatype to construct the necessary testers and
 * selectors.
 *
 * An additional point to make is that we want to ease the burden on
 * both the parser AND the users of the CVC4 API, so this class takes
 * on the task of generating its own selectors and testers, for
 * instance.  That means that, after reifying the Datatype with the
 * ExprManager, the parser needs to go through the (now-resolved)
 * Datatype and request ; see src/parser/parser.cpp for how this is
 * done.  For API usage ideas, see test/unit/util/datatype_black.h.
 */
class CVC4_PUBLIC Datatype {
public:
  class CVC4_PUBLIC SelfType {
  };/* class Datatype::SelfType */

  class CVC4_PUBLIC UnresolvedType {
    std::string d_name;
  public:
    inline UnresolvedType(std::string name);
    inline std::string getName() const throw();
  };/* class Datatype::UnresolvedType */

  class CVC4_PUBLIC Constructor {
  public:
    class CVC4_PUBLIC Arg {

      std::string d_name;
      Expr d_selector;
      bool d_resolved;

      explicit Arg(std::string name, Expr selector);
      friend class Constructor;
      friend class Datatype;

      bool isUnresolvedSelf() const throw();

    public:

      std::string getName() const throw();
      Expr getSelector() const;
      std::string getSelectorTypeName() const;

      bool isResolved() const throw();

    };/* class Datatype::Constructor::Arg */

    typedef std::vector<Arg>::iterator iterator;
    typedef std::vector<Arg>::const_iterator const_iterator;

  private:

    std::string d_name;
    Expr d_constructor;
    Expr d_tester;
    std::vector<Arg> d_args;

    void resolve(ExprManager* em, DatatypeType self,
                 const std::map<std::string, DatatypeType>& resolutions)
      throw(AssertionException, DatatypeResolutionException);
    friend class Datatype;

  public:
    explicit Constructor(std::string name, std::string tester);
    void addArg(std::string selectorName, Type selectorType);
    void addArg(std::string selectorName, Datatype::UnresolvedType selectorType);
    void addArg(std::string selectorName, Datatype::SelfType);

    std::string getName() const throw();
    Expr getConstructor() const;
    Expr getTester() const;
    inline size_t getNumArgs() const throw();

    inline bool isResolved() const throw();

    inline iterator begin() throw();
    inline iterator end() throw();
    inline const_iterator begin() const throw();
    inline const_iterator end() const throw();

  };/* class Datatype::Constructor */

  typedef std::vector<Constructor>::iterator iterator;
  typedef std::vector<Constructor>::const_iterator const_iterator;

private:
  std::string d_name;
  std::vector<Constructor> d_constructors;
  bool d_resolved;

  /**
   * Datatypes refer to themselves, recursively, and we have a
   * chicken-and-egg problem.  The DatatypeType around the Datatype
   * cannot exist until the Datatype is finalized, and the Datatype
   * cannot refer to the DatatypeType representing itself until it
   * exists.  resolve() is called by the ExprManager when a Type.  Has
   * the effect of freezing the object, too; that is, addConstructor()
   * will fail after a call to resolve().
   */
  void resolve(ExprManager* em,
               const std::map<std::string, DatatypeType>& resolutions)
    throw(AssertionException, DatatypeResolutionException);
  friend class ExprManager;// for access to resolve()

public:

  inline explicit Datatype(std::string name);
  void addConstructor(const Constructor& c);

  inline std::string getName() const throw();
  inline size_t getNumConstructors() const throw();

  // We need == for mkConst(Datatype) to properly work---since if the
  // Datatype Expr requested is the same as an already-existing one,
  // we need to return that one.  For that, we have a hash and
  // operator==.  We provide != for symmetry.  We don't provide
  // operator<() etc. because given two Datatype Exprs, you could
  // simply compare those rather than the (bare) Datatypes.  This
  // means, though, that Datatype cannot be stored in a sorted list or
  // RB tree directly, so maybe we can consider adding these
  // comparison operators later on.
  bool operator==(const Datatype& other) const throw();
  inline bool operator!=(const Datatype& other) const throw();

  inline bool isResolved() const throw();

  inline iterator begin() throw();
  inline iterator end() throw();
  inline const_iterator begin() const throw();
  inline const_iterator end() const throw();

};/* class Datatype */

struct CVC4_PUBLIC DatatypeHashStrategy {
  static inline size_t hash(const Datatype& dt) {
    return StringHashFunction()(dt.getName());
  }
};/* struct DatatypeHashStrategy */

// FUNCTION DECLARATIONS FOR OUTPUT STREAMS

std::ostream& operator<<(std::ostream& os, const Datatype& dt) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& os, const Datatype::Constructor& ctor) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& os, const Datatype::Constructor::Arg& arg) CVC4_PUBLIC;

// INLINE FUNCTIONS

inline DatatypeResolutionException::DatatypeResolutionException(std::string msg) :
  Exception(msg) {
}

inline Datatype::UnresolvedType::UnresolvedType(std::string name) :
  d_name(name) {
}

inline std::string Datatype::UnresolvedType::getName() const throw() {
  return d_name;
}

inline Datatype::Datatype(std::string name) :
  d_name(name),
  d_constructors(),
  d_resolved(false) {
}

inline std::string Datatype::getName() const throw() {
  return d_name;
}

inline size_t Datatype::getNumConstructors() const throw() {
  return d_constructors.size();
}

inline bool Datatype::operator!=(const Datatype& other) const throw() {
  return !(*this == other);
}

inline bool Datatype::isResolved() const throw() {
  return d_resolved;
}

inline Datatype::iterator Datatype::begin() throw() {
  return d_constructors.begin();
}

inline Datatype::iterator Datatype::end() throw() {
  return d_constructors.end();
}

inline Datatype::const_iterator Datatype::begin() const throw() {
  return d_constructors.begin();
}

inline Datatype::const_iterator Datatype::end() const throw() {
  return d_constructors.end();
}

inline bool Datatype::Constructor::isResolved() const throw() {
  return !d_tester.isNull();
}

inline size_t Datatype::Constructor::getNumArgs() const throw() {
  return d_args.size();
}

inline bool Datatype::Constructor::Arg::isResolved() const throw() {
  // We could just write:
  //
  //   return !d_selector.isNull() && d_selector.getType().isSelector();
  //
  // HOWEVER, this causes problems in ExprManager tear-down, because
  // the attributes are removed before the pool is purged.  When the
  // pool is purged, this triggers an equality test between Datatypes,
  // and this triggers a call to isResolved(), which breaks because
  // d_selector has no type after attributes are stripped.
  //
  // This problem, coupled with the fact that this function is called
  // _often_, means we should just use a boolean flag.
  //
  return d_resolved;
}

inline Datatype::Constructor::iterator Datatype::Constructor::begin() throw() {
  return d_args.begin();
}

inline Datatype::Constructor::iterator Datatype::Constructor::end() throw() {
  return d_args.end();
}

inline Datatype::Constructor::const_iterator Datatype::Constructor::begin() const throw() {
  return d_args.begin();
}

inline Datatype::Constructor::const_iterator Datatype::Constructor::end() const throw() {
  return d_args.end();
}

}/* CVC4 namespace */

#endif /* __CVC4__DATATYPE_H */

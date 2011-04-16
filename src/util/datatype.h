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

namespace CVC4 {

class CVC4_PUBLIC ExprManager;

class CVC4_PUBLIC Datatype {
public:
  class CVC4_PUBLIC UnresolvedType {
    std::string d_name;
  public:
    UnresolvedType(std::string name);
    std::string getName() const throw();
  };/* class Datatype::UnresolvedType */

  class CVC4_PUBLIC Constructor {
  public:
    class CVC4_PUBLIC Arg {
      std::string d_name;
      Expr d_selector;

      explicit Arg(std::string name, Expr selector);
      friend class Constructor;

    public:

      std::string getName() const throw();
      Expr getSelector() const throw();

    };/* class Datatype::Constructor::Arg */

    typedef std::vector<Arg>::iterator iterator;
    typedef std::vector<Arg>::const_iterator const_iterator;

  private:
    std::string d_name;
    Expr d_tester;
    std::vector<Arg> d_args;

    void resolve(ExprManager* em, DatatypeType self, std::map<std::string, DatatypeType>& resolutions);
    friend class Datatype;

  public:
    explicit Constructor(std::string name, std::string tester);
    void addArg(std::string selectorName, Type selectorType);
    void addArg(std::string selectorName, Datatype::UnresolvedType selectorType);

    std::string getName() const throw();
    Expr getTester() const throw();
    size_t getNumArgs() const throw();

    bool isResolved() const;

    iterator begin() throw();
    iterator end() throw();
    const_iterator begin() const throw();
    const_iterator end() const throw();

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
  void resolve(ExprManager* em, std::map<std::string, DatatypeType>& resolutions);
  friend class ExprManager;// for access to resolve()

public:

  explicit Datatype(std::string name);
  void addConstructor(const Constructor& c);

  std::string getName() const throw();
  size_t getNumConstructors() const throw();

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
  bool operator!=(const Datatype& other) const throw();

  bool isResolved() const throw();

  iterator begin() throw();
  iterator end() throw();
  const_iterator begin() const throw();
  const_iterator end() const throw();

};/* class Datatype */

struct CVC4_PUBLIC DatatypeHashStrategy {
  static inline size_t hash(const Datatype& dt) {
    return StringHashFunction()(dt.getName());
  }
};/* struct DatatypeHashStrategy */

std::ostream& operator<<(std::ostream& os, const Datatype& dt) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& os, const Datatype::Constructor& ctor) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& os, const Datatype::Constructor::Arg& arg) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__DATATYPE_H */

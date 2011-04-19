/*********************                                                        */
/*! \file expr_manager_template.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public-facing expression manager interface.
 **
 ** Public-facing expression manager interface.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__EXPR_MANAGER_H
#define __CVC4__EXPR_MANAGER_H

#include <vector>

#include "expr/kind.h"
#include "expr/type.h"
#include "expr/expr.h"

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 37 "${template}"

namespace CVC4 {

class Expr;
class SmtEngine;
class NodeManager;
struct Options;
class IntStat;

namespace context {
  class Context;
}/* CVC4::context namespace */

class CVC4_PUBLIC ExprManager {
private:
  /** The context */
  context::Context* d_ctxt;

  /** The internal node manager */
  NodeManager* d_nodeManager;

  /** Counts of expressions and variables created of a given kind */
  IntStat* d_exprStatisticsVars[LAST_TYPE + 1];
  IntStat* d_exprStatistics[kind::LAST_KIND];

  /**
   * Returns the internal node manager.  This should only be used by
   * internal users, i.e. the friend classes.
   */
  NodeManager* getNodeManager() const;

  /**
   * Returns the internal Context.  Used by internal users, i.e. the
   * friend classes.
   */
  context::Context* getContext() const;

  /**
   * SmtEngine will use all the internals, so it will grab the
   * NodeManager.
   */
  friend class SmtEngine;

  /** ExprManagerScope reaches in to get the NodeManager */
  friend class ExprManagerScope;

  /** NodeManager reaches in to get the NodeManager */
  friend class NodeManager;

  // undefined, private copy constructor and assignment op (disallow copy)
  ExprManager(const ExprManager&) CVC4_UNDEFINED;
  ExprManager& operator=(const ExprManager&) CVC4_UNDEFINED;

public:

  /**
   * Creates an expression manager with default options.
   */
  ExprManager();

  /**
   * Creates an expression manager.
   *
   * @param options the earlyTypeChecking field is used to configure
   * whether to do at Expr creation time.
   */
  explicit ExprManager(const Options& options);

  /**
   * Destroys the expression manager. No will be deallocated at this point, so
   * any expression references that used to be managed by this expression
   * manager and are left-over are bad.
   */
  ~ExprManager();

  /** Get the type for booleans */
  BooleanType booleanType() const;

  /** Get the type for sorts. */
  KindType kindType() const;

  /** Get the type for reals. */
  RealType realType() const;

  /** Get the type for integers */
  IntegerType integerType() const;

  /**
   * Make a unary expression of a given kind (NOT, BVNOT, ...).
   * @param kind the kind of expression
   * @param child1 kind the kind of expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1);

  /**
   * Make a binary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1, Expr child2);

  /**
   * Make a 3-ary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @param child3 the third child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3);

  /**
   * Make a 4-ary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @param child3 the third child of the new expression
   * @param child4 the fourth child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4);

  /**
   * Make a 5-ary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @param child3 the third child of the new expression
   * @param child4 the fourth child of the new expression
   * @param child5 the fifth child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4,
              Expr child5);

  /**
   * Make an n-ary expression of given kind given a vector of its
   * children
   *
   * @param kind the kind of expression to build
   * @param children the subexpressions
   * @return the n-ary expression
   */
  Expr mkExpr(Kind kind, const std::vector<Expr>& children);

  /**
   * Make a nullary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @return the nullary expression
   */
  Expr mkExpr(Expr opExpr);

  /**
   * Make a unary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the subexpression
   * @return the unary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1);

  /**
   * Make a binary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the first subexpression
   * @param child2 the second subexpression
   * @return the binary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1, Expr child2);

  /**
   * Make a ternary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the first subexpression
   * @param child2 the second subexpression
   * @param child3 the third subexpression
   * @return the ternary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3);

  /**
   * Make a quaternary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the first subexpression
   * @param child2 the second subexpression
   * @param child3 the third subexpression
   * @param child4 the fourth subexpression
   * @return the quaternary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3, Expr child4);

  /**
   * Make a quinary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the first subexpression
   * @param child2 the second subexpression
   * @param child3 the third subexpression
   * @param child4 the fourth subexpression
   * @param child5 the fifth subexpression
   * @return the quinary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3, Expr child4,
              Expr child5);

  /**
   * Make an n-ary expression of given operator to apply and a vector
   * of its children
   *
   * @param opExpr the operator expression
   * @param children the subexpressions
   * @return the n-ary expression
   */
  Expr mkExpr(Expr opExpr, const std::vector<Expr>& children);

  /** Create a constant of type T */
  template <class T>
  Expr mkConst(const T&);

  /**
   * Create an Expr by applying an associative operator to the children.
   * If <code>children.size()</code> is greater than the max arity for
   * <code>kind</code>, then the expression will be broken up into
   * suitably-sized chunks, taking advantage of the associativity of
   * <code>kind</code>. For example, if kind <code>FOO</code> has max arity
   * 2, then calling <code>mkAssociative(FOO,a,b,c)</code> will return
   * <code>(FOO (FOO a b) c)</code> or <code>(FOO a (FOO b c))</code>.
   * The order of the arguments will be preserved in a left-to-right
   * traversal of the resulting tree.
   */
  Expr mkAssociative(Kind kind, const std::vector<Expr>& children);


  /** Make a function type from domain to range. */
  FunctionType mkFunctionType(Type domain, Type range);

  /**
   * Make a function type with input types from argTypes.
   * <code>argTypes</code> must have at least one element.
   */
  FunctionType mkFunctionType(const std::vector<Type>& argTypes, Type range);

  /**
   * Make a function type with input types from
   * <code>sorts[0..sorts.size()-2]</code> and result type
   * <code>sorts[sorts.size()-1]</code>. <code>sorts</code> must have
   * at least 2 elements.
   */
  FunctionType mkFunctionType(const std::vector<Type>& sorts);

  /**
   * Make a predicate type with input types from
   * <code>sorts</code>. The result with be a function type with range
   * <code>BOOLEAN</code>. <code>sorts</code> must have at least one
   * element.
   */
  FunctionType mkPredicateType(const std::vector<Type>& sorts);

  /**
   * Make a tuple type with types from
   * <code>types[0..types.size()-1]</code>.  <code>types</code> must
   * have at least 2 elements.
   */
  TupleType mkTupleType(const std::vector<Type>& types);

  /** Make a type representing a bit-vector of the given size. */
  BitVectorType mkBitVectorType(unsigned size) const;

  /** Make the type of arrays with the given parameterization. */
  ArrayType mkArrayType(Type indexType, Type constituentType) const;

  /** Make a type representing the given datatype. */
  DatatypeType mkDatatypeType(const Datatype& datatype);

  /**
   * Make a set of types representing the given datatypes, which may be
   * mutually recursive.
   */
  std::vector<DatatypeType> mkMutualDatatypeTypes(const std::vector<Datatype>& datatypes);

  /**
   * Make a type representing a constructor with the given parameterization.
   */
  ConstructorType mkConstructorType(const Datatype::Constructor& constructor, Type range) const;

  /** Make a type representing a selector with the given parameterization. */
  SelectorType mkSelectorType(Type domain, Type range) const;

  /** Make a type representing a tester with the given parameterization. */
  TesterType mkTesterType(Type domain) const;

  /** Make a new sort with the given name. */
  SortType mkSort(const std::string& name) const;

  /** Make a new sort from a constructor. */
  SortType mkSort(SortConstructorType constructor,
                  const std::vector<TypeNode>& children) const;

  /** Make a sort constructor from a name and arity. */
  SortConstructorType mkSortConstructor(const std::string& name,
                                        size_t arity) const;

  /** Get the type of an expression */
  Type getType(Expr e, bool check = false)
    throw (TypeCheckingException);

  // variables are special, because duplicates are permitted
  Expr mkVar(const std::string& name, Type type);
  Expr mkVar(Type type);

  /** Returns the minimum arity of the given kind. */
  static unsigned minArity(Kind kind);

  /** Returns the maximum arity of the given kind. */
  static unsigned maxArity(Kind kind);
};

${mkConst_instantiations}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */

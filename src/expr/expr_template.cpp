/*********************                                                        */
/*! \file expr_template.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public-facing expression interface, implementation.
 **
 ** Public-facing expression interface, implementation.
 **/

#include "expr/expr.h"
#include "expr/node.h"
#include "expr/expr_manager_scope.h"
#include "expr/variable_type_map.h"
#include "util/Assert.h"
#include "expr/pickle.h"

#include <vector>

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 35 "${template}"

using namespace CVC4::kind;

namespace CVC4 {

class ExprManager;

namespace expr {

const int ExprSetDepth::s_iosIndex = std::ios_base::xalloc();
const int ExprPrintTypes::s_iosIndex = std::ios_base::xalloc();
const int ExprSetLanguage::s_iosIndex = std::ios_base::xalloc();

}/* CVC4::expr namespace */

std::ostream& operator<<(std::ostream& out, const TypeCheckingException& e) {
  return out << e.getMessage() << ": " << e.getExpression();
}

std::ostream& operator<<(std::ostream& out, const Expr& e) {
  ExprManagerScope ems(*e.getExprManager());
  return out << e.getNode();
}

TypeCheckingException::TypeCheckingException(const TypeCheckingException& t)
: Exception(t.d_msg), d_expr(new Expr(t.getExpression()))
  {}


TypeCheckingException::TypeCheckingException(const Expr& expr, std::string message)
: Exception(message), d_expr(new Expr(expr))
{
}

TypeCheckingException::TypeCheckingException(ExprManager* em,
                                             const TypeCheckingExceptionPrivate* exc)
: Exception(exc->getMessage()), d_expr(new Expr(em, new Node(exc->getNode())))
{
}

TypeCheckingException::~TypeCheckingException() throw () {
  delete d_expr;
}

std::string TypeCheckingException::toString() const {
  std::stringstream ss;
  ss << "Error type-checking " << d_expr << ": " << d_msg << std::endl << *d_expr;
  return ss.str();
}

Expr TypeCheckingException::getExpression() const {
  return *d_expr;
}

Expr::Expr() :
  d_node(new Node),
  d_exprManager(NULL) {
}

Expr::Expr(ExprManager* em, Node* node) :
  d_node(node),
  d_exprManager(em) {
}

Expr::Expr(const Expr& e) :
  d_node(new Node(*e.d_node)),
  d_exprManager(e.d_exprManager) {
}

Expr::Expr(uintptr_t n) :
  d_node(new Node),
  d_exprManager(NULL) {

  AlwaysAssert(n == 0);
}

Expr::~Expr() {
  ExprManagerScope ems(*this);
  delete d_node;
}

ExprManager* Expr::getExprManager() const {
  return d_exprManager;
}

namespace expr {

static Node exportConstant(TNode n, NodeManager* to);

Node exportInternal(TNode n, ExprManager* from, ExprManager* to, VariableTypeMap& vmap) {
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    return exportConstant(n, NodeManager::fromExprManager(to));
  } else if(n.getMetaKind() == kind::metakind::VARIABLE) {
    Expr from_e(from, new Node(n));
    Expr& to_e = vmap[from_e];
    if(! to_e.isNull()) {
Debug("export") << "+ mapped `" << from_e << "' to `" << to_e << "'" << std::endl;
      return to_e.getNode();
    } else {
      // construct new variable in other manager:
      // to_e is a ref, so this inserts from_e -> to_e
      std::string name;
      Type type = from->exportType(from_e.getType(), to, vmap);
      if(Node::fromExpr(from_e).getAttribute(VarNameAttr(), name)) {
        to_e = to->mkVar(name, type);// FIXME thread safety
Debug("export") << "+ exported var `" << from_e << "'[" << from_e.getId() << "] with name `" << name << "' and type `" << from_e.getType() << "' to `" << to_e << "'[" << to_e.getId() << "] with type `" << type << "'" << std::endl;
      } else {
        to_e = to->mkVar(type);// FIXME thread safety
Debug("export") << "+ exported unnamed var `" << from_e << "' with type `" << from_e.getType() << "' to `" << to_e << "' with type `" << type << "'" << std::endl;
      }
      vmap[to_e] = from_e;// insert other direction too
      return Node::fromExpr(to_e);
    }
  } else {
    std::vector<Node> children;
Debug("export") << "n: " << n << std::endl;
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
Debug("export") << "+ parameterized, op is " << n.getOperator() << std::endl;
      children.reserve(n.getNumChildren() + 1);
      children.push_back(exportInternal(n.getOperator(), from, to, vmap));
    } else {
      children.reserve(n.getNumChildren());
    }
    for(TNode::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
Debug("export") << "+ child: " << *i << std::endl;
      children.push_back(exportInternal(*i, from, to, vmap));
    }
    if(Debug.isOn("export")) {
      ExprManagerScope ems(*to);
      Debug("export") << "children for export from " << n << std::endl;
      for(std::vector<Node>::iterator i = children.begin(), i_end = children.end(); i != i_end; ++i) {
        Debug("export") << "  child: " << *i << std::endl;
      }
    }
    return NodeManager::fromExprManager(to)->mkNode(n.getKind(), children);// FIXME thread safety
  }
}/* exportInternal() */

}/* CVC4::expr namespace */

Expr Expr::exportTo(ExprManager* exprManager, VariableTypeMap& variableMap) {
  if(Debug.isOn("pickle")) {
    expr::pickle::Pickler::debugPickleTest(*this);
  }
  Assert(d_exprManager != exprManager,
         "No sense in cloning an Expr in the same ExprManager");
  ExprManagerScope ems(*this);
  return Expr(exprManager, new Node(expr::exportInternal(*d_node, d_exprManager, exprManager, variableMap)));
}

Expr& Expr::operator=(const Expr& e) {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");

  ExprManagerScope ems(*this);
  *d_node = *e.d_node;
  d_exprManager = e.d_exprManager;

  return *this;
}

bool Expr::operator==(const Expr& e) const {
  if(d_exprManager != e.d_exprManager) {
    return false;
  }
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  return *d_node == *e.d_node;
}

bool Expr::operator!=(const Expr& e) const {
  return !(*this == e);
}

bool Expr::operator<(const Expr& e) const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  if(isNull() && !e.isNull()) {
    return true;
  }
  ExprManagerScope ems(*this);
  return *d_node < *e.d_node;
}

bool Expr::operator>(const Expr& e) const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  if(isNull() && !e.isNull()) {
    return true;
  }
  ExprManagerScope ems(*this);
  return *d_node > *e.d_node;
}

unsigned Expr::getId() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getId();
}

Kind Expr::getKind() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getKind();
}

size_t Expr::getNumChildren() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getNumChildren();
}

Expr Expr::getChild(unsigned int i) const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(i >= 0 && i < d_node->getNumChildren(), "Child index out of bounds");
  return Expr(d_exprManager,new Node((*d_node)[i]));
}

bool Expr::hasOperator() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->hasOperator();
}

Expr Expr::getOperator() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  CheckArgument(d_node->hasOperator(), *this,
                "Expr::getOperator() called on an Expr with no operator");
  return Expr(d_exprManager, new Node(d_node->getOperator()));
}

Type Expr::getType(bool check) const throw (TypeCheckingException) {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_exprManager->getType(*this, check);
}

std::string Expr::toString() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->toString();
}

bool Expr::isNull() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isNull();
}

Expr::operator bool() const {
  return !isNull();
}

bool Expr::isConst() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isConst();
}

void Expr::toStream(std::ostream& out, int depth, bool types,
                    OutputLanguage language) const {
  ExprManagerScope ems(*this);
  d_node->toStream(out, depth, types, language);
}

Node Expr::getNode() const throw() {
  return *d_node;
}

TNode Expr::getTNode() const throw() {
  return *d_node;
}

BoolExpr::BoolExpr() {
}

BoolExpr::BoolExpr(const Expr& e) :
  Expr(e) {
}

BoolExpr BoolExpr::notExpr() const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  return d_exprManager->mkExpr(NOT, *this);
}

BoolExpr BoolExpr::andExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(AND, *this, e);
}

BoolExpr BoolExpr::orExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(OR, *this, e);
}

BoolExpr BoolExpr::xorExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(XOR, *this, e);
}

BoolExpr BoolExpr::iffExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(IFF, *this, e);
}

BoolExpr BoolExpr::impExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(IMPLIES, *this, e);
}

BoolExpr BoolExpr::iteExpr(const BoolExpr& then_e,
                           const BoolExpr& else_e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == then_e.d_exprManager, then_e,
                "Different expression managers!");
  CheckArgument(d_exprManager == else_e.d_exprManager, else_e,
                "Different expression managers!");
  return d_exprManager->mkExpr(ITE, *this, then_e, else_e);
}

Expr BoolExpr::iteExpr(const Expr& then_e, const Expr& else_e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == then_e.getExprManager(), then_e,
                "Different expression managers!");
  CheckArgument(d_exprManager == else_e.getExprManager(), else_e,
                "Different expression managers!");
  return d_exprManager->mkExpr(ITE, *this, then_e, else_e);
}

void Expr::printAst(std::ostream & o, int indent) const {
  ExprManagerScope ems(*this);
  getNode().printAst(o, indent);
}

void Expr::debugPrint() {
#ifndef CVC4_MUZZLE
  printAst(Warning());
  Warning().flush();
#endif /* ! CVC4_MUZZLE */
}

${getConst_implementations}

namespace expr {

static Node exportConstant(TNode n, NodeManager* to) {
  Assert(n.getMetaKind() == kind::metakind::CONSTANT);
  switch(n.getKind()) {
${exportConstant_cases}

  default: Unhandled(n.getKind());
  }
}/* exportConstant() */

}/* CVC4::expr namespace */
}/* CVC4 namespace */

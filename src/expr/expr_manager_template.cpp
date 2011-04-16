/*********************                                                        */
/*! \file expr_manager_template.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters, cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public-facing expression manager interface, implementation.
 **
 ** Public-facing expression manager interface, implementation.
 **/

#include "expr/node_manager.h"
#include "expr/expr_manager.h"
#include "context/context.h"
#include "util/options.h"
#include "util/stats.h"

#include <map>

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 34 "${template}"

#ifdef CVC4_STATISTICS_ON
  #define INC_STAT(kind) \
  { \
    if (d_exprStatistics[kind] == NULL) { \
      stringstream statName; \
      statName << "expr::ExprManager::" << kind; \
      d_exprStatistics[kind] = new IntStat(statName.str(), 0); \
      StatisticsRegistry::registerStat(d_exprStatistics[kind]); \
    } \
    ++ *(d_exprStatistics[kind]); \
  }
  #define INC_STAT_VAR(type) \
  { \
    TypeNode* typeNode = Type::getTypeNode(type); \
    TypeConstant type = typeNode->getKind() == kind::TYPE_CONSTANT ? typeNode->getConst<TypeConstant>() : LAST_TYPE; \
    if (d_exprStatisticsVars[type] == NULL) { \
      stringstream statName; \
      if (type == LAST_TYPE) { \
        statName << "expr::ExprManager::VARIABLE:Parametrized type"; \
      } else { \
        statName << "expr::ExprManager::VARIABLE:" << type; \
      } \
      d_exprStatisticsVars[type] = new IntStat(statName.str(), 0); \
      StatisticsRegistry::registerStat(d_exprStatisticsVars[type]); \
    } \
    ++ *(d_exprStatisticsVars[type]); \
  }
#else
  #define INC_STAT(kind)
  #define INC_STAT_VAR(type)
#endif

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {

ExprManager::ExprManager() :
  d_ctxt(new Context),
  d_nodeManager(new NodeManager(d_ctxt, this)) {
#ifdef CVC4_STATISTICS_ON
  for (unsigned i = 0; i < kind::LAST_KIND; ++ i) {
    d_exprStatistics[i] = NULL;
  }
  for (unsigned i = 0; i <= LAST_TYPE; ++ i) {
    d_exprStatisticsVars[i] = NULL;
  }
#endif
}

ExprManager::ExprManager(const Options& options) :
  d_ctxt(new Context),
  d_nodeManager(new NodeManager(d_ctxt, this, options)) {
#ifdef CVC4_STATISTICS_ON
  for (unsigned i = 0; i <= LAST_TYPE; ++ i) {
    d_exprStatisticsVars[i] = NULL;
  }
  for (unsigned i = 0; i < kind::LAST_KIND; ++ i) {
    d_exprStatistics[i] = NULL;
  }
#endif
}

ExprManager::~ExprManager() {
#ifdef CVC4_STATISTICS_ON
  NodeManagerScope nms(d_nodeManager);
  for (unsigned i = 0; i < kind::LAST_KIND; ++ i) {
    if (d_exprStatistics[i] != NULL) {
      StatisticsRegistry::unregisterStat(d_exprStatistics[i]);
      delete d_exprStatistics[i];
    }
  }
  for (unsigned i = 0; i <= LAST_TYPE; ++ i) {
    if (d_exprStatisticsVars[i] != NULL) {
      StatisticsRegistry::unregisterStat(d_exprStatisticsVars[i]);
      delete d_exprStatisticsVars[i];
    }
  }
#endif
  delete d_nodeManager;
  delete d_ctxt;
}

BooleanType ExprManager::booleanType() const {
  NodeManagerScope nms(d_nodeManager);
  return BooleanType(Type(d_nodeManager, new TypeNode(d_nodeManager->booleanType())));
}

KindType ExprManager::kindType() const {
  NodeManagerScope nms(d_nodeManager);
  return KindType(Type(d_nodeManager, new TypeNode(d_nodeManager->kindType())));
}

RealType ExprManager::realType() const {
  NodeManagerScope nms(d_nodeManager);
  return RealType(Type(d_nodeManager, new TypeNode(d_nodeManager->realType())));
}

IntegerType ExprManager::integerType() const {
  NodeManagerScope nms(d_nodeManager);
  return IntegerType(Type(d_nodeManager, new TypeNode(d_nodeManager->integerType())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1) {
  const unsigned n = 1;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind, child1.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2) {
  const unsigned n = 2;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3) {
  const unsigned n = 3;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3, const Expr& child4) {
  const unsigned n = 4;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3, const Expr& child4,
                         const Expr& child5) {
  const unsigned n = 5;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode(),
                                               child5.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, const std::vector<Expr>& children) {
  const unsigned n = children.size();
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);

  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  vector<Expr>::const_iterator it = children.begin();
  vector<Expr>::const_iterator it_end = children.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind, nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, const std::vector<Expr>& children) {
  const unsigned n = children.size();
  Kind kind = kind::operatorKindToKind(opExpr.getKind());
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);

  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  vector<Expr>::const_iterator it = children.begin();
  vector<Expr>::const_iterator it_end = children.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  try {
    INC_STAT(kind);
    return Expr(this,d_nodeManager->mkNodePtr(opExpr.getNode(), nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

/** Make a function type from domain to range. */
FunctionType ExprManager::mkFunctionType(const Type& domain, const Type& range) {
  NodeManagerScope nms(d_nodeManager);
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(*domain.d_typeNode, *range.d_typeNode))));
}

/** Make a function type with input types from argTypes. */
FunctionType ExprManager::mkFunctionType(const std::vector<Type>& argTypes, const Type& range) {
  NodeManagerScope nms(d_nodeManager);
  Assert( argTypes.size() >= 1 );
  std::vector<TypeNode> argTypeNodes;
  for (unsigned i = 0, i_end = argTypes.size(); i < i_end; ++ i) {
    argTypeNodes.push_back(*argTypes[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(argTypeNodes, *range.d_typeNode))));
}

FunctionType ExprManager::mkFunctionType(const std::vector<Type>& sorts) {
  NodeManagerScope nms(d_nodeManager);
  Assert( sorts.size() >= 2 );
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0, i_end = sorts.size(); i < i_end; ++ i) {
     sortNodes.push_back(*sorts[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(sortNodes))));
}

FunctionType ExprManager::mkPredicateType(const std::vector<Type>& sorts) {
  NodeManagerScope nms(d_nodeManager);
  Assert( sorts.size() >= 1 );
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0, i_end = sorts.size(); i < i_end; ++ i) {
     sortNodes.push_back(*sorts[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkPredicateType(sortNodes))));
}

TupleType ExprManager::mkTupleType(const std::vector<Type>& types) {
  NodeManagerScope nms(d_nodeManager);
  Assert( types.size() >= 2 );
  std::vector<TypeNode> typeNodes;
  for (unsigned i = 0, i_end = types.size(); i < i_end; ++ i) {
     typeNodes.push_back(*types[i].d_typeNode);
  }
  return TupleType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkTupleType(typeNodes))));
}

BitVectorType ExprManager::mkBitVectorType(unsigned size) const {
  NodeManagerScope nms(d_nodeManager);
  return BitVectorType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkBitVectorType(size))));
}

ArrayType ExprManager::mkArrayType(Type indexType, Type constituentType) const {
  NodeManagerScope nms(d_nodeManager);
  return ArrayType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkArrayType(*indexType.d_typeNode, *constituentType.d_typeNode))));
}

DatatypeType ExprManager::mkDatatypeType(const Datatype& datatype) {
  NodeManagerScope nms(d_nodeManager);
  TypeNode* typeNode = new TypeNode(d_nodeManager->mkTypeConst(datatype));
  Type type(d_nodeManager, typeNode);
  DatatypeType dtt(type);
  const Datatype& dt = typeNode->getConst<Datatype>();
  if(!dt.isResolved()) {
    std::map<std::string, DatatypeType> resolutions;
    resolutions.insert(std::make_pair(datatype.getName(), dtt));
    const_cast<Datatype&>(dt).resolve(this, resolutions);
  }
  return dtt;
}

std::vector<DatatypeType> ExprManager::mkMutualDatatypeTypes(const std::vector<Datatype>& datatypes) {
  NodeManagerScope nms(d_nodeManager);
  std::map<std::string, DatatypeType> resolutions;
  std::vector<DatatypeType> dtts;
  for(std::vector<Datatype>::const_iterator i = datatypes.begin(), i_end = datatypes.end();
      i != i_end;
      ++i) {
    TypeNode* typeNode = new TypeNode(d_nodeManager->mkTypeConst(*i));
    Type type(d_nodeManager, typeNode);
    DatatypeType dtt(type);
    CheckArgument(resolutions.find((*i).getName()) == resolutions.end(),
                  datatypes,
                  "cannot construct two datatypes at the same time with the same name `%s'",
                  (*i).getName().c_str());
    resolutions.insert(std::make_pair((*i).getName(), dtt));
    dtts.push_back(dtt);
  }
  for(std::vector<DatatypeType>::iterator i = dtts.begin(), i_end = dtts.end();
      i != i_end;
      ++i) {
    const Datatype& dt = (*i).getDatatype();
    if(!dt.isResolved()) {
      const_cast<Datatype&>(dt).resolve(this, resolutions);
    }
  }
  return dtts;
}

ConstructorType ExprManager::mkConstructorType(const Datatype::Constructor& constructor) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkConstructorType(constructor)));
}

SelectorType ExprManager::mkSelectorType(const Type& domain,const Type& range) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkSelectorType(*domain.d_typeNode, *range.d_typeNode)));
}

TesterType ExprManager::mkTesterType(const Type& domain) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkTesterType(*domain.d_typeNode)));
}

SortType ExprManager::mkSort(const std::string& name) const {
  NodeManagerScope nms(d_nodeManager);
  return SortType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkSort(name))));
}

SortConstructorType ExprManager::mkSortConstructor(const std::string& name,
                                                   size_t arity) const {
  NodeManagerScope nms(d_nodeManager);
  return SortConstructorType(Type(d_nodeManager,
              new TypeNode(d_nodeManager->mkSortConstructor(name, arity))));
}

/**
 * Get the type for the given Expr and optionally do type checking.
 *
 * Initial type computation will be near-constant time if
 * type checking is not requested. Results are memoized, so that
 * subsequent calls to getType() without type checking will be
 * constant time.
 *
 * Initial type checking is linear in the size of the expression.
 * Again, the results are memoized, so that subsequent calls to
 * getType(), with or without type checking, will be constant
 * time.
 *
 * NOTE: A TypeCheckingException can be thrown even when type
 * checking is not requested. getType() will always return a
 * valid and correct type and, thus, an exception will be thrown
 * when no valid or correct type can be computed (e.g., if the
 * arguments to a bit-vector operation aren't bit-vectors). When
 * type checking is not requested, getType() will do the minimum
 * amount of checking required to return a valid result.
 *
 * @param e the Expr for which we want a type
 * @param check whether we should check the type as we compute it
 * (default: false)
 */
Type ExprManager::getType(const Expr& e, bool check) throw (TypeCheckingException) {
  NodeManagerScope nms(d_nodeManager);
  Type t;
  try {
    t = Type(d_nodeManager,
             new TypeNode(d_nodeManager->getType(e.getNode(), check)));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
  return t;
}

Expr ExprManager::mkVar(const std::string& name, const Type& type) {
  NodeManagerScope nms(d_nodeManager);
  Node* n = d_nodeManager->mkVarPtr(name, *type.d_typeNode);
  Debug("nm") << "set " << name << " on " << *n << std::endl;
  INC_STAT_VAR(type);
  return Expr(this, n);
}

Expr ExprManager::mkVar(const Type& type) {
  NodeManagerScope nms(d_nodeManager);
  INC_STAT_VAR(type);
  return Expr(this, d_nodeManager->mkVarPtr(*type.d_typeNode));
}

Expr ExprManager::mkAssociative(Kind kind,
                                const std::vector<Expr>& children) {
  CheckArgument( kind::isAssociative(kind), kind,
                 "Illegal kind in mkAssociative: %s",
                 kind::kindToString(kind).c_str());

  NodeManagerScope nms(d_nodeManager);
  const unsigned int max = maxArity(kind);
  const unsigned int min = minArity(kind);
  unsigned int numChildren = children.size();

  /* If the number of children is within bounds, then there's nothing to do. */
  if( numChildren <= max ) {
    return mkExpr(kind,children);
  }

  std::vector<Expr>::const_iterator it = children.begin() ;
  std::vector<Expr>::const_iterator end = children.end() ;

  /* The new top-level children and the children of each sub node */
  std::vector<Node> newChildren;
  std::vector<Node> subChildren;

  while( it != end && numChildren > max ) {
    /* Grab the next max children and make a node for them. */
    for( std::vector<Expr>::const_iterator next = it + max;
         it != next;
         ++it, --numChildren ) {
      subChildren.push_back(it->getNode());
    }
    Node subNode = d_nodeManager->mkNode(kind,subChildren);
    newChildren.push_back(subNode);

    subChildren.clear();
  }

  /* If there's children left, "top off" the Expr. */
  if(numChildren > 0) {
    /* If the leftovers are too few, just copy them into newChildren;
     * otherwise make a new sub-node  */
    if(numChildren < min) {
      for(; it != end; ++it) {
        newChildren.push_back(it->getNode());
      }
    } else {
      for(; it != end; ++it) {
        subChildren.push_back(it->getNode());
      }
      Node subNode = d_nodeManager->mkNode(kind, subChildren);
      newChildren.push_back(subNode);
    }
  }

  /* It's inconceivable we could have enough children for this to fail
   * (more than 2^32, in most cases?). */
  AlwaysAssert( newChildren.size() <= max,
                "Too many new children in mkAssociative" );

  /* It would be really weird if this happened (it would require
   * min > 2, for one thing), but let's make sure. */
  AlwaysAssert( newChildren.size() >= min,
                "Too few new children in mkAssociative" );

  return Expr(this, d_nodeManager->mkNodePtr(kind,newChildren) );
}

unsigned ExprManager::minArity(Kind kind) {
  return metakind::getLowerBoundForKind(kind);
}

unsigned ExprManager::maxArity(Kind kind) {
  return metakind::getUpperBoundForKind(kind);
}

NodeManager* ExprManager::getNodeManager() const {
  return d_nodeManager;
}

Context* ExprManager::getContext() const {
  return d_ctxt;
}

${mkConst_implementations}

}/* CVC4 namespace */

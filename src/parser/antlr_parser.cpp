/*********************                                                        */
/** antlr_parser.cpp
 ** Original author: dejan
 ** Major contributors: cconway
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A super-class for ANTLR-generated input language parsers
 **/

/*
 * antlr_parser.cpp
 *
 *  Created on: Nov 30, 2009
 *      Author: dejan
 */

#include <iostream>
#include <limits.h>
#include <antlr3.h>

#include "antlr_parser.h"
#include "semantic_exception.h"
#include "util/output.h"
#include "util/Assert.h"
#include "expr/command.h"
#include "expr/type.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

AntlrParser::AntlrParser(const std::string& filename) :
    d_filename(filename), d_checksEnabled(true) {
}

Expr AntlrParser::getSymbol(const std::string& name, SymbolType type) {
  Assert( isDeclared(name, type) );


  switch( type ) {

  case SYM_VARIABLE: // Functions share var namespace
  case SYM_FUNCTION:
    return d_varSymbolTable.getObject(name);

  default:
    Unhandled("Unhandled symbol type!");
  }
}

Expr AntlrParser::getVariable(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

Expr AntlrParser::getFunction(const std::string& name) {
  return getSymbol(name, SYM_FUNCTION);
}

const Type* 
AntlrParser::getType(const std::string& var_name,
                     SymbolType type) {
  Assert( isDeclared(var_name, type) );
  const Type* t = getSymbol(var_name,type).getType();
  return t;
}

const Type* AntlrParser::getSort(const std::string& name) {
  Assert( isDeclared(name, SYM_SORT) );
  const Type* t = d_sortTable.getObject(name);
  return t;
}

/* Returns true if name is bound to a boolean variable. */
bool AntlrParser::isBoolean(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name)->isBoolean();
}

/* Returns true if name is bound to a function. */
bool AntlrParser::isFunction(const std::string& name) {
  return isDeclared(name, SYM_FUNCTION) && getType(name)->isFunction();
}

/* Returns true if name is bound to a function returning boolean. */
bool AntlrParser::isPredicate(const std::string& name) {
  return isDeclared(name, SYM_FUNCTION) && getType(name)->isPredicate();
}

Expr AntlrParser::getTrueExpr() const {
  return d_exprManager->mkExpr(TRUE);
}

Expr AntlrParser::getFalseExpr() const {
  return d_exprManager->mkExpr(FALSE);
}

Expr AntlrParser::mkExpr(Kind kind, const Expr& child) {
  Expr result = d_exprManager->mkExpr(kind, child);
  Debug("parser") << "mkExpr() => " << result << std::endl;
  return result;
}

Expr AntlrParser::mkExpr(Kind kind, const Expr& child_1, const Expr& child_2) {
  Expr result = d_exprManager->mkExpr(kind, child_1, child_2);
  Debug("parser") << "mkExpr() => " << result << std::endl;
  return result;
}

Expr AntlrParser::mkExpr(Kind kind, const Expr& child_1, const Expr& child_2,
                         const Expr& child_3) {
  Expr result = d_exprManager->mkExpr(kind, child_1, child_2, child_3);
  Debug("parser") << "mkExpr() => " << result << std::endl;
  return result;
}

Expr AntlrParser::mkExpr(Kind kind, const std::vector<Expr>& children) {
  Expr result = d_exprManager->mkExpr(kind, children);
  Debug("parser") << "mkExpr() => " << result << std::endl;
  return result;
}

const Type* 
AntlrParser::functionType(const Type* domainType, 
                          const Type* rangeType) {
  return d_exprManager->mkFunctionType(domainType,rangeType);
}

const Type* 
AntlrParser::functionType(const std::vector<const Type*>& argTypes, 
                          const Type* rangeType) {
  Assert( argTypes.size() > 0 );
  return d_exprManager->mkFunctionType(argTypes,rangeType);
}

const Type* 
AntlrParser::functionType(const std::vector<const Type*>& sorts) {
  Assert( sorts.size() > 0 );
  if( sorts.size() == 1 ) {
    return sorts[0];
  } else {
    std::vector<const Type*> argTypes(sorts);
    const Type* rangeType = argTypes.back();
    argTypes.pop_back();
    return functionType(argTypes,rangeType);
  }
}

const Type* AntlrParser::predicateType(const std::vector<const Type*>& sorts) {
  if(sorts.size() == 0) {
    return d_exprManager->booleanType();
  } else {
    return d_exprManager->mkFunctionType(sorts, d_exprManager->booleanType());
  }
}

Expr 
AntlrParser::mkVar(const std::string& name, const Type* type) {
  Debug("parser") << "mkVar(" << name << "," << *type << ")" << std::endl;
  Assert( !isDeclared(name) ) ;
  Expr expr = d_exprManager->mkVar(type, name);
  d_varSymbolTable.bindName(name, expr);
  Assert( isDeclared(name) ) ;
  return expr;
}

const std::vector<Expr> 
AntlrParser::mkVars(const std::vector<std::string> names, 
                    const Type* type) {
  std::vector<Expr> vars;
  for(unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkVar(names[i], type));
  }
  return vars;
}


const Type* 
AntlrParser::newSort(const std::string& name) {
  Debug("parser") << "newSort(" << name << ")" << std::endl;
  Assert( !isDeclared(name, SYM_SORT) ) ;
  const Type* type = d_exprManager->mkSort(name);
  d_sortTable.bindName(name, type);
  Assert( isDeclared(name, SYM_SORT) ) ;
  return type;
}

const std::vector<const Type*>
AntlrParser::newSorts(const std::vector<std::string>& names) {
  std::vector<const Type*> types;
  for(unsigned i = 0; i < names.size(); ++i) {
    types.push_back(newSort(names[i]));
  }
  return types;
}

const BooleanType* AntlrParser::booleanType() {
  return d_exprManager->booleanType(); 
}

const KindType* AntlrParser::kindType() {
  return d_exprManager->kindType(); 
}

unsigned int AntlrParser::minArity(Kind kind) {
  switch(kind) {
  case FALSE:
  case SKOLEM:
  case TRUE:
  case VARIABLE:
    return 0;

  case AND:
  case NOT:
  case OR:
    return 1;

  case APPLY:
  case EQUAL: 
  case IFF:
  case IMPLIES:
  case PLUS:
  case XOR:
    return 2;

  case ITE:
    return 3;

  default:
    Unhandled("kind in minArity");
  }
}

unsigned int AntlrParser::maxArity(Kind kind) {
  switch(kind) {
  case FALSE:
  case SKOLEM:
  case TRUE:
  case VARIABLE:
    return 0;

  case NOT:
    return 1;

  case EQUAL: 
  case IFF:
  case IMPLIES:
  case XOR:
    return 2;

  case ITE:
    return 3;

  case AND:
  case APPLY:
  case PLUS:
  case OR:
    return UINT_MAX;

  default:
    Unhandled("kind in maxArity");
  }
}

void AntlrParser::setExpressionManager(ExprManager* em) {
  d_exprManager = em;
}

bool AntlrParser::isDeclared(const std::string& name, SymbolType type) {
  switch(type) {
  case SYM_VARIABLE: // Functions share var namespace
  case SYM_FUNCTION:
    return d_varSymbolTable.isBound(name);
  case SYM_SORT:
    return d_sortTable.isBound(name);
  default:
    Unhandled("Unhandled symbol type!");
  }
}

void AntlrParser::parseError(const std::string& message)
    throw (SemanticException) {
  pANTLR3_LEXER lexer = getAntlrLexer();
  throw SemanticException(message, getFilename(), lexer->getLine(lexer),
                          lexer->getCharPositionInLine(lexer));
}

void AntlrParser::checkDeclaration(const std::string& varName,
                                   DeclarationCheck check,
                                   SymbolType type)
    throw (SemanticException) {
  if(!d_checksEnabled) {
    return;
  }

  switch(check) {
  case CHECK_DECLARED:
    if( !isDeclared(varName, type) ) {
      parseError("Symbol " + varName + " not declared");
    }
    break;

  case CHECK_UNDECLARED:
    if( isDeclared(varName, type) ) {
      parseError("Symbol " + varName + " previously declared");
    }
    break;

  case CHECK_NONE:
    break;

  default:
    Unhandled("Unknown check type!");
  }
}

void AntlrParser::checkFunction(const std::string& name)
  throw (SemanticException) {
  if( d_checksEnabled && !isFunction(name) ) {
    parseError("Expecting function symbol, found '" + name + "'");
  } 
}

void AntlrParser::checkArity(Kind kind, unsigned int numArgs)
  throw (SemanticException) {
  if(!d_checksEnabled) {
    return;
  }

  unsigned int min = minArity(kind);
  unsigned int max = maxArity(kind);

  if( numArgs < min || numArgs > max ) {
    stringstream ss;
    ss << "Expecting ";
    if( numArgs < min ) {
      ss << "at least " << min << " ";
    } else {
      ss << "at most " << max << " ";
    }
    ss << "arguments for operator '" << kind << "', ";
    ss << "found " << numArgs;
    parseError(ss.str());
  }
}

void AntlrParser::enableChecks() {
  d_checksEnabled = true;
}

void AntlrParser::disableChecks() {
  d_checksEnabled = false;
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

/*********************                                                        */
/*! \file parser.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): ajreynol
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Parser state implementation.
 **
 ** Parser state implementation.
 **/

#include <iostream>
#include <fstream>
#include <iterator>
#include <stdint.h>

#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "expr/command.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "util/output.h"
#include "util/options.h"
#include "util/Assert.h"
#include "parser/cvc/cvc_input.h"
#include "parser/smt/smt_input.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

Parser::Parser(ExprManager* exprManager, Input* input, bool strictMode, bool parseOnly) :
  d_exprManager(exprManager),
  d_input(input),
  d_declScopeAllocated(),
  d_declScope(&d_declScopeAllocated),
  d_anonymousFunctionCount(0),
  d_done(false),
  d_checksEnabled(true),
  d_strictMode(strictMode),
  d_parseOnly(parseOnly) {
  d_input->setParser(*this);
}

Expr Parser::getSymbol(const std::string& name, SymbolType type) {
  checkDeclaration(name, CHECK_DECLARED, type);
  Assert( isDeclared(name, type) );

  switch( type ) {

  case SYM_VARIABLE: // Functions share var namespace
    return d_declScope->lookup(name);

  default:
    Unhandled(type);
  }
}


Expr Parser::getVariable(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

Expr Parser::getFunction(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

Type Parser::getType(const std::string& var_name,
                     SymbolType type) {
  checkDeclaration(var_name, CHECK_DECLARED, type);
  Assert( isDeclared(var_name, type) );
  Type t = getSymbol(var_name, type).getType();
  return t;
}

Type Parser::getSort(const std::string& name) {
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  Assert( isDeclared(name, SYM_SORT) );
  Type t = d_declScope->lookupType(name);
  return t;
}

Type Parser::getSort(const std::string& name,
                     const std::vector<Type>& params) {
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  Assert( isDeclared(name, SYM_SORT) );
  Type t = d_declScope->lookupType(name, params);
  return t;
}

size_t Parser::getArity(const std::string& sort_name){
  checkDeclaration(sort_name, CHECK_DECLARED, SYM_SORT);
  Assert( isDeclared(sort_name, SYM_SORT) );
  return d_declScope->lookupArity(sort_name);
}

/* Returns true if name is bound to a boolean variable. */
bool Parser::isBoolean(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name).isBoolean();
}

/* Returns true if name is bound to a function-like thing (function,
 * constructor, tester, or selector). */
bool Parser::isFunctionLike(const std::string& name) {
  if(!isDeclared(name, SYM_VARIABLE)) {
    return false;
  }
  Type type = getType(name);
  return type.isFunction() || type.isConstructor() ||
    type.isTester() || type.isSelector();
}

/* Returns true if name is bound to a defined function. */
bool Parser::isDefinedFunction(const std::string& name) {
  // more permissive in type than isFunction(), because defined
  // functions can be zero-ary and declared functions cannot.
  return d_declScope->isBoundDefinedFunction(name);
}

/* Returns true if the Expr is a defined function. */
bool Parser::isDefinedFunction(Expr func) {
  // more permissive in type than isFunction(), because defined
  // functions can be zero-ary and declared functions cannot.
  return d_declScope->isBoundDefinedFunction(func);
}

/* Returns true if name is bound to a function returning boolean. */
bool Parser::isPredicate(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name).isPredicate();
}

Expr
Parser::mkVar(const std::string& name, const Type& type) {
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  Expr expr = d_exprManager->mkVar(name, type);
  defineVar(name, expr);
  return expr;
}

Expr
Parser::mkFunction(const std::string& name, const Type& type) {
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  Expr expr = d_exprManager->mkVar(name, type);
  defineFunction(name, expr);
  return expr;
}

Expr
Parser::mkAnonymousFunction(const std::string& prefix, const Type& type) {
  stringstream name;
  name << prefix << ':' << ++d_anonymousFunctionCount;
  return mkFunction(name.str(), type);
}

std::vector<Expr>
Parser::mkVars(const std::vector<std::string> names,
               const Type& type) {
  std::vector<Expr> vars;
  for(unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkVar(names[i], type));
  }
  return vars;
}

void
Parser::defineVar(const std::string& name, const Expr& val) {
  d_declScope->bind(name, val);
  Assert( isDeclared(name) );
}

void
Parser::defineFunction(const std::string& name, const Expr& val) {
  d_declScope->bindDefinedFunction(name, val);
  Assert( isDeclared(name) );
}

void
Parser::defineType(const std::string& name, const Type& type) {
  d_declScope->bindType(name, type);
  Assert( isDeclared(name, SYM_SORT) );
}

void
Parser::defineType(const std::string& name,
                   const std::vector<Type>& params,
                   const Type& type) {
  d_declScope->bindType(name, params, type);
  Assert( isDeclared(name, SYM_SORT) );
}

void
Parser::defineParameterizedType(const std::string& name,
                                const std::vector<Type>& params,
                                const Type& type) {
  if(Debug.isOn("parser")) {
    Debug("parser") << "defineParameterizedType(" << name << ", " << params.size() << ", [";
    if(params.size() > 0) {
      copy(params.begin(), params.end() - 1,
           ostream_iterator<Type>(Debug("parser"), ", ") );
      Debug("parser") << params.back();
    }
    Debug("parser") << "], " << type << ")" << std::endl;
  }
  defineType(name, params, type);
}

SortType
Parser::mkSort(const std::string& name) {
  Debug("parser") << "newSort(" << name << ")" << std::endl;
  Type type = d_exprManager->mkSort(name);
  defineType(name, type);
  return type;
}

SortConstructorType
Parser::mkSortConstructor(const std::string& name, size_t arity) {
  Debug("parser") << "newSortConstructor(" << name << ", " << arity << ")"
                  << std::endl;
  SortConstructorType type = d_exprManager->mkSortConstructor(name, arity);
  defineType(name, vector<Type>(arity), type);
  return type;
}

SortType Parser::mkUnresolvedType(const std::string& name) {
  SortType unresolved = mkSort(name);
  d_unresolved.insert(unresolved);
  return unresolved;
}

SortConstructorType
Parser::mkUnresolvedTypeConstructor(const std::string& name,
                                    size_t arity) {
  SortConstructorType unresolved = mkSortConstructor(name, arity);
  d_unresolved.insert(unresolved);
  return unresolved;
}

SortConstructorType
Parser::mkUnresolvedTypeConstructor(const std::string& name,
                                    const std::vector<Type>& params) {
  Debug("parser") << "newSortConstructor(P)(" << name << ", " << params.size() << ")"
                  << std::endl;
  SortConstructorType unresolved = d_exprManager->mkSortConstructor(name, params.size());
  defineType(name, params, unresolved);
  Type t = getSort( name, params );
  d_unresolved.insert(unresolved);
  return unresolved;
}

bool Parser::isUnresolvedType(const std::string& name) {
  if(!isDeclared(name, SYM_SORT)) {
    return false;
  }
  return d_unresolved.find(getSort(name)) != d_unresolved.end();
}

std::vector<DatatypeType>
Parser::mkMutualDatatypeTypes(const std::vector<Datatype>& datatypes) {

  std::vector<DatatypeType> types =
    d_exprManager->mkMutualDatatypeTypes(datatypes, d_unresolved);

  Assert(datatypes.size() == types.size());

  for(unsigned i = 0; i < datatypes.size(); ++i) {
    DatatypeType t = types[i];
    const Datatype& dt = t.getDatatype();
    const std::string& name = dt.getName();
    Debug("parser-idt") << "define " << name << " as " << t << std::endl;
    if(isDeclared(name, SYM_SORT)) {
      throw ParserException(name + " already declared");
    }
    if( t.isParametric() ) {
      std::vector< Type > paramTypes = t.getParamTypes();
      defineType(name, paramTypes, t );
    } else {
      defineType(name, t);
    }
    for(Datatype::const_iterator j = dt.begin(),
          j_end = dt.end();
        j != j_end;
        ++j) {
      const Datatype::Constructor& ctor = *j;
      Expr::printtypes::Scope pts(Debug("parser-idt"), true);
      Expr constructor = ctor.getConstructor();
      Debug("parser-idt") << "+ define " << constructor << std::endl;
      string constructorName = constructor.toString();
      if(isDeclared(constructorName, SYM_VARIABLE)) {
        throw ParserException(constructorName + " already declared");
      }
      defineVar(constructorName, constructor);
      Expr tester = ctor.getTester();
      Debug("parser-idt") << "+ define " << tester << std::endl;
      string testerName = tester.toString();
      if(isDeclared(testerName, SYM_VARIABLE)) {
        throw ParserException(testerName + " already declared");
      }
      defineVar(testerName, tester);
      for(Datatype::Constructor::const_iterator k = ctor.begin(),
            k_end = ctor.end();
          k != k_end;
          ++k) {
        Expr selector = (*k).getSelector();
        Debug("parser-idt") << "+++ define " << selector << std::endl;
        string selectorName = selector.toString();
        if(isDeclared(selectorName, SYM_VARIABLE)) {
          throw ParserException(selectorName + " already declared");
        }
        defineVar(selectorName, selector);
      }
    }
  }

  // These are no longer used, and the ExprManager would have
  // complained of a bad substitution if anything is left unresolved.
  // Clear out the set.
  d_unresolved.clear();

  return types;
}

bool Parser::isDeclared(const std::string& name, SymbolType type) {
  switch(type) {
  case SYM_VARIABLE:
    return d_declScope->isBound(name);
  case SYM_SORT:
    return d_declScope->isBoundType(name);
  default:
    Unhandled(type);
  }
}

void Parser::checkDeclaration(const std::string& varName,
                              DeclarationCheck check,
                              SymbolType type)
    throw(ParserException) {
  if(!d_checksEnabled) {
    return;
  }

  switch(check) {
  case CHECK_DECLARED:
    if( !isDeclared(varName, type) ) {
      parseError("Symbol " + varName + " not declared as a " +
                 (type == SYM_VARIABLE ? "variable" : "type"));
    }
    break;

  case CHECK_UNDECLARED:
    if( isDeclared(varName, type) ) {
      parseError("Symbol " + varName + " previously declared as a " +
                 (type == SYM_VARIABLE ? "variable" : "type"));
    }
    break;

  case CHECK_NONE:
    break;

  default:
    Unhandled(check);
  }
}

void Parser::checkFunctionLike(const std::string& name) throw(ParserException) {
  if(d_checksEnabled && !isFunctionLike(name)) {
    parseError("Expecting function-like symbol, found '" + name + "'");
  }
}

void Parser::checkArity(Kind kind, unsigned numArgs)
  throw(ParserException) {
  if(!d_checksEnabled) {
    return;
  }

  unsigned min = d_exprManager->minArity(kind);
  unsigned max = d_exprManager->maxArity(kind);

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

void Parser::checkOperator(Kind kind, unsigned numArgs) throw(ParserException) {
  if( d_strictMode && d_logicOperators.find(kind) == d_logicOperators.end() ) {
    parseError( "Operator is not defined in the current logic: " + kindToString(kind) );
  }
  checkArity(kind, numArgs);
}

void Parser::addOperator(Kind kind) {
  d_logicOperators.insert(kind);
}

void Parser::preemptCommand(Command* cmd) {
  d_commandQueue.push_back(cmd);
}

Command* Parser::nextCommand() throw(ParserException) {
  Debug("parser") << "nextCommand()" << std::endl;
  Command* cmd = NULL;
  if(!d_commandQueue.empty()) {
    cmd = d_commandQueue.front();
    d_commandQueue.pop_front();
    if(cmd == NULL) {
      setDone();
    }
  } else {
    if(!done()) {
      try {
        cmd = d_input->parseCommand();
        d_commandQueue.push_back(cmd);
        cmd = d_commandQueue.front();
        d_commandQueue.pop_front();
        if(cmd == NULL) {
          setDone();
        }
      } catch(ParserException& e) {
        setDone();
        throw;
      } catch(Exception& e) {
        setDone();
        stringstream ss;
        // set the language of the stream, otherwise if it contains
        // Exprs or Types it prints in the AST language
        OutputLanguage outlang =
          language::toOutputLanguage(d_input->getLanguage());
        ss << Expr::setlanguage(outlang) << e;
        parseError( ss.str() );
      }
    }
  }
  Debug("parser") << "nextCommand() => " << cmd << std::endl;
  return cmd;
}

Expr Parser::nextExpression() throw(ParserException) {
  Debug("parser") << "nextExpression()" << std::endl;
  Expr result;
  if(!done()) {
    try {
      result = d_input->parseExpr();
      if(result.isNull()) {
        setDone();
      }
    } catch(ParserException& e) {
      setDone();
      throw;
    } catch(Exception& e) {
      setDone();
      stringstream ss;
      ss << e;
      parseError( ss.str() );
    }
  }
  Debug("parser") << "nextExpression() => " << result << std::endl;
  return result;
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

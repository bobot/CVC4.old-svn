/* *******************                                                        */
/*  Cvc.g
 ** Original author: cconway
 ** Major contributors: dejan, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser for CVC-LIB input language.
 **/

grammar Cvc;

options {
  language = 'C';                  // C output for antlr
//  defaultErrorHandler = false;      // Skip the default error handling, just break with exceptions
  k = 2;
}

@header {
/**
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **/
}

@lexer::includes {
/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#define ANTLR3_INLINE_INPUT_ASCII
}

@parser::includes {
#include "expr/command.h"
#include "parser/input.h"

namespace CVC4 {
  class Expr;
namespace parser {
  class CvcInput;
}
}

extern
void SetCvcInput(CVC4::parser::CvcInput* input);

}

@parser::postinclude {
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/input.h"
#include "parser/cvc/cvc_input.h"
#include "util/output.h"
#include <vector>

using namespace CVC4;
using namespace CVC4::parser;
}

@members {
CVC4::parser::CvcInput *input;

extern
void SetCvcInput(CVC4::parser::CvcInput* _input) {
  input = _input;
}
}

/**
 * Parses an expression.
 * @return the parsed expression
 */
parseExpr returns [CVC4::Expr expr]
  : formula[expr]
  | EOF
  ;

/**
 * Parses a command (the whole benchmark)
 * @return the command of the benchmark
 */
parseCommand returns [CVC4::Command* cmd]
  : c = command { $cmd = c; }
  ;

/**
 * Matches a command of the input. If a declaration, it will return an empty
 * command.
 */
command returns [CVC4::Command* cmd = 0]
@init {
  Expr f;
  Debug("parser") << "command: " << LT(1)->getText() << endl;
}
  : ASSERT_TOK   f = formula  SEMICOLON { cmd = new AssertCommand(f);   }
  | QUERY_TOK    f = formula  SEMICOLON { cmd = new QueryCommand(f);    }
  | CHECKSAT_TOK f = formula  SEMICOLON { cmd = new CheckSatCommand(f); }
  | CHECKSAT_TOK              SEMICOLON { cmd = new CheckSatCommand(getTrueExpr()); }
  | PUSH                  SEMICOLON { cmd = new PushCommand(); }
  | POP_TOK                   SEMICOLON { cmd = new PopCommand(); }
  | cmd = declaration
  | EOF
  ;

/**
 * Match a declaration
 */

declaration returns [CVC4::DeclarationCommand* cmd]
@init {
  vector<string> ids;
  Type* t;
  Debug("parser") << "declaration: " << LT(1)->getText() << endl;
}
  : // FIXME: These could be type or function declarations, if that matters.
    identifierList[ids, CHECK_UNDECLARED, SYM_VARIABLE] COLON t = declType[ids] SEMICOLON
    { cmd = new DeclarationCommand(ids,t); }
  ;

/** Match the right-hand side of a declaration. Returns the type. */
declType[std::vector<std::string>& idList] returns [CVC4::Type* t]
@init {
  Debug("parser") << "declType: " << LT(1)->getText() << endl;
}
  : /* A sort declaration (e.g., "T : TYPE") */
    TYPE_TOK { newSorts(idList); t = kindType(); }
  | /* A variable declaration */
    t = type { mkVars(idList,t); }
  ;

/**
 * Match the type in a declaration and do the declaration binding.
 * TODO: Actually parse sorts into Type objects.
 */
type returns  [CVC4::Type* t]
@init {
  Type *t1, *t2;
  Debug("parser") << "type: " << LT(1)->getText() << endl;
}
  : /* Simple type */
    t = baseType
  | /* Single-parameter function type */
    t1 = baseType RIGHT_ARROW t2 = baseType
    { t = functionType(t1,t2); }
  | /* Multi-parameter function type */
    LPAREN t1 = baseType
    { std::vector<Type*> argTypes;
      argTypes.push_back(t1); }
    (COMMA t1 = baseType { argTypes.push_back(t1); } )+
    RPAREN ARROW_TOK t2 = baseType
    { t = functionType(argTypes,t2); }
  ;

/**
 * Matches a list of identifiers separated by a comma and puts them in the
 * given list.
 * @param idList the list to fill with identifiers.
 * @param check what kinds of check to perform on the symbols
 */
identifierList[std::vector<std::string>& idList,
               CVC4::parser::DeclarationCheck check,
               CVC4::parser::SymbolType type]
@init {
  string id;
}
  : id = identifier[check,type] { idList.push_back(id); }
      (COMMA id = identifier[check] { idList.push_back(id); })*
  ;


/**
 * Matches an identifier and returns a string.
 */
identifier[CVC4::parser::DeclarationCheck check,
           CVC4::parser::SymbolType type]
returns [std::string id]
  : IDENTIFIER
    { id = AntlrInput::tokenText($IDENTIFIER);
      checkDeclaration(id, check, type); }
  ;

/**
 * Matches a type.
 * TODO: parse more types
 */
baseType returns [CVC4::Type* t]
@init {
  std::string id;
  Debug("parser") << "base type: " << LT(1)->getText() << endl;
}
  : BOOLEAN_TOK { t = booleanType(); }
  | t = typeSymbol
  ;

/**
 * Matches a type identifier
 */
typeSymbol returns [CVC4::Type* t]
@init {
  std::string id;
  Debug("parser") << "type symbol: " << LT(1)->getText() << endl;
}
  : id = identifier[CHECK_DECLARED,SYM_SORT]
    { t = getSort(id); }
  ;

/**
 * Matches a CVC4 formula.
 * @return the expression representing the formula
 */
formula returns [CVC4::Expr formula]
@init {
  Debug("parser") << "formula: " << LT(1)->getText() << endl;
}
  :  formula = iffFormula
  ;

/**
 * Matches a comma-separated list of formulas
 */
formulaList[std::vector<CVC4::Expr>& formulas]
@init {
  Expr f;
}
  : f = formula { formulas.push_back(f); }
    ( COMMA f = formula
      { formulas.push_back(f); }
    )*
  ;

/**
 * Matches a Boolean IFF formula (right-associative)
 */
iffFormula returns [CVC4::Expr f]
@init {
  Expr e;
  Debug("parser") << "<=> formula: " << LT(1)->getText() << endl;
}
  : f = impliesFormula
    ( IFF_TOK e = iffFormula
        { f = mkExpr(CVC4::kind::IFF, f, e); }
    )?
  ;

/**
 * Matches a Boolean IMPLIES formula (right-associative)
 */
impliesFormula returns [CVC4::Expr f]
@init {
  Expr e;
  Debug("parser") << "=> Formula: " << LT(1)->getText() << endl;
}
  : f = orFormula
    ( IMPLIES_TOK e = impliesFormula
        { f = mkExpr(CVC4::kind::IMPLIES, f, e); }
    )?
  ;

/**
 * Matches a Boolean OR formula (left-associative)
 */
orFormula returns [CVC4::Expr f]
@init {
  Expr e;
  vector<Expr> exprs;
  Debug("parser") << "OR Formula: " << LT(1)->getText() << endl;
}
  : e = xorFormula { exprs.push_back(e); }
      ( OR_TOK e = xorFormula { exprs.push_back(e); } )*
    {
      f = (exprs.size() > 1 ? mkExpr(CVC4::kind::OR, exprs) : exprs[0]);
    }
  ;

/**
 * Matches a Boolean XOR formula (left-associative)
 */
xorFormula returns [CVC4::Expr f]
@init {
  Expr e;
  Debug("parser") << "XOR formula: " << LT(1)->getText() << endl;
}
  : f = andFormula
    ( XOR_TOK e = andFormula
      { f = mkExpr(CVC4::kind::XOR,f, e); }
    )*
  ;

/**
 * Matches a Boolean AND formula (left-associative)
 */
andFormula returns [CVC4::Expr f]
@init {
  Expr e;
  vector<Expr> exprs;
  Debug("parser") << "AND Formula: " << LT(1)->getText() << endl;
}
  : e = notFormula { exprs.push_back(e); }
    ( AND_TOK e = notFormula { exprs.push_back(e); } )*
    {
      f = (exprs.size() > 1 ? mkExpr(CVC4::kind::AND, exprs) : exprs[0]);
    }
  ;

/**
 * Parses a NOT formula.
 * @return the expression representing the formula
 */
notFormula returns [CVC4::Expr f]
@init {
  Debug("parser") << "NOT formula: " << LT(1)->getText() << endl;
}
  : /* negation */
    NOT_TOK f = notFormula
    { f = mkExpr(CVC4::kind::NOT, f); }
  | /* a boolean atom */
    f = predFormula
  ;

predFormula returns [CVC4::Expr f]
@init {
  Debug("parser") << "predicate formula: " << LT(1)->getText() << endl;
}
  : { Expr e; }
    f = term
    (EQUAL_TOK e = term
      { f = mkExpr(CVC4::kind::EQUAL, f, e); }
    )?
  ; // TODO: lt, gt, etc.

/**
 * Parses a term.
 */
term returns [CVC4::Expr t]
@init {
  std::string name;
  Debug("parser") << "term: " << LT(1)->getText() << endl;
}
  : /* function application */
    // { isFunction(LT(1)->getText()) }?
    { Expr f;
      std::vector<CVC4::Expr> args; }
    f = functionSymbol[CHECK_DECLARED]
    { args.push_back( f ); }

    LPAREN formulaList[args] RPAREN
    // TODO: check arity
    { t = mkExpr(CVC4::kind::APPLY, args); }

  | /* if-then-else */
    t = iteTerm

  | /* parenthesized sub-formula */
    LPAREN t = formula RPAREN

    /* constants */
  | TRUE_TOK  { t = getTrueExpr(); }
  | FALSE_TOK { t = getFalseExpr(); }

  | /* variable */
    name = identifier[CHECK_DECLARED,SYM_VARIABLE]
    { t = getVariable(name); }
  ;

/**
 * Parses an ITE term.
 */
iteTerm returns [CVC4::Expr t]
@init {
  Expr iteCondition, iteThen, iteElse;
  Debug("parser") << "ite: " << LT(1)->getText() << endl;
}
  : IF_TOK iteCondition = formula
    THEN_TOK iteThen = formula
    iteElse = iteElseTerm
    ENDIF_TOK
    { t = mkExpr(CVC4::kind::ITE, iteCondition, iteThen, iteElse); }
  ;

/**
 * Parses the else part of the ITE, i.e. ELSE f, or ELSIF b THEN f1 ...
 */
iteElseTerm returns [CVC4::Expr t]
@init {
  Expr iteCondition, iteThen, iteElse;
  Debug("parser") << "else: " << LT(1)->getText() << endl;
}
  : ELSE_TOK t = formula
  | ELSEIF_TOK iteCondition = formula
    THEN_TOK iteThen = formula
    iteElse = iteElseTerm
    { t = mkExpr(CVC4::kind::ITE, iteCondition, iteThen, iteElse); }
  ;

/**
 * Parses a function symbol (an identifier).
 * @param what kind of check to perform on the id
 * @return the predicate symol
 */
functionSymbol[CVC4::parser::DeclarationCheck check] returns [CVC4::Expr f]
@init {
  Debug("parser") << "function symbol: " << LT(1)->getText() << endl;
  std::string name;
}
  : name = identifier[check,SYM_FUNCTION]
    { checkFunction(name);
      f = getFunction(name); }
  ;


// Keywords

AND_TOK : 'AND';
ASSERT_TOK : 'ASSERT';
BOOLEAN_TOK : 'BOOLEAN';
CHECKSAT_TOK : 'CHECKSAT';
ECHO_TOK : 'ECHO';
ELSEIF_TOK : 'ELSIF';
ELSE_TOK : 'ELSE';
ENDIF_TOK : 'ENDIF';
FALSE_TOK : 'FALSE';
IF_TOK : 'IF';
NOT_TOK : 'NOT';
OR_TOK : 'OR';
POPTO_TOK : 'POPTO';
POP_TOK : 'POP';
PRINT_TOK : 'PRINT';
PUSH_TOK : 'PUSH';
QUERY_TOK : 'QUERY';
THEN_TOK : 'THEN';
TRUE_TOK : 'TRUE';
TYPE_TOK : 'TYPE';
XOR_TOK : 'XOR';

// Symbols

COLON : ':';
COMMA : ',';
LPAREN : '(';
RPAREN : ')';
SEMICOLON : ';';

// Operators

IMPLIES_TOK : '=>';
IFF_TOK     : '<=>';
ARROW_TOK : '->';
EQUAL_TOK   : '=';

/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER : ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*;

/**
 * Matches a numeral from the input (non-empty sequence of digits).
 */
NUMERAL: (DIGIT)+;

/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment ALPHA : 'a'..'z' | 'A'..'Z';

/**
 * Matches the digits (0-9)
 */
fragment DIGIT : '0'..'9';

/**
 * Matches and skips whitespace in the input and ignores it.
 */
WHITESPACE : (' ' | '\t' | '\f' | '\r' | '\n') { $channel = HIDDEN;; };

/**
 * Matches the comments and ignores them
 */
COMMENT : '%' (~('\n' | '\r'))* { $channel = HIDDEN;; };


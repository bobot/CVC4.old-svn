/* *******************                                                        */
/*  Smt.g
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
 ** Parser for SMT-LIB input language.
 **/

grammar Smt;

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
 * Otherwise, we have to let the lexer detect the encoding at runtime and
 * take the performance hit.
 */
#define ANTLR3_INLINE_INPUT_ASCII
}

@parser::includes {
#include "expr/command.h"
#include "parser/parser.h"

namespace CVC4 {
  class Expr;
namespace parser {
  class Smt;
}
}

extern
void SetSmt(CVC4::parser::Smt* smt);

}

@parser::postinclude {
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/parser.h"
#include "parser/smt/smt_parser.h"
#include "util/output.h"
#include <vector>

using namespace CVC4;
using namespace CVC4::parser;
}

@members {
CVC4::parser::Smt *smt;
CVC4::Node currentNode;
  
extern
void SetSmt(CVC4::parser::Smt* newSmt) {
  smt = newSmt;
}

inline static
std::string tokenText(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  ANTLR3_MARKER end = token->getStopIndex(token);
  std::string txt( (const char *)start, end-start+1 );
  Debug("parser-extra") << "tokenText: start=" << start << std::endl
                        <<  "end=" << end << std::endl
                        <<  "txt='" << txt << "'" << std::endl;
  return txt;
}
}

/**
 * Parses an expression.
 * @return the parsed CVC4::Nodeession
 */
parseExpr returns [CVC4::Node expr]
  : annotatedFormula[expr]
  | EOF
  ;

/**
 * Parses a command (the whole benchmark)
 * @return the command of the benchmark
 */
parseCommand returns [CVC4::Command* cmd]
  : b = benchmark { $cmd = b; }
  ;

/**
 * Matches the whole SMT-LIB benchmark.
 * @return the sequence command containing the whole problem
 */
benchmark returns [CVC4::Command* cmd]
  : TOK_LPAREN TOK_BENCHMARK IDENTIFIER c = benchAttributes TOK_RPAREN 
  	{ $cmd = c; }
  | EOF { $cmd = 0; }
  ;

/**
 * Matches a sequence of benchmark attributes and returns a pointer to a
 * command sequence.
 * @return the command sequence
 */
benchAttributes returns [CVC4::CommandSequence* cmd_seq]
@init {
  cmd_seq = new CommandSequence();
}
  : (cmd = benchAttribute { if (cmd) cmd_seq->addCommand(cmd); } )+
  ;

/**
 * Matches a benchmark attribute, sucha as ':logic', ':formula', and returns
 * a corresponding command
 * @return a command corresponding to the attribute
 */
benchAttribute returns [CVC4::Command* smt_command]
@declarations { 
  std::string name;
  BenchmarkStatus b_status;
}
  : TOK_LOGIC identifier[name,CHECK_NONE,SYM_VARIABLE]
    { smt_command = new SetBenchmarkLogicCommand(name);   }
  | TOK_ASSUMPTION annotatedFormula[currentNode]
    { smt_command = new AssertCommand(smt->toExpr(currentNode));   }
  | TOK_FORMULA annotatedFormula[currentNode]
    { smt_command = new CheckSatCommand(smt->toExpr(currentNode)); }
  | TOK_STATUS status[b_status]                   
    { smt_command = new SetBenchmarkStatusCommand(b_status); }        
  | TOK_EXTRAFUNS TOK_LPAREN (functionDeclaration)+ TOK_RPAREN  
  | TOK_EXTRAPREDS TOK_LPAREN (predicateDeclaration)+ TOK_RPAREN  
  | TOK_EXTRASORTS TOK_LPAREN (sortDeclaration)+ TOK_RPAREN  
  | TOK_NOTES STRING_LITERAL        
  | annotation
  ;

/**
 * Matches an annotated formula.
 * @return the expression representing the formula
 */
annotatedFormula[CVC4::Node& formula]
@init {
  Debug("parser") << "annotated formula: " << tokenText(LT(1)) << std::endl;
  Kind kind;
  std::string name;
  std::vector<Node> args; /* = getExprVector(); */
} 
  : /* a built-in operator application */
    TOK_LPAREN builtinOp[kind] annotatedFormulas[args] TOK_RPAREN 
    { smt->checkArity(kind, args.size());
      formula = smt->mkNode(kind,args); }

  | /* A non-built-in function application */

    // Semantic predicate not necessary if parenthesized subexpressions
    // are disallowed
    // { isFunction(LT(2)->getText()) }? 

    TOK_LPAREN 
    functionSymbol[currentNode]
    { args.push_back(currentNode); }
    annotatedFormulas[args] TOK_RPAREN
    // TODO: check arity
    { formula = smt->mkNode(CVC4::kind::APPLY,args); }

  | /* An ite expression */
    TOK_LPAREN (TOK_ITE | TOK_IF_THEN_ELSE) 
    annotatedFormula[currentNode]
    { args.push_back(currentNode); } 
    annotatedFormula[currentNode]
    { args.push_back(currentNode); } 
    annotatedFormula[currentNode]
    { args.push_back(currentNode); } 
    TOK_RPAREN
    { formula = smt->mkNode(CVC4::kind::ITE, args); }

  | /* a variable */
    identifier[name,CHECK_DECLARED,SYM_VARIABLE]
    { formula = smt->getVariable(name); }

    /* constants */
  | TOK_TRUE          { formula = smt->getTrueNode(); }
  | TOK_FALSE         { formula = smt->getFalseNode(); }
    /* TODO: let, flet, quantifiers, arithmetic constants */
  ;

/**
 * Matches a sequence of annotaed formulas and puts them into the formulas
 * vector.
 * @param formulas the vector to fill with formulas
 */   
annotatedFormulas[std::vector<CVC4::Node>& formulas]
  : ( annotatedFormula[currentNode] { formulas.push_back(currentNode); } )+
  ;

/**
* Matches on of the unary Boolean connectives.
* @return the kind of the Bollean connective
*/
builtinOp[CVC4::Kind& kind]
@init {
  Debug("parser") << "builtin: " << tokenText(LT(1)) << std::endl;
}
  : TOK_NOT      { $kind = CVC4::kind::NOT;     }
  | TOK_IMPLIES  { $kind = CVC4::kind::IMPLIES; }
  | TOK_AND      { $kind = CVC4::kind::AND;     }
  | TOK_OR       { $kind = CVC4::kind::OR;      }
  | TOK_XOR      { $kind = CVC4::kind::XOR;     }
  | TOK_IFF      { $kind = CVC4::kind::IFF;     }
  | TOK_EQUAL    { $kind = CVC4::kind::EQUAL;   }
    /* TODO: lt, gt, plus, minus, etc. */
  ;

/**
 * Matches a (possibly undeclared) predicate identifier (returning the string). 
 * @param check what kind of check to do with the symbol
 */
predicateName[std::string& name, CVC4::parser::DeclarationCheck check]
  :  functionName[name,check]
  ;

/**
 * Matches a (possibly undeclared) function identifier (returning the string)
 * @param check what kind of check to do with the symbol
 */
functionName[std::string& name, CVC4::parser::DeclarationCheck check]
  :  identifier[name,check,SYM_FUNCTION] 
  ;

/**
 * Matches an previously declared function symbol (returning an Expr)
 */
functionSymbol[CVC4::Node& fun]
@declarations {
	std::string name;
}
  : functionName[name,CHECK_DECLARED]
    { smt->checkFunction(name);
      fun = smt->getFunction(name); }
  ;
  
/**
 * Matches an attribute name from the input (:attribute_name).
 */
attribute
  :  ATTR_IDENTIFIER
  ;



functionDeclaration
@declarations {
  std::string name;
  std::vector<const Type*> sorts;
}
  : TOK_LPAREN functionName[name,CHECK_UNDECLARED] 
      t = sortSymbol // require at least one sort
    { sorts.push_back(t); }
      sortList[sorts] TOK_RPAREN
    { t = smt->functionType(sorts);
      smt->mkVar(name, t); } 
  ;
              
/**
 * Matches the declaration of a predicate and declares it
 */
predicateDeclaration
@declarations {
  std::string name;
  std::vector<const Type*> p_sorts;
}
  : TOK_LPAREN predicateName[name,CHECK_UNDECLARED] sortList[p_sorts] TOK_RPAREN
    { const Type *t = smt->predicateType(p_sorts);
      smt->mkVar(name, t); } 
  ;

sortDeclaration 
@declarations {
  std::string name;
}
  : sortName[name,CHECK_UNDECLARED]
    { smt->newSort(name); }
  ;
  
/**
 * Matches a sequence of sort symbols and fills them into the given vector.
 */
sortList[std::vector<const CVC4::Type*>& sorts]
  : ( t = sortSymbol { sorts.push_back(t); })* 
  ;

/**
 * Matches the sort symbol, which can be an arbitrary identifier.
 * @param check the check to perform on the name
 */
sortName[std::string& name, CVC4::parser::DeclarationCheck check] 
  : identifier[name,check,SYM_SORT] 
  ;

sortSymbol returns [const CVC4::Type* t]
@declarations {
  std::string name;
}
  : sortName[name,CHECK_NONE] 
  	{ $t = smt->getSort(name); }
  ;

/**
 * Matches the status of the benchmark, one of 'sat', 'unsat' or 'unknown'.
 */
status[ CVC4::BenchmarkStatus& status ]
  : TOK_SAT       { $status = SMT_SATISFIABLE;    }
  | TOK_UNSAT     { $status = SMT_UNSATISFIABLE;  }
  | TOK_UNKNOWN   { $status = SMT_UNKNOWN;        }
  ;

/**
 * Matches an annotation, which is an attribute name, with an optional user
 */
annotation
  : attribute (USER_VALUE)?
  ;

/**
 * Matches an identifier and returns a string.
 * @param check what kinds of check to do on the symbol
 * @return the id string
 */
identifier[std::string& id,
		   CVC4::parser::DeclarationCheck check, 
           CVC4::parser::SymbolType type] 
@init {
  id = tokenText(LT(1));
  Debug("parser") << "identifier: " << id
                  << " check? " << toString(check)
                  << " type? " << toString(type) << std::endl;
}
  : IDENTIFIER
    { Assert( id == tokenText( $IDENTIFIER ) );
      smt->checkDeclaration(id, check,type); }
  ;

// Base SMT-LIB tokens
TOK_DISTINCT      : 'distinct';
TOK_ITE           : 'ite';
TOK_IF_THEN_ELSE  : 'if_then_else';
TOK_TRUE          : 'true';
TOK_FALSE         : 'false';
TOK_NOT           : 'not';
TOK_IMPLIES       : 'implies';
TOK_AND           : 'and';
TOK_OR            : 'or';
TOK_XOR           : 'xor';
TOK_IFF           : 'iff';
TOK_EXISTS        : 'exists';
TOK_FORALL        : 'forall';
TOK_LET           : 'let';
TOK_FLET          : 'flet';
TOK_THEORY        : 'theory';
TOK_SAT           : 'sat';
TOK_UNSAT         : 'unsat';
TOK_UNKNOWN       : 'unknown';
TOK_BENCHMARK     : 'benchmark';

// The SMT attribute tokens
TOK_LOGIC       : ':logic';
TOK_ASSUMPTION  : ':assumption';
TOK_FORMULA     : ':formula';
TOK_STATUS      : ':status';
TOK_EXTRASORTS  : ':extrasorts';
TOK_EXTRAFUNS   : ':extrafuns';
TOK_EXTRAPREDS  : ':extrapreds';
TOK_NOTES       : ':notes';

// arithmetic symbols
TOK_EQUAL         : '=';
TOK_LESS_THAN     : '<';
TOK_GREATER_THAN  : '>';
TOK_AMPERSAND     : '&';
TOK_AT            : '@';
TOK_POUND         : '#';
TOK_PLUS          : '+';
TOK_MINUS         : '-';
TOK_STAR          : '*';
TOK_DIV           : '/';
TOK_PERCENT       : '%';
TOK_PIPE          : '|';
TOK_TILDE         : '~';

// Language meta-symbols
TOK_QUESTION      : '?';
TOK_DOLLAR        : '$';
TOK_LPAREN        : '(';
TOK_RPAREN        : ')';

/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER /*options { paraphrase = 'an identifier'; testLiterals = true; }*/
  :  ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*
  ;

/**
 * Matches an identifier starting with a colon. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a colon.
 */
ATTR_IDENTIFIER /*options { paraphrase = 'an identifier starting with a colon'; testLiterals = true; }*/
  :  ':' ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*
  ;

/**
 * Matches the value of user-defined annotations or attributes. The only constraint imposed on a user-defined value is that it start with
 * an open brace and end with closed brace.
 */
USER_VALUE
  :   '{'
      ( ~('{' | '}') )*
    '}'
  ;


/**
 * Matches and skips whitespace in the input.
 */
WHITESPACE /*options { paraphrase = 'whitespace'; }*/
  :  (' ' | '\t' | '\f' | '\r' | '\n')+             { $channel = HIDDEN;; }
  ;

/**
 * Matches a numeral from the input (non-empty sequence of digits).
 */
TOK_NUMERAL /*options { paraphrase = 'a numeral'; }*/
  :  (DIGIT)+
  ;

/**
 * Matches a double quoted string literal. Escaping is supported, and escape
 * character '\' has to be escaped.
 */
STRING_LITERAL /*options { paraphrase = 'a string literal'; }*/
  :  '"' (ESCAPE | ~('"'|'\\'))* '"'
  ;

/**
 * Matches the comments and ignores them
 */
COMMENT /*options { paraphrase = 'comment'; }*/
  : ';' (~('\n' | '\r'))*                    { $channel = HIDDEN;; }
  ;


/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment
ALPHA /*options { paraphrase = 'a letter'; }*/
  :  'a'..'z'
  |  'A'..'Z'
  ;

/**
 * Matches the digits (0-9)
 */
fragment
DIGIT /*options { paraphrase = 'a digit'; }*/
  :   '0'..'9'
  ;


/**
 * Matches an allowed escaped character.
 */
fragment ESCAPE
  : '\\' ('"' | '\\' | 'n' | 't' | 'r')
  ;


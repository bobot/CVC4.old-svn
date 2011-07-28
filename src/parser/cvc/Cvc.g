/* *******************                                                        */
/*! \file Cvc.g
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan, ajreynol
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Parser for CVC presentation input language
 **
 ** Parser for CVC input language.
 **/

grammar Cvc;

options {
  // C output for antlr
  language = 'C';

  // Skip the default error handling, just break with exceptions
  // defaultErrorHandler = false;

  // Only lookahead of <= k requested (disable for LL* parsing)
  // Note that CVC4's BoundedTokenBuffer requires a fixed k !
  // If you change this k, change it also in cvc_input.cpp !
  k = 3;
}/* options */

tokens {
  /* commands */

  ASSERT_TOK = 'ASSERT';
  QUERY_TOK = 'QUERY';
  CHECKSAT_TOK = 'CHECKSAT';
  OPTION_TOK = 'OPTION';
  PUSH_TOK = 'PUSH';
  POP_TOK = 'POP';
  POPTO_TOK = 'POPTO';
  PUSH_SCOPE_TOK = 'PUSH_SCOPE';
  POP_SCOPE_TOK = 'POP_SCOPE';
  POPTO_SCOPE_TOK = 'POPTO_SCOPE';
  RESET_TOK = 'RESET';
  DATATYPE_TOK = 'DATATYPE';
  END_TOK = 'END';
  CONTEXT_TOK = 'CONTEXT';
  FORGET_TOK = 'FORGET';
  GET_TYPE_TOK = 'GET_TYPE';
  CHECK_TYPE_TOK = 'CHECK_TYPE';
  GET_CHILD_TOK = 'GET_CHILD';
  GET_OP_TOK = 'GET_OP';
  SUBSTITUTE_TOK = 'SUBSTITUTE';
  DBG_TOK = 'DBG';
  TRACE_TOK = 'TRACE';
  UNTRACE_TOK = 'UNTRACE';
  HELP_TOK = 'HELP';
  TRANSFORM_TOK = 'TRANSFORM';
  PRINT_TOK = 'PRINT';
  PRINT_TYPE_TOK = 'PRINT_TYPE';
  CALL_TOK = 'CALL';
  ECHO_TOK = 'ECHO';
  EXIT_TOK = 'EXIT';
  INCLUDE_TOK = 'INCLUDE';
  DUMP_PROOF_TOK = 'DUMP_PROOF';
  DUMP_ASSUMPTIONS_TOK = 'DUMP_ASSUMPTIONS';
  DUMP_SIG_TOK = 'DUMP_SIG';
  DUMP_TCC_TOK = 'DUMP_TCC';
  DUMP_TCC_ASSUMPTIONS_TOK = 'DUMP_TCC_ASSUMPTIONS';
  DUMP_TCC_PROOF_TOK = 'DUMP_TCC_PROOF';
  DUMP_CLOSURE_TOK = 'DUMP_CLOSURE';
  DUMP_CLOSURE_PROOF_TOK = 'DUMP_CLOSURE_PROOF';
  WHERE_TOK = 'WHERE';
  ASSERTIONS_TOK = 'ASSERTIONS';
  ASSUMPTIONS_TOK = 'ASSUMPTIONS';
  COUNTEREXAMPLE_TOK = 'COUNTEREXAMPLE';
  COUNTERMODEL_TOK = 'COUNTERMODEL';
  ARITH_VAR_ORDER_TOK = 'ARITH_VAR_ORDER';

  /* operators */

  AND_TOK = 'AND';
  BOOLEAN_TOK = 'BOOLEAN';
  ELSEIF_TOK = 'ELSIF';
  ELSE_TOK = 'ELSE';
  ENDIF_TOK = 'ENDIF';
  FALSE_TOK = 'FALSE';
  IF_TOK = 'IF';
  IN_TOK = 'IN';
  INT_TOK = 'INT';
  LET_TOK = 'LET';
  NOT_TOK = 'NOT';
  OR_TOK = 'OR';
  REAL_TOK = 'REAL';
  THEN_TOK = 'THEN';
  TRUE_TOK = 'TRUE';
  TYPE_TOK = 'TYPE';
  XOR_TOK = 'XOR';

  ARRAY_TOK = 'ARRAY';
  OF_TOK = 'OF';
  WITH_TOK = 'WITH';

  SUBTYPE_TOK = 'SUBTYPE';

  FORALL_TOK = 'FORALL';
  EXISTS_TOK = 'EXISTS';
  PATTERN_TOK = 'PATTERN';

  LAMBDA = 'LAMBDA';

  // Symbols

  COLON = ':';
  COMMA = ',';
  LPAREN = '(';
  RPAREN = ')';
  LBRACE = '{';
  RBRACE = '}';
  LBRACKET = '[';
  RBRACKET = ']';
  SEMICOLON = ';';
  BAR = '|';
  UNDERSCORE = '_';

  SQHASH = '[#';
  HASHSQ = '#]';
  PARENHASH = '(#';
  HASHPAREN = '#)';

  //DOT = '.';
  DOTDOT = '..';

  // Operators

  ARROW_TOK = '->';
  DIV_TOK = '/';
  EQUAL_TOK = '=';
  DISEQUAL_TOK = '/=';
  EXP_TOK = '^';
  GT_TOK = '>';
  GEQ_TOK = '>=';
  IFF_TOK = '<=>';
  IMPLIES_TOK = '=>';
  LT_TOK = '<';
  LEQ_TOK = '<=';
  MINUS_TOK = '-';
  PLUS_TOK = '+';
  STAR_TOK = '*';
  ASSIGN_TOK = ':=';
  MOD_TOK = 'MOD';
  INTDIV_TOK = 'DIV';
  FLOOR_TOK = 'FLOOR';

  // Bitvectors

  BITVECTOR_TOK = 'BITVECTOR';
  LEFTSHIFT_TOK = '<<';
  RIGHTSHIFT_TOK = '>>';
  BVPLUS_TOK = 'BVPLUS';
  BVSUB_TOK = 'BVSUB';
  BVUDIV_TOK = 'BVUDIV';
  BVSDIV_TOK = 'BVSDIV';
  BVUREM_TOK = 'BVUREM';
  BVSREM_TOK = 'BVSREM';
  BVSMOD_TOK = 'BVSMOD';
  BVSHL_TOK = 'BVSHL';
  BVASHR_TOK = 'BVASHR';
  BVLSHR_TOK = 'BVLSHR';
  BVUMINUS_TOK = 'BVUMINUS';
  BVMULT_TOK = 'BVMULT';
  BVNEG_TOK = '~';
  BVAND_TOK = '&';
  BVXOR_TOK = 'BVXOR';
  BVNAND_TOK = 'BVNAND';
  BVNOR_TOK = 'BVNOR';
  BVCOMP_TOK = 'BVCOMP';
  BVXNOR_TOK = 'BVXNOR';
  CONCAT_TOK = '@';
  //BVTOINT_TOK = 'BVTOINT';
  //INTTOBV_TOK = 'INTTOBV';
  //BOOLEXTRACT_TOK = 'BOOLEXTRACT';
  //IS_INTEGER_TOK = 'IS_INTEGER';
  BVLT_TOK = 'BVLT';
  BVGT_TOK = 'BVGT';
  BVLE_TOK = 'BVLE';
  BVGE_TOK = 'BVGE';
  SX_TOK = 'SX';
  BVZEROEXTEND_TOK = 'BVZEROEXTEND';
  BVREPEAT_TOK = 'BVREPEAT';
  BVROTL_TOK = 'BVROTL';
  BVROTR_TOK = 'BVROTR';
  BVSLT_TOK = 'BVSLT';
  BVSGT_TOK = 'BVSGT';
  BVSLE_TOK = 'BVSLE';
  BVSGE_TOK = 'BVSGE';
}/* tokens */

@parser::members {

// Idea and code guidance from Sam Harwell,
// http://www.antlr.org/wiki/display/ANTLR3/Operator+precedence+parser

bool isRightToLeft(int type) {
  // return true here for any operators that are right-to-left associative
  switch(type) {
  case IMPLIES_TOK: return true;
  default: return false;
  }
}/* isRightToLeft() */

int getOperatorPrecedence(int type) {
  switch(type) {
  case BITVECTOR_TOK: return 1;
  //case DOT:
  case LPAREN:
  case LBRACE: return 2;
  case LBRACKET: return 3;
  case ARROW_TOK: return 4;
  //case IS_INTEGER_TOK: return 5;
  case BVSLT_TOK:
  case BVSLE_TOK:
  case BVSGT_TOK:
  case BVSGE_TOK: return 6;
  case BVLT_TOK:
  case BVLE_TOK:
  case BVGT_TOK:
  case BVGE_TOK: return 7;
  case LEFTSHIFT_TOK:
  case RIGHTSHIFT_TOK: return 8;
  case SX_TOK:
  case BVZEROEXTEND_TOK:
  case BVREPEAT_TOK:
  case BVROTL_TOK:
  case BVROTR_TOK: return 9;
  case BVUDIV_TOK:
  case BVSDIV_TOK:
  case BVUREM_TOK:
  case BVSREM_TOK:
  case BVSMOD_TOK:
  case BVSHL_TOK:
  case BVASHR_TOK:
  case BVLSHR_TOK: return 10;
  case BVUMINUS_TOK:
  case BVPLUS_TOK:
  case BVSUB_TOK: return 11;
  case BVNEG_TOK: return 12;
  case BVXNOR_TOK: return 13;
  case BVNOR_TOK:
  case BVCOMP_TOK: return 14;
  case BVNAND_TOK: return 15;
  case BVXOR_TOK: return 16;
  case BVAND_TOK: return 17;
  case BAR: return 18;
  case CONCAT_TOK: return 19;
//case UMINUS_TOK: return 20;
  case WITH_TOK: return 21;
  case EXP_TOK: return 22;
  case STAR_TOK:
  case INTDIV_TOK:
  case DIV_TOK:
  case MOD_TOK: return 23;
  case PLUS_TOK:
  case MINUS_TOK: return 24;
  case LEQ_TOK:
  case LT_TOK:
  case GEQ_TOK:
  case GT_TOK:
  case FLOOR_TOK: return 25;
  case EQUAL_TOK:
  case DISEQUAL_TOK: return 26;
  case NOT_TOK: return 27;
  case AND_TOK: return 28;
  case OR_TOK:
  case XOR_TOK: return 29;
  case IMPLIES_TOK: return 30;// right-to-left
  case IFF_TOK: return 31;
  case FORALL_TOK:
  case EXISTS_TOK: return 32;
  case ASSIGN_TOK:
  case IN_TOK: return 33;

  default:
    Unhandled(CvcParserTokenNames[type]);
  }
}/* getOperatorPrecedence() */

Kind getOperatorKind(int type, bool& negate) {
  negate = false;

  switch(type) {
    // booleanBinop
  case IFF_TOK: return kind::IFF;
  case IMPLIES_TOK: return kind::IMPLIES;
  case OR_TOK: return kind::OR;
  case XOR_TOK: return kind::XOR;
  case AND_TOK: return kind::AND;

    // comparisonBinop
  case EQUAL_TOK: return kind::EQUAL;
  case DISEQUAL_TOK: negate = true; return kind::EQUAL;
  case GT_TOK: return kind::GT;
  case GEQ_TOK: return kind::GEQ;
  case LT_TOK: return kind::LT;
  case LEQ_TOK: return kind::LEQ;

    // arithmeticBinop
  case PLUS_TOK: return kind::PLUS;
  case MINUS_TOK: return kind::MINUS;
  case STAR_TOK: return kind::MULT;
  case INTDIV_TOK: Unhandled(CvcParserTokenNames[type]);
  case DIV_TOK: return kind::DIVISION;
  case EXP_TOK: Unhandled(CvcParserTokenNames[type]);

    // bvBinop
  case CONCAT_TOK: return kind::BITVECTOR_CONCAT;
  case BAR: return kind::BITVECTOR_OR;
  case BVAND_TOK: return kind::BITVECTOR_AND;

  default:
    Unhandled(CvcParserTokenNames[type]);
  }
}/* getOperatorKind() */

unsigned findPivot(const std::vector<unsigned>& operators,
                   unsigned startIndex, unsigned stopIndex) {
  unsigned pivot = startIndex;
  unsigned pivotRank = getOperatorPrecedence(operators[pivot]);
  /*Debug("prec") << "initial pivot at " << pivot
                << "(" << CvcParserTokenNames[operators[pivot]] << ") "
                << "level " << pivotRank << std::endl;*/
  for(unsigned i = startIndex + 1; i <= stopIndex; ++i) {
    unsigned current = getOperatorPrecedence(operators[i]);
    bool rtl = isRightToLeft(operators[i]);
    if(current > pivotRank || (current == pivotRank && !rtl)) {
      /*Debug("prec") << "new pivot at " << i
                    << "(" << CvcParserTokenNames[operators[i]] << ") "
                    << "level " << current << " rtl == " << rtl << std::endl;*/
      pivot = i;
      pivotRank = current;
    }
  }
  return pivot;
}/* findPivot() */

Expr createPrecedenceTree(ExprManager* em,
                          const std::vector<CVC4::Expr>& expressions,
                          const std::vector<unsigned>& operators,
                          unsigned startIndex, unsigned stopIndex) {
  Assert(expressions.size() == operators.size() + 1);
  Assert(startIndex < expressions.size());
  Assert(stopIndex < expressions.size());
  Assert(startIndex <= stopIndex);

  if(stopIndex == startIndex) {
    return expressions[startIndex];
  }

  unsigned pivot = findPivot(operators, startIndex, stopIndex - 1);
  //Debug("prec") << "pivot[" << startIndex << "," << stopIndex - 1 << "] at " << pivot << std::endl;
  bool negate;
  Expr e = em->mkExpr(getOperatorKind(operators[pivot], negate),
                      createPrecedenceTree(em, expressions, operators, startIndex, pivot),
                      createPrecedenceTree(em, expressions, operators, pivot + 1, stopIndex));
  return negate ? em->mkExpr(kind::NOT, e) : e;
}/* createPrecedenceTree() recursive variant */

Expr createPrecedenceTree(ExprManager* em,
                          const std::vector<CVC4::Expr>& expressions,
                          const std::vector<unsigned>& operators) {
  if(Debug.isOn("prec") && operators.size() > 1) {
    for(unsigned i = 0; i < expressions.size(); ++i) {
      Debug("prec") << expressions[i];
      if(operators.size() > i) {
        Debug("prec") << ' ' << CvcParserTokenNames[operators[i]] << ' ';
      }
    }
    Debug("prec") << std::endl;
  }

  Expr e = createPrecedenceTree(em, expressions, operators, 0, expressions.size() - 1);
  if(Debug.isOn("prec") && operators.size() > 1) {
    Expr::setlanguage::Scope ls(Debug("prec"), language::output::LANG_AST);
    Debug("prec") << "=> " << e << std::endl;
  }
  return e;
}/* createPrecedenceTree() base variant */

/** Add n NOTs to the front of e and return the result. */
Expr addNots(ExprManager* em, size_t n, Expr e) {
  while(n-- > 0) {
    e = em->mkExpr(kind::NOT, e);
  }
  return e;
}/* addNots() */

}/* @parser::members */

@header {
/**
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **/
}/* @header */

@lexer::includes {

/** This suppresses warnings about the redefinition of token symbols between different
  * parsers. The redefinitions should be harmless as long as no client: (a) #include's
  * the lexer headers for two grammars AND (b) uses the token symbol definitions. */
#pragma GCC system_header

/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#define ANTLR3_INLINE_INPUT_ASCII

#include "parser/antlr_tracing.h"
#include "util/integer.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"

}/* @lexer::includes */

@parser::includes {

#include <stdint.h>
#include "expr/command.h"
#include "parser/parser.h"
#include "util/subrange_bound.h"
#include "parser/antlr_tracing.h"

namespace CVC4 {
  class Expr;

  namespace parser {
    namespace cvc {
      /**
       * This class is just here to get around an unfortunate bit of Antlr.
       * We use strings below as return values from rules, which require
       * them to be constructible by a void*.  So we derive the string
       * class to provide just such a conversion.
       */
      class myString : public std::string {
      public:
        myString(const std::string& s) : std::string(s) {}
        myString(void*) : std::string() {}
        myString() : std::string() {}
      };/* class myString */

      /**
       * Just exists to give us the void* construction that
       * ANTLR requires.
       */
      class mySubrangeBound : public CVC4::SubrangeBound {
      public:
        mySubrangeBound() : CVC4::SubrangeBound() {}
        mySubrangeBound(void*) : CVC4::SubrangeBound() {}
        mySubrangeBound(const Integer& i) : CVC4::SubrangeBound(i) {}
        mySubrangeBound(const SubrangeBound& b) : CVC4::SubrangeBound(b) {}
      };/* class mySubrangeBound */

      /**
       * Just exists to give us the void* construction that
       * ANTLR requires.
       */
      struct myExpr : public CVC4::Expr {
        myExpr() : CVC4::Expr() {}
        myExpr(void*) : CVC4::Expr() {}
        myExpr(const Expr& e) : CVC4::Expr(e) {}
        myExpr(const myExpr& e) : CVC4::Expr(e) {}
      };/* struct myExpr */

    }/* CVC4::parser::cvc namespace */
  }/* CVC4::parser namespace */
}/* CVC4 namespace */

}/* @parser::includes */

@parser::postinclude {

#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "util/output.h"

#include <vector>

#define REPEAT_COMMAND(k, CommandCtor)                      \
  ({                                                        \
    unsigned __k = (k);                                     \
    (__k <= 1)                                              \
      ? (Command*) new CommandCtor                          \
      : ({                                                  \
          CommandSequence* __seq = new CommandSequence();   \
          while(__k-- > 0) {                                \
            __seq->addCommand(new CommandCtor);             \
          }                                                 \
          (Command*) __seq;                                 \
        });                                                 \
  })

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which will be defined
 * by ANTLR *after* this section. (If they were functions, PARSER would be undefined.) */
#undef PARSER_STATE
#define PARSER_STATE ((Parser*)PARSER->super)
#undef EXPR_MANAGER
#define EXPR_MANAGER PARSER_STATE->getExprManager()
#undef MK_EXPR
#define MK_EXPR EXPR_MANAGER->mkExpr
#undef MK_CONST
#define MK_CONST EXPR_MANAGER->mkConst
#define UNSUPPORTED PARSER_STATE->unimplementedFeature

}/* @parser::postinclude */

/**
 * Parses an expression.
 * @return the parsed expression
 */
parseExpr returns [CVC4::Expr expr = CVC4::Expr()]
  : formula[expr]
  | EOF
  ;

/**
 * Parses a command (the whole benchmark)
 * @return the command of the benchmark
 */
parseCommand returns [CVC4::Command* cmd = NULL]
  : c=command { $cmd = c; }
  | EOF { $cmd = NULL; }
  ;

/**
 * Matches a command of the input. If a declaration, it will return an empty
 * command.
 */
command returns [CVC4::Command* cmd = NULL]
  : ( mainCommand[cmd] SEMICOLON
    | SEMICOLON
    | LET_TOK { PARSER_STATE->pushScope(); }
      typeOrVarLetDecl[CHECK_DECLARED] ( COMMA typeOrVarLetDecl[CHECK_DECLARED] )*
      IN_TOK c=command
      { $cmd = c;
        PARSER_STATE->popScope();
      }
    )
    { if($cmd == NULL) {
        cmd = new EmptyCommand();
      }
    }
  ;

typeOrVarLetDecl[CVC4::parser::DeclarationCheck check]
options { backtrack = true; }
  : letDecl | typeLetDecl[check]
  ;

mainCommand[CVC4::Command*& cmd]
@init {
  Expr f;
  SExpr sexpr;
  std::string id;
  Type t;
  std::vector<CVC4::Datatype> dts;
  Debug("parser-extra") << "command: " << AntlrInput::tokenText(LT(1)) << std::endl;
  std::string s;
}
    /* our bread & butter */
  : ASSERT_TOK formula[f] { cmd = new AssertCommand(f); }

  | QUERY_TOK formula[f] { cmd = new QueryCommand(f); }
  | CHECKSAT_TOK formula[f] { cmd = new CheckSatCommand(f); }
  | CHECKSAT_TOK { cmd = new CheckSatCommand(MK_CONST(true)); }

    /* options */
  | OPTION_TOK
    ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
    symbolicExpr[sexpr]
    { cmd = new SetOptionCommand(s, sexpr); }

    /* push / pop */
  | PUSH_TOK k=numeral?
    { cmd = REPEAT_COMMAND(k, PushCommand()); }
  | POP_TOK k=numeral?
    { cmd = REPEAT_COMMAND(k, PopCommand()); }
  | POPTO_TOK k=numeral?
    { UNSUPPORTED("POPTO command"); }

    /* push / pop scopes */
  | PUSH_SCOPE_TOK k=numeral?
    { UNSUPPORTED("PUSH_SCOPE command"); }
  | POP_SCOPE_TOK k=numeral?
    { UNSUPPORTED("POP_SCOPE command"); }
  | POPTO_SCOPE_TOK k=numeral?
    { UNSUPPORTED("POPTO_SCOPE command"); }

  | RESET_TOK
    { UNSUPPORTED("RESET command"); }

    // Datatypes can be mututally-recursive if they're in the same
    // definition block, separated by a comma.  So we parse everything
    // and then ask the ExprManager to resolve everything in one go.
  | DATATYPE_TOK
    { /* open a scope to keep the UnresolvedTypes contained */
      PARSER_STATE->pushScope(); }
    datatypeDef[dts]
    ( COMMA datatypeDef[dts] )*
    END_TOK
    { PARSER_STATE->popScope();
      cmd = new DatatypeDeclarationCommand(PARSER_STATE->mkMutualDatatypeTypes(dts)); }

  | CONTEXT_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { UNSUPPORTED("CONTEXT command"); }
    | { UNSUPPORTED("CONTEXT command"); }
    )

  | FORGET_TOK identifier[id,CHECK_NONE,SYM_VARIABLE]
    { UNSUPPORTED("FORGET command"); }

  | GET_TYPE_TOK formula[f]
    { UNSUPPORTED("GET_TYPE command"); }

  | CHECK_TYPE_TOK formula[f] COLON type[t,CHECK_DECLARED]
    { UNSUPPORTED("CHECK_TYPE command"); }

  | GET_CHILD_TOK formula[f] k=numeral
    { UNSUPPORTED("GET_CHILD command"); }

  | GET_OP_TOK formula[f]
    { UNSUPPORTED("GET_OP command"); }

  | SUBSTITUTE_TOK identifier[id,CHECK_NONE,SYM_VARIABLE] COLON type[t,CHECK_DECLARED] EQUAL_TOK
    formula[f] LBRACKET identifier[id,CHECK_NONE,SYM_VARIABLE] ASSIGN_TOK formula[f] RBRACKET
    { UNSUPPORTED("SUBSTITUTE command"); }

    /* Like the --debug command line option, DBG turns on both tracing
     * and debugging. */
  | DBG_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Debug.on(s); Trace.on(s); }
    | { Message() << "Please specify what to debug." << std::endl; }
    )

  | TRACE_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Trace.on(s); }
    | { Message() << "Please specify something to trace." << std::endl; }
    )
  | UNTRACE_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Trace.off(s); }
    | { Message() << "Please specify something to untrace." << std::endl; }
    )

  | HELP_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Message() << "No help available for `" << s << "'." << std::endl; }
    | { Message() << "Please use --help at the command line for help." << std::endl; }
    )

  | TRANSFORM_TOK formula[f]
    { cmd = new SimplifyCommand(f); }

  | PRINT_TOK formula[f]
    { UNSUPPORTED("PRINT command"); }
  | PRINT_TYPE_TOK type[t,CHECK_DECLARED]
    { UNSUPPORTED("PRINT_TYPE command"); }

  | CALL_TOK identifier[id,CHECK_NONE,SYM_VARIABLE] formula[f]
    { UNSUPPORTED("CALL command"); }

  | ECHO_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Message() << s << std::endl; }
    | { Message() << std::endl; }
    )

  | EXIT_TOK
    { cmd = new QuitCommand(); }

  | INCLUDE_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { UNSUPPORTED("INCLUDE command"); }
    | { PARSER_STATE->parseError("No filename given to INCLUDE command"); }
    )

  | ( DUMP_PROOF_TOK
    | DUMP_ASSUMPTIONS_TOK
    | DUMP_SIG_TOK
    | DUMP_TCC_TOK
    | DUMP_TCC_ASSUMPTIONS_TOK
    | DUMP_TCC_PROOF_TOK
    | DUMP_CLOSURE_TOK
    | DUMP_CLOSURE_PROOF_TOK
    ) { UNSUPPORTED("DUMP* command"); }

    /* these are all synonyms */
  | ( WHERE_TOK | ASSERTIONS_TOK | ASSUMPTIONS_TOK )
    { cmd = new GetAssertionsCommand(); }

  | COUNTEREXAMPLE_TOK
    { UNSUPPORTED("COUNTEREXAMPLE command"); }
  | COUNTERMODEL_TOK
    { UNSUPPORTED("COUNTERMODEL command"); }

  | ARITH_VAR_ORDER_TOK LPAREN formula[f] ( COMMA formula[f] )* RPAREN
    { UNSUPPORTED("ARITH_VAR_ORDER command"); }

  | toplevelDeclaration[cmd]
  ;

symbolicExpr[CVC4::SExpr& sexpr]
@declarations {
  std::vector<SExpr> children;
  std::string s;
}
  : INTEGER_LITERAL ('.' DIGIT+)?
    { sexpr = SExpr((const char*)$symbolicExpr.text->chars); }
  | str[s]
    { sexpr = SExpr(s); }
  | IDENTIFIER
    { sexpr = SExpr(AntlrInput::tokenText($IDENTIFIER)); }
  | LPAREN (symbolicExpr[sexpr] { children.push_back(sexpr); } )* RPAREN
    { sexpr = SExpr(children); }
  ;

/**
 * Match a top-level declaration.
 */
toplevelDeclaration[CVC4::Command*& cmd]
@init {
  std::vector<std::string> ids;
  Type t;
  Debug("parser-extra") << "declaration: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : identifierList[ids,CHECK_NONE,SYM_VARIABLE] COLON
    ( declareVariables[cmd,t,ids,true]
    | declareTypes[cmd,ids] )
  ;

/**
 * A bound variable declaration.
 */
boundVarDecl[std::vector<std::string>& ids, CVC4::Type& t]
  : identifierList[ids,CHECK_NONE,SYM_VARIABLE] COLON declareVariables[*(Command**)NULL,t,ids,false]
  ;

/**
 * A series of bound variable declarations.
 */
boundVarDecls
@init {
  std::vector<std::string> ids;
  Type t;
}
  : boundVarDecl[ids,t] ( COMMA boundVarDecl[ids,t] )*
  ;

boundVarDeclsReturn[std::vector<CVC4::Expr>& terms,
                    std::vector<CVC4::Type>& types]
@init {
  std::vector<std::string> ids;
  Type t;
  terms.clear();
  types.clear();
}
  : boundVarDeclReturn[terms,types] ( COMMA boundVarDeclReturn[terms,types] )*
  ;

boundVarDeclReturn[std::vector<CVC4::Expr>& terms,
                   std::vector<CVC4::Type>& types]
@init {
  std::vector<std::string> ids;
  Type t;
  // NOTE: do not clear the vectors here!
}
  : identifierList[ids,CHECK_NONE,SYM_VARIABLE] COLON type[t,CHECK_DECLARED]
    { const std::vector<Expr>& vars = PARSER_STATE->mkVars(ids, t);
      terms.insert(terms.end(), vars.begin(), vars.end());
      for(unsigned i = 0; i < vars.size(); ++i) {
        types.push_back(t);
      }
    }
  ;

/**
 * Match the right-hand-side of a type declaration.  Unlike
 * declareVariables[] below, don't need to return the Type, since it's
 * always the KindType (the type of types).  Also don't need toplevel
 * because type declarations are always top-level, except for
 * type-lets, which don't use this rule.
 */
declareTypes[CVC4::Command*& cmd, const std::vector<std::string>& idList]
@init {
  Type t;
}
    /* A sort declaration (e.g., "T : TYPE") */
  : TYPE_TOK
    { DeclarationSequence* seq = new DeclarationSequence();
      for(std::vector<std::string>::const_iterator i = idList.begin();
          i != idList.end();
          ++i) {
        // Don't allow a type variable to clash with a previously
        // declared type variable, however a type variable and a
        // non-type variable can clash unambiguously.  Break from CVC3
        // behavior here.
        PARSER_STATE->checkDeclaration(*i, CHECK_UNDECLARED, SYM_SORT);
        Type sort = PARSER_STATE->mkSort(*i);
        Command* decl = new DeclareTypeCommand(*i, 0, sort);
        seq->addCommand(decl);
      }
      cmd = seq;
    }

    /* A type alias "T : TYPE = foo..." */
  | TYPE_TOK EQUAL_TOK type[t,CHECK_DECLARED]
    { for(std::vector<std::string>::const_iterator i = idList.begin();
          i != idList.end();
          ++i) {
        PARSER_STATE->checkDeclaration(*i, CHECK_UNDECLARED, SYM_SORT);
        PARSER_STATE->defineType(*i, t);
      }
    }
  ;

/**
 * Match the right-hand side of a variable declaration.  Returns the
 * type.  Some IDs might have been declared previously, and are not
 * re-declared if topLevel is true (CVC allows re-declaration if the
 * types are compatible---if they aren't compatible, an error is
 * thrown).  Also if topLevel is true, variable definitions are
 * permitted and "cmd" is output.
 */
declareVariables[CVC4::Command*& cmd, CVC4::Type& t, const std::vector<std::string>& idList, bool topLevel]
@init {
  Expr f;
  Debug("parser-extra") << "declType: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
    /* A variable declaration (or definition) */
  : type[t,CHECK_DECLARED] ( EQUAL_TOK formula[f] )?
    { DeclarationSequence* seq = NULL;
      if(topLevel) {
        cmd = seq = new DeclarationSequence();
      }
      if(f.isNull()) {
        Debug("parser") << "working on " << idList.front() << " : " << t << std::endl;
        // CVC language allows redeclaration of variables if types are the same
        for(std::vector<std::string>::const_iterator i = idList.begin(),
              i_end = idList.end();
            i != i_end;
            ++i) {
          if(PARSER_STATE->isDeclared(*i, SYM_VARIABLE)) {
            Type oldType = PARSER_STATE->getType(*i);
            Debug("parser") << "  " << *i << " was declared previously "
                            << "with type " << oldType << std::endl;
            if(oldType != t) {
              std::stringstream ss;
              ss << Expr::setlanguage(language::output::LANG_CVC4)
                 << "incompatible type for `" << *i << "':" << std::endl
                 << "  old type: " << oldType << std::endl
                 << "  new type: " << t << std::endl;
              PARSER_STATE->parseError(ss.str());
            } else {
              Debug("parser") << "  types " << t << " and " << oldType
                              << " are compatible" << std::endl;
            }
          } else {
            Debug("parser") << "  " << *i << " not declared" << std::endl;
            PARSER_STATE->mkVar(*i, t);
            if(topLevel) {
              Command* decl = new DeclareFunctionCommand(*i, t);
              seq->addCommand(decl);
            }
          }
        }
      } else {
        if(!topLevel) {
          // must be top-level; doesn't make sense to write something
          // like e.g. FORALL(x:INT = 4): [...]
          PARSER_STATE->parseError("cannot construct a definition here; maybe you want a LET");
        }
        Debug("parser") << "made " << idList.front() << " = " << f << std::endl;
        for(std::vector<std::string>::const_iterator i = idList.begin(),
              i_end = idList.end();
            i != i_end;
            ++i) {
          PARSER_STATE->checkDeclaration(*i, CHECK_UNDECLARED, SYM_VARIABLE);
          PARSER_STATE->defineFunction(*i, f);
          Command* decl = new DefineFunctionCommand(*i, Expr(), f);
          seq->addCommand(decl);
        }
      }
    }
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
  std::string id;
  idList.clear();
}
  : identifier[id,check,type] { idList.push_back(id); }
    ( COMMA identifier[id,check,type] { idList.push_back(id); } )*
  ;

/**
 * Matches an identifier and returns a string.
 */
identifier[std::string& id,
           CVC4::parser::DeclarationCheck check,
           CVC4::parser::SymbolType type]
  : IDENTIFIER
    { id = AntlrInput::tokenText($IDENTIFIER);
      PARSER_STATE->checkDeclaration(id, check, type); }
  ;

/**
 * Match the type in a declaration and do the declaration binding.  If
 * "check" is CHECK_NONE, then identifiers occurring in the type need
 * not exist!  They are created as "unresolved" types and linked up in
 * a type-substitution pass.  Right now, only datatype definitions are
 * supported in this way (since type names can occur without any
 * forward-declaration in CVC language datatype definitions, we have
 * to create types for them on-the-fly).  Before passing CHECK_NONE
 * you really should have a clear idea of WHY you need to parse that
 * way; then you should trace through Parser::mkMutualDatatypeType()
 * to figure out just what you're in for.
 */
type[CVC4::Type& t,
     CVC4::parser::DeclarationCheck check]
@init {
  Type t2;
  bool lhs;
  std::vector<Type> args;
}
    /* a type, possibly a function */
  : restrictedTypePossiblyFunctionLHS[t,check,lhs]
    { if(lhs) {
        Assert(t.isTuple());
        args = TupleType(t).getTypes();
      } else {
        args.push_back(t);
      }
    }
    ( ARROW_TOK type[t2,check] { args.push_back(t2); } )?
    { if(t2.isNull()) {
        if(lhs) {
          PARSER_STATE->parseError("improperly-placed type list; expected `->' after to define a function; or else maybe these parentheses were meant to be square brackets, to define a tuple type?");
        }
      } else {
        t = EXPR_MANAGER->mkFunctionType(args);
      }
    }

    /* type-lets: typeLetDecl defines the types, we just manage the
     * scopes here.  NOTE that LET in the CVC language is always
     * sequential! */
  | LET_TOK { PARSER_STATE->pushScope(); }
    typeLetDecl[check] ( COMMA typeLetDecl[check] )* IN_TOK type[t,check]
    { PARSER_STATE->popScope(); }
  ;

// A restrictedType is one that is not a "bare" function type (it can
// be enclosed in parentheses) and is not a type list.  To support the
// syntax
//
//   f : (nat, nat) -> nat;
//
// we have to permit restrictedTypes to be type lists (as on the LHS
// there).  The "type" rule above uses restictedTypePossiblyFunctionLHS
// directly in order to implement that; this rule allows a type list to
// parse but then issues an error.
restrictedType[CVC4::Type& t,
               CVC4::parser::DeclarationCheck check]
@init {
  bool lhs;
}
  : restrictedTypePossiblyFunctionLHS[t,check,lhs]
    { if(lhs) { PARSER_STATE->parseError("improperly-placed type list; maybe these parentheses were meant to be square brackets, to define a tuple type?"); } }
  ;

/**
 * lhs is set to "true" on output if we have a list of types, so an
 * ARROW must follow.  An ARROW can always follow; lhs means it MUST.
 */
restrictedTypePossiblyFunctionLHS[CVC4::Type& t,
                                  CVC4::parser::DeclarationCheck check,
                                  bool& lhs]
@init {
  Type t2;
  Expr f;
  std::string id;
  std::vector<Type> types;
  lhs = false;
}
    /* named types */
  : identifier[id,check,SYM_SORT]
    parameterization[check,types]?
    {
      if(check == CHECK_DECLARED ||
         PARSER_STATE->isDeclared(id, SYM_SORT)) {
        Debug("parser-param") << "param: getSort " << id << " " << types.size() << " " << PARSER_STATE->getArity( id )
                              << " " << PARSER_STATE->isDeclared(id, SYM_SORT) << std::endl;
        if( types.size()>0 ){
          t = PARSER_STATE->getSort(id, types);
        }else{
          t = PARSER_STATE->getSort(id);
        }
      } else {
        if( types.empty() ){
          t = PARSER_STATE->mkUnresolvedType(id);
          Debug("parser-param") << "param: make unres type " << id << std::endl;
        }else{
          t = PARSER_STATE->mkUnresolvedTypeConstructor(id,types);
          t = SortConstructorType(t).instantiate( types );
          Debug("parser-param") << "param: make unres param type " << id << " " << types.size() << " "
                                << PARSER_STATE->getArity( id ) << std::endl;
        }
      }
    }

    /* array types */
  | ARRAY_TOK restrictedType[t,check] OF_TOK restrictedType[t2,check]
    { t = EXPR_MANAGER->mkArrayType(t, t2); }

    /* subtypes */
  | SUBTYPE_TOK LPAREN formula[f] ( COMMA formula[f] )? RPAREN
    { UNSUPPORTED("subtypes not supported yet");
      t = Type(); }

    /* subrange types */
  | LBRACKET k1=bound DOTDOT k2=bound RBRACKET
    { std::stringstream ss;
      ss << "subranges not supported yet: [" << k1 << ":" << k2 << ']';
      UNSUPPORTED(ss.str());
      if(k1.hasBound() && k2.hasBound() &&
         k1.getBound() > k2.getBound()) {
        ss.str("");
        ss << "Subrange [" << k1.getBound() << ".." << k2.getBound()
           << "] inappropriate: range must be nonempty!";
        PARSER_STATE->parseError(ss.str());
      }
      Debug("subranges") << ss.str() << std::endl;
      t = Type(); }

    /* tuple types / old-style function types */
  | LBRACKET type[t,check] { types.push_back(t); }
    ( COMMA type[t,check] { types.push_back(t); } )* RBRACKET
    { if(types.size() == 1) {
        if(types.front().isFunction()) {
          // old style function syntax [ T -> U ]
          PARSER_STATE->parseError("old-style function type syntax not supported anymore; please use the new syntax");
        } else {
          PARSER_STATE->parseError("I'm not sure what you're trying to do here; tuples must have > 1 type");
        }
      } else {
        // tuple type [ T, U, V... ]
        t = EXPR_MANAGER->mkTupleType(types);
      }
    }

    /* record types */
  | SQHASH identifier[id,CHECK_NONE,SYM_SORT] COLON type[t,check]
    ( COMMA identifier[id,CHECK_NONE,SYM_SORT] COLON type[t,check] )* HASHSQ
    { UNSUPPORTED("records not supported yet");
      t = Type(); }

    /* bitvector types */
  | BITVECTOR_TOK LPAREN k=numeral RPAREN
    { t = EXPR_MANAGER->mkBitVectorType(k); }

    /* basic types */
  | BOOLEAN_TOK { t = EXPR_MANAGER->booleanType(); }
  | REAL_TOK { t = EXPR_MANAGER->realType(); }
  | INT_TOK { t = EXPR_MANAGER->integerType(); }

    /* Parenthesized general type, or the lhs of an ARROW (a list of
     * types).  These two things are combined to avoid conflicts in
     * parsing. */
  | LPAREN type[t,check] { types.push_back(t); }
    ( COMMA type[t,check] { lhs = true; types.push_back(t); } )* RPAREN
    { if(lhs) { t = EXPR_MANAGER->mkTupleType(types); }
      // if !lhs, t is already set up correctly, nothing to do..
    }
  ;

parameterization[CVC4::parser::DeclarationCheck check,
                 std::vector<CVC4::Type>& params]
@init {
  Type t;
}
  : LBRACKET restrictedType[t,check] { Debug("parser-param") << "t = " << t << std::endl; params.push_back( t ); }
    ( COMMA restrictedType[t,check] { Debug("parser-param") << "t = " << t << std::endl; params.push_back( t ); } )* RBRACKET
  ;

bound returns [CVC4::parser::cvc::mySubrangeBound bound]
  : UNDERSCORE { $bound = SubrangeBound(); }
  | k=integer { $bound = SubrangeBound(k); }
;

typeLetDecl[CVC4::parser::DeclarationCheck check]
@init {
  Type t;
  std::string id;
}
  : identifier[id,CHECK_NONE,SYM_SORT] (COLON TYPE_TOK)? EQUAL_TOK restrictedType[t,check]
    { PARSER_STATE->defineType(id, t); }
  ;

/**
 * Matches a CVC4 expression.  Formulas and terms are not really
 * distinguished during parsing; please ignore the naming of the
 * grammar rules.
 *
 * @return the expression representing the formula/term
 */
formula[CVC4::Expr& f]
@init {
  Debug("parser-extra") << "formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
  Expr f2;
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : n=nots
    ( prefixFormula[f]
      { f = addNots(EXPR_MANAGER, n, f); }
    | comparison[f]
      { f = addNots(EXPR_MANAGER, n, f);
        expressions.push_back(f);
      }
      i=morecomparisons[expressions,operators]?
      { f = createPrecedenceTree(EXPR_MANAGER, expressions, operators); }
    )
  ;

morecomparisons[std::vector<CVC4::Expr>& expressions,
                std::vector<unsigned>& operators] returns [size_t i = 0]
@init {
  unsigned op;
  Expr f;
  $i = expressions.size();
}
  : booleanBinop[op] { operators.push_back(op); }
    n=nots
    ( prefixFormula[f]
      { expressions.push_back(addNots(EXPR_MANAGER, n, f)); }
    | comparison[f]
      { f = addNots(EXPR_MANAGER, n, f);
        expressions.push_back(f);
      }
      inner=morecomparisons[expressions,operators]?
    )
  ;

/** Matches 0 or more NOTs. */
nots returns [size_t n = 0]
  : ( NOT_TOK { ++$n; } )*
  ;

prefixFormula[CVC4::Expr& f]
@init {
  std::vector<std::string> ids;
  std::vector<Expr> terms;
  std::vector<Type> types;
  Type t;
}
    /* quantifiers */
  : FORALL_TOK { PARSER_STATE->pushScope(); } LPAREN
    boundVarDecl[ids,t] (COMMA boundVarDecl[ids,t])* RPAREN
    COLON instantiationPatterns? formula[f]
    { PARSER_STATE->popScope();
      UNSUPPORTED("quantifiers not supported yet");
      f = EXPR_MANAGER->mkVar(EXPR_MANAGER->booleanType());
    }
  | EXISTS_TOK { PARSER_STATE->pushScope(); } LPAREN
    boundVarDecl[ids,t] (COMMA boundVarDecl[ids,t])* RPAREN
    COLON instantiationPatterns? formula[f]
    { PARSER_STATE->popScope();
      UNSUPPORTED("quantifiers not supported yet");
      f = EXPR_MANAGER->mkVar(EXPR_MANAGER->booleanType());
    }

   /* lets: letDecl defines the variables and functionss, we just
     * manage the scopes here.  NOTE that LET in the CVC language is
     * always sequential! */
  | LET_TOK { PARSER_STATE->pushScope(); }
    letDecl ( COMMA letDecl )*
    IN_TOK formula[f] { PARSER_STATE->popScope(); }

   /* lambda */
  | LAMBDA { PARSER_STATE->pushScope(); } LPAREN
    boundVarDeclsReturn[terms,types]
    RPAREN COLON formula[f]
    { PARSER_STATE->popScope();
      Type t = EXPR_MANAGER->mkFunctionType(types, f.getType());
      std::string name = "lambda";
      Expr func = PARSER_STATE->mkAnonymousFunction(name, t);
      Command* cmd = new DefineFunctionCommand(name, func, terms, f);
      PARSER_STATE->preemptCommand(cmd);
      f = func;
    }

    /* array literals */
  | ARRAY_TOK { PARSER_STATE->pushScope(); } LPAREN
    boundVarDecl[ids,t] RPAREN COLON formula[f]
    { PARSER_STATE->popScope();
      UNSUPPORTED("array literals not supported yet");
      f = EXPR_MANAGER->mkVar(EXPR_MANAGER->mkArrayType(t, f.getType()));
    }
  ;

instantiationPatterns
@init {
  Expr f;
}
  : ( PATTERN_TOK LPAREN formula[f] (COMMA formula[f])* RPAREN COLON )+
  ;

/**
 * Matches (and defines) a single LET declaration.
 */
letDecl
@init {
  Expr e;
  std::string name;
}
  : identifier[name,CHECK_NONE,SYM_VARIABLE] EQUAL_TOK formula[e]
    { Debug("parser") << Expr::setlanguage(language::output::LANG_CVC4) << e.getType() << std::endl;
      PARSER_STATE->defineVar(name, e);
      Debug("parser") << "LET[" << PARSER_STATE->getDeclarationLevel() << "]: "
                      << name << std::endl
                      << " ==>" << " " << e << std::endl;
    }
  ;

booleanBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : IFF_TOK
  | IMPLIES_TOK
  | OR_TOK
  | XOR_TOK
  | AND_TOK
  ;

comparison[CVC4::Expr& f]
@init {
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : term[f] { expressions.push_back(f); }
    ( comparisonBinop[op] term[f]
      { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(EXPR_MANAGER, expressions, operators); }
  ;

comparisonBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : EQUAL_TOK
  | DISEQUAL_TOK
  | GT_TOK
  | GEQ_TOK
  | LT_TOK
  | LEQ_TOK
  ;

term[CVC4::Expr& f]
@init {
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
  Type t;
}
  : storeTerm[f] { expressions.push_back(f); }
    ( arithmeticBinop[op] storeTerm[f] { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(EXPR_MANAGER, expressions, operators); }
  ;

arithmeticBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : PLUS_TOK
  | MINUS_TOK
  | STAR_TOK
  | INTDIV_TOK
  | DIV_TOK
  | EXP_TOK
  ;

/** Parses an array assignment term. */
storeTerm[CVC4::Expr& f]
  : uminusTerm[f]
    ( WITH_TOK arrayStore[f] ( COMMA arrayStore[f] )* )*
  ;

/**
 * Parses just part of the array assignment (and constructs
 * the store terms).
 */
arrayStore[CVC4::Expr& f]
@init {
  Expr f2, f3;
  std::vector<Expr> dims;
}
  : ( LBRACKET formula[f2] { dims.push_back(f2); } RBRACKET )+
    ASSIGN_TOK uminusTerm[f3]
    { Assert(dims.size() >= 1);
      // these loops are a bit complicated; they're only used for the
      // multidimensional ...WITH [a][b] :=... syntax
      for(unsigned i = 0; i < dims.size() - 1; ++i) {
        f = MK_EXPR(CVC4::kind::SELECT, f, dims[i]);
      }
      // a[i][j][k] := v  turns into
      // store(a, i, store(a[i], j, store(a[i][j], k, v)))
      for(unsigned i = dims.size() - 1; i > 0; --i) {
        f3 = MK_EXPR(CVC4::kind::STORE, f, dims[i], f3);
        // strip off one layer of the select
        f = f[0];
      }

      // outermost wrapping
      f = MK_EXPR(CVC4::kind::STORE, f, dims[0], f3);
    }
  ;

/** Parses a unary minus term. */
uminusTerm[CVC4::Expr& f]
@init {
  unsigned minusCount = 0;
}
    /* Unary minus */
  : (MINUS_TOK { ++minusCount; })+ bvBinaryOpTerm[f]
    { while(minusCount > 0) { --minusCount; f = MK_EXPR(CVC4::kind::UMINUS, f); } }
  | bvBinaryOpTerm[f]
  ;

/** Parses bitvectors.  Starts with binary operators @, &, and |. */
bvBinaryOpTerm[CVC4::Expr& f]
@init {
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : bvNegTerm[f] { expressions.push_back(f); }
    ( bvBinop[op] bvNegTerm[f] { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(EXPR_MANAGER, expressions, operators); }
  ;
bvBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : CONCAT_TOK
  | BAR // bitwise OR
  | BVAND_TOK
  ;

bvNegTerm[CVC4::Expr& f]
    /* BV neg */
  : BVNEG_TOK bvNegTerm[f]
    { f = MK_EXPR(CVC4::kind::BITVECTOR_NOT, f); }
  | postfixTerm[f]
  ;

/**
 * Parses an array select / bitvector extract / bitvector shift /
 * function or constructor application.  These are all parsed the same
 * way because they are all effectively post-fix operators and can
 * continue piling onto an expression.  Array selects and bitvector
 * extracts even share similar syntax with their use of [ square
 * brackets ], so we left-factor as much out as possible to make ANTLR
 * happy.
 */
postfixTerm[CVC4::Expr& f]
@init {
  Expr f2;
  bool extract = false, left = false;
  std::vector<Expr> args;
  std::string id;
  Type t;
}
  : bvTerm[f]
    ( /* array select / bitvector extract */
      LBRACKET
        ( formula[f2] { extract = false; }
        | k1=numeral COLON k2=numeral { extract = true; } )
      RBRACKET
      { if(extract) {
          /* bitvector extract */
          f = MK_EXPR(MK_CONST(BitVectorExtract(k1, k2)), f);
        } else {
          /* array select */
          f = MK_EXPR(CVC4::kind::SELECT, f, f2);
        }
      }

      /* left- or right-shift */
    | ( LEFTSHIFT_TOK { left = true; }
      | RIGHTSHIFT_TOK { left = false; } ) k=numeral
      { // Defined in:
        // http://www.cs.nyu.edu/acsys/cvc3/doc/user_doc.html#user_doc_pres_lang_expr_bit
        if(left) {
          f = MK_EXPR(kind::BITVECTOR_CONCAT, f, MK_CONST(BitVector(k)));
        } else {
          unsigned n = BitVectorType(f.getType()).getSize();
          f = MK_EXPR(kind::BITVECTOR_CONCAT, MK_CONST(BitVector(k)),
                      MK_EXPR(MK_CONST(BitVectorExtract(n - 1, k)), f));
        }
      }

      /* function/constructor application */
    | LPAREN { args.push_back(f); }
      formula[f] { args.push_back(f); }
      ( COMMA formula[f] { args.push_back(f); } )* RPAREN
      // TODO: check arity
      { Type t = args.front().getType();
        Debug("parser") << "type is " << t << std::endl;
        Debug("parser") << "expr is " << args.front() << std::endl;
        if(PARSER_STATE->isDefinedFunction(args.front())) {
          f = MK_EXPR(CVC4::kind::APPLY, args);
        } else if(t.isFunction()) {
          f = MK_EXPR(CVC4::kind::APPLY_UF, args);
        } else if(t.isConstructor()) {
          f = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, args);
        } else if(t.isSelector()) {
          f = MK_EXPR(CVC4::kind::APPLY_SELECTOR, args);
        } else if(t.isTester()) {
          f = MK_EXPR(CVC4::kind::APPLY_TESTER, args);
        } else {
          Unhandled(t);
        }
      }

      /* record / tuple select */
    // FIXME - clash in lexer between tuple-select and real; can
    // resolve with syntactic predicate in ANTLR 3.3, but broken in
    // 3.2 ?
    /*| DOT
      ( identifier[id,CHECK_NONE,SYM_VARIABLE]
        { UNSUPPORTED("record select not implemented yet");
          f = Expr(); }
      | k=numeral
        { UNSUPPORTED("tuple select not implemented yet");
          // This will assert-fail if k too big or f not a tuple
          // that's ok for now, once a TUPLE_SELECT operator exists,
          // that will do any necessary type checking
          f = EXPR_MANAGER->mkVar(TupleType(f.getType()).getTypes()[k]); }
      )*/
    )*
    ( typeAscription[f, t]
      { if(f.getKind() == CVC4::kind::APPLY_CONSTRUCTOR && t.isDatatype()) {
          std::vector<CVC4::Expr> v;
          Expr e = f.getOperator();
          const Datatype::Constructor& dtc = Datatype::datatypeOf(e)[Datatype::indexOf(e)];
          v.push_back(MK_EXPR( CVC4::kind::APPLY_TYPE_ASCRIPTION,
                               MK_CONST(AscriptionType(dtc.getSpecializedConstructorType(t))), f.getOperator() ));
          v.insert(v.end(), f.begin(), f.end());
          f = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, v);
        } else {
          if(f.getType() != t) {
            PARSER_STATE->parseError("Type ascription not satisfied.");
          }
        }
      }
    )?
  ;

bvTerm[CVC4::Expr& f]
@init {
  Expr f2;
}
    /* BV xor */
  : BVXOR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_XOR, f, f2); }
  | BVNAND_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_NAND, f, f2); }
  | BVNOR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_NOR, f, f2); }
  | BVCOMP_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_COMP, f, f2); }
  | BVXNOR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_XNOR, f, f2); }

    /* BV unary minus */
  | BVUMINUS_TOK LPAREN formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_NEG, f); }
    /* BV addition */
  | BVPLUS_TOK LPAREN k=numeral COMMA formula[f]
    ( COMMA formula[f2] { f = MK_EXPR(CVC4::kind::BITVECTOR_PLUS, f, f2); } )+ RPAREN
    { unsigned size = BitVectorType(f.getType()).getSize();
      if(k == 0) {
        PARSER_STATE->parseError("BVPLUS(k,_,_,...) must have k > 0");
      }
      if(k > size) {
        f = MK_EXPR(MK_CONST(BitVectorZeroExtend(k)), f);
      } else if(k < size) {
        f = MK_EXPR(MK_CONST(BitVectorExtract(k - 1, 0)), f);
      }
    }
    /* BV subtraction */
  | BVSUB_TOK LPAREN k=numeral COMMA formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SUB, f, f2);
      if(k == 0) {
        PARSER_STATE->parseError("BVSUB(k,_,_) must have k > 0");
      }
      unsigned size = BitVectorType(f.getType()).getSize();
      if(k > size) {
        f = MK_EXPR(MK_CONST(BitVectorZeroExtend(k)), f);
      } else if(k < size) {
        f = MK_EXPR(MK_CONST(BitVectorExtract(k - 1, 0)), f);
      }
    }
    /* BV multiplication */
  | BVMULT_TOK LPAREN k=numeral COMMA formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_MULT, f, f2);
      if(k == 0) {
        PARSER_STATE->parseError("BVMULT(k,_,_) must have k > 0");
      }
      unsigned size = BitVectorType(f.getType()).getSize();
      if(k > size) {
        f = MK_EXPR(MK_CONST(BitVectorZeroExtend(k)), f);
      } else if(k < size) {
        f = MK_EXPR(MK_CONST(BitVectorExtract(k - 1, 0)), f);
      }
    }
    /* BV unsigned division */
  | BVUDIV_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_UDIV, f, f2); }
    /* BV signed division */
  | BVSDIV_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SDIV, f, f2); }
    /* BV unsigned remainder */
  | BVUREM_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_UREM, f, f2); }
    /* BV signed remainder */
  | BVSREM_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SREM, f, f2); }
    /* BV signed modulo */
  | BVSMOD_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SMOD, f, f2); }
    /* BV left shift */
  | BVSHL_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SHL, f, f2); }
    /* BV arithmetic right shift */
  | BVASHR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_ASHR, f, f2); }
    /* BV logical left shift */
  | BVLSHR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_LSHR, f, f2); }
    /* BV sign extension */
  | SX_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { unsigned n = BitVectorType(f.getType()).getSize();
      // Sign extension in TheoryBitVector is defined as in SMT-LIBv2
      // which is different than in the CVC language
      // SX(BITVECTOR(k), n) in CVC language extends to n bits
      // In SMT-LIBv2, such a thing expands to k + n bits
      f = MK_EXPR(MK_CONST(BitVectorSignExtend(k - n)), f); }
    /* BV zero extension */
  | BVZEROEXTEND_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { unsigned n = BitVectorType(f.getType()).getSize();
      // Zero extension in TheoryBitVector is defined as in SMT-LIBv2
      // which is the same as in CVC3, but different than SX!
      // SX(BITVECTOR(k), n) in CVC language extends to n bits
      // BVZEROEXTEND(BITVECTOR(k), n) in CVC language extends to k + n bits
      f = MK_EXPR(MK_CONST(BitVectorZeroExtend(k)), f); }
    /* BV repeat operation */
  | BVREPEAT_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { f = MK_EXPR(MK_CONST(BitVectorRepeat(k)), f); }
    /* BV rotate right */
  | BVROTR_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { f = MK_EXPR(MK_CONST(BitVectorSignExtend(k)), f); }
    /* BV rotate left */
  | BVROTL_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { f = MK_EXPR(MK_CONST(BitVectorRotateLeft(k)), f); }

    /* BV comparisons */
  | BVLT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_ULT, f, f2); }
  | BVLE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_ULE, f, f2); }
  | BVGT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_UGT, f, f2); }
  | BVGE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_UGE, f, f2); }
  | BVSLT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SLT, f, f2); }
  | BVSLE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SLE, f, f2); }
  | BVSGT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SGT, f, f2); }
  | BVSGE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SGE, f, f2); }

  /*
  | IS_INTEGER_TOK LPAREN formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_IS_INTEGER, f); }
  */

  | simpleTerm[f]
  ;

/** Parses a simple term. */
simpleTerm[CVC4::Expr& f]
@init {
  std::string name;
  std::vector<Expr> args;
  Debug("parser-extra") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
  Type t;
}
    /* if-then-else */
  : iteTerm[f]

    /* parenthesized sub-formula / tuple literals */
  | LPAREN formula[f] { args.push_back(f); }
    ( COMMA formula[f] { args.push_back(f); } )* RPAREN
    { if(args.size() > 1) {
        /* If args has elements, we must be a tuple literal.
         * Otherwise, f is already the sub-formula, and
         * there's nothing to do */
        f = EXPR_MANAGER->mkExpr(kind::TUPLE, args);
      }
    }

    /* boolean literals */
  | TRUE_TOK  { f = MK_CONST(true); }
  | FALSE_TOK { f = MK_CONST(false); }
    /* arithmetic literals */
    /* syntactic predicate: never match INTEGER.DIGIT as an integer and a dot!
     * This is a rational constant!  Otherwise the parser interprets it as a tuple
     * selector! */
  | DECIMAL_LITERAL { f = MK_CONST(AntlrInput::tokenToRational($DECIMAL_LITERAL)); }
  | INTEGER_LITERAL { f = MK_CONST(AntlrInput::tokenToInteger($INTEGER_LITERAL)); }
    /* bitvector literals */
  | HEX_LITERAL
    { Assert( AntlrInput::tokenText($HEX_LITERAL).find("0hex") == 0 );
      std::string hexString = AntlrInput::tokenTextSubstr($HEX_LITERAL, 4);
      f = MK_CONST( BitVector(hexString, 16) ); }
  | BINARY_LITERAL
    { Assert( AntlrInput::tokenText($BINARY_LITERAL).find("0bin") == 0 );
      std::string binString = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 4);
      f = MK_CONST( BitVector(binString, 2) ); }
    /* record literals */
  | PARENHASH recordEntry (COMMA recordEntry)+ HASHPAREN
    { UNSUPPORTED("records not implemented yet");
      f = Expr(); }

    /* variable / zero-ary constructor application */
  | identifier[name,CHECK_DECLARED,SYM_VARIABLE]
    /* ascriptions will be required for parameterized zero-ary constructors */
    { f = PARSER_STATE->getVariable(name); }
    { // datatypes: zero-ary constructors
      Type t2 = PARSER_STATE->getType(name);
      if(t2.isConstructor() && ConstructorType(t2).getArity() == 0) {
        // don't require parentheses, immediately turn it into an apply
        f = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, f);
      }
    }
  ;

/**
 * Matches (and performs) a type ascription.
 * The f arg is the term to check (it is an input-only argument).
 */
typeAscription[const CVC4::Expr& f, CVC4::Type& t]
@init {
}
  : COLON COLON type[t,CHECK_DECLARED]
  ;

/**
 * Matches an entry in a record literal.
 */
recordEntry
@init {
  std::string id;
  Expr f;
}
  : identifier[id,CHECK_DECLARED,SYM_VARIABLE] ASSIGN_TOK formula[f]
  ;

/**
 * Parses an ITE term.
 */
iteTerm[CVC4::Expr& f]
@init {
  std::vector<Expr> args;
  Debug("parser-extra") << "ite: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : IF_TOK formula[f] { args.push_back(f); }
    THEN_TOK formula[f] { args.push_back(f); }
    iteElseTerm[f] { args.push_back(f); }
    ENDIF_TOK
    { f = MK_EXPR(CVC4::kind::ITE, args); }
  ;

/**
 * Parses the else part of the ITE, i.e. ELSE f, or ELSIF b THEN f1 ...
 */
iteElseTerm[CVC4::Expr& f]
@init {
  std::vector<Expr> args;
  Debug("parser-extra") << "else: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : ELSE_TOK formula[f]
  | ELSEIF_TOK iteCondition = formula[f] { args.push_back(f); }
    THEN_TOK iteThen = formula[f] { args.push_back(f); }
    iteElse = iteElseTerm[f] { args.push_back(f); }
    { f = MK_EXPR(CVC4::kind::ITE, args); }
  ;

/**
 * Parses a datatype definition
 */
datatypeDef[std::vector<CVC4::Datatype>& datatypes]
@init {
  std::string id, id2;
  Type t;
  std::vector< Type > params;
}
    /* This really needs to be CHECK_NONE, or mutually-recursive
     * datatypes won't work, because this type will already be
     * "defined" as an unresolved type; don't worry, we check
     * below. */
  : identifier[id,CHECK_NONE,SYM_SORT] { PARSER_STATE->pushScope(); }
    ( LBRACKET identifier[id2,CHECK_UNDECLARED,SYM_SORT] {
        t = PARSER_STATE->mkSort(id2);
        params.push_back( t );
      }
      ( COMMA identifier[id2,CHECK_UNDECLARED,SYM_SORT] {
        t = PARSER_STATE->mkSort(id2);
        params.push_back( t ); }
      )* RBRACKET
    )?
    { datatypes.push_back(Datatype(id,params));
      if(!PARSER_STATE->isUnresolvedType(id)) {
        // if not unresolved, must be undeclared
        PARSER_STATE->checkDeclaration(id, CHECK_UNDECLARED, SYM_SORT);
      }
    }
    EQUAL_TOK constructorDef[datatypes.back()]
    ( BAR constructorDef[datatypes.back()] )*
    { PARSER_STATE->popScope(); }
  ;

/**
 * Parses a constructor defintion for type
 */
constructorDef[CVC4::Datatype& type]
@init {
  std::string id;
  CVC4::Datatype::Constructor* ctor = NULL;
}
  : identifier[id,CHECK_UNDECLARED,SYM_SORT]
    { // make the tester
      std::string testerId("is_");
      testerId.append(id);
      PARSER_STATE->checkDeclaration(testerId, CHECK_UNDECLARED, SYM_SORT);
      ctor = new CVC4::Datatype::Constructor(id, testerId);
    }
    ( LPAREN
      selector[*ctor]
      ( COMMA selector[*ctor] )*
      RPAREN
    )?
    { // make the constructor
      type.addConstructor(*ctor);
      Debug("parser-idt") << "constructor: " << id.c_str() << std::endl;
      delete ctor;
    }
  ;

selector[CVC4::Datatype::Constructor& ctor]
@init {
  std::string id;
  Type t, t2;
}
  : identifier[id,CHECK_UNDECLARED,SYM_SORT] COLON type[t,CHECK_NONE]
    { ctor.addArg(id, t);
      Debug("parser-idt") << "selector: " << id.c_str() << std::endl;
    }
  ;

/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER : (ALPHA | '_') (ALPHA | DIGIT | '_' | '\'' | '\\' | '?' | '$' | '~')*;

/**
 * Matches an integer literal.
 */
INTEGER_LITERAL
  : ( '0'
    | '1'..'9' DIGIT*
    )
  ;

/**
 * Matches a decimal literal.
 */
DECIMAL_LITERAL
  : INTEGER_LITERAL '.' DIGIT+
  ;

/**
 * Same as an integer literal converted to an unsigned int, but
 * slightly more convenient AND works around a strange ANTLR bug (?)
 * in the BVPLUS/BVMINUS/BVMULT rules where $INTEGER_LITERAL was
 * returning a reference to the wrong token?!
 */
numeral returns [unsigned k = 0]
  : INTEGER_LITERAL
    { $k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL); }
  ;

/**
 * Similar to numeral but for arbitrary-precision, signed integer.
 */
integer returns [CVC4::Integer k = 0]
  : INTEGER_LITERAL
    { $k = AntlrInput::tokenToInteger($INTEGER_LITERAL); }
  | MINUS_TOK INTEGER_LITERAL
    { $k = -AntlrInput::tokenToInteger($INTEGER_LITERAL); }
  ;

/**
 * Similar to numeral but for strings.
 */
str[std::string& s]
  : STRING_LITERAL
    { s = AntlrInput::tokenText($STRING_LITERAL);
      /* strip off the quotes */
      s = s.substr(1, s.size() - 2);
    }
  ;

/**
 * Matches a hexadecimal constant.
 */
HEX_LITERAL
  : '0hex' HEX_DIGIT+
  ;

/**
 * Matches a binary constant.
 */
BINARY_LITERAL
  : '0bin' ('0' | '1')+
  ;

/**
 * Matches a double quoted string literal. Escaping is supported, and
 * escape character '\' has to be escaped.
 */
STRING_LITERAL: '"' (ESCAPE | ~('"'|'\\'))* '"';

/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment ALPHA : 'a'..'z' | 'A'..'Z';

/**
 * Matches the decimal digits (0-9)
 */
fragment DIGIT : '0'..'9';

/**
 * Matches the hexidecimal digits (0-9, a-f, A-F)
 */
fragment HEX_DIGIT : DIGIT | 'a'..'f' | 'A'..'F';

/**
 * Matches and skips whitespace in the input and ignores it.
 */
WHITESPACE : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP(); };

/**
 * Matches the comments and ignores them
 */
COMMENT : '%' (~('\n' | '\r'))* { SKIP(); };

/**
 * Matches an allowed escaped character.
 */
fragment ESCAPE : '\\' ('"' | '\\' | 'n' | 't' | 'r');

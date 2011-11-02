/*********************                                                        */
/*! \file smt2_input.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include <antlr3.h>

#include "parser/smt2/smt2_input.h"
#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/smt2/smt2.h"
#include "parser/smt2/generated/Smt2Lexer.h"
#include "parser/smt2/generated/Smt2Parser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
Smt2Input::Smt2Input(AntlrInputStream& inputStream) :
  AntlrInput(inputStream, 2) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  AlwaysAssert( input != NULL );

  d_pSmt2Lexer = Smt2LexerNew(input);
  if( d_pSmt2Lexer == NULL ) {
    throw ParserException("Failed to create SMT2 lexer.");
  }

  setAntlr3Lexer( d_pSmt2Lexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  AlwaysAssert( tokenStream != NULL );

  d_pSmt2Parser = Smt2ParserNew(tokenStream);
  if( d_pSmt2Parser == NULL ) {
    throw ParserException("Failed to create SMT2 parser.");
  }

  setAntlr3Parser(d_pSmt2Parser->pParser);
}


Smt2Input::~Smt2Input() {
  d_pSmt2Lexer->free(d_pSmt2Lexer);
  d_pSmt2Parser->free(d_pSmt2Parser);
}

Command* Smt2Input::parseCommand()
  throw (ParserException, TypeCheckingException, AssertionException) {
  return d_pSmt2Parser->parseCommand(d_pSmt2Parser);
}

Expr Smt2Input::parseExpr()
  throw (ParserException, TypeCheckingException, AssertionException) {
  return d_pSmt2Parser->parseExpr(d_pSmt2Parser);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

/*********************                                                        */
/*! \file cvc_input.cpp
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

#include "expr/expr_manager.h"
#include "parser/antlr_input.h"
#include "parser/parser_exception.h"
#include "parser/cvc/cvc_input.h"
#include "parser/cvc/generated/CvcLexer.h"
#include "parser/cvc/generated/CvcParser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=3 */
CvcInput::CvcInput(AntlrInputStream& inputStream) :
  AntlrInput(inputStream,6) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  AlwaysAssert( input != NULL );

  d_pCvcLexer = CvcLexerNew(input);
  if( d_pCvcLexer == NULL ) {
    throw ParserException("Failed to create CVC lexer.");
  }

  setAntlr3Lexer( d_pCvcLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  AlwaysAssert( tokenStream != NULL );

  d_pCvcParser = CvcParserNew(tokenStream);
  if( d_pCvcParser == NULL ) {
    throw ParserException("Failed to create CVC parser.");
  }

  setAntlr3Parser(d_pCvcParser->pParser);
}


CvcInput::~CvcInput() {
  d_pCvcLexer->free(d_pCvcLexer);
  d_pCvcParser->free(d_pCvcParser);
}

Command* CvcInput::parseCommand()
  throw (ParserException, TypeCheckingException, AssertionException) {
  return d_pCvcParser->parseCommand(d_pCvcParser);
}

Expr CvcInput::parseExpr()
  throw (ParserException, TypeCheckingException, AssertionException) {
  return d_pCvcParser->parseExpr(d_pCvcParser);
}

/*
pANTLR3_LEXER CvcInput::getLexer() {
  return d_pCvcLexer->pLexer;
}
*/

}/* CVC4::parser namespace */
}/* CVC4 namespace */

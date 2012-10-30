/*********************                                                        */
/*! \file tptp_input.cpp
 ** \verbatim
 ** Original author: bobot
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include <antlr3.h>

#include "parser/tptp/tptp_input.h"
#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/tptp/tptp.h"
#include "parser/tptp/generated/TptpLexer.h"
#include "parser/tptp/generated/TptpParser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=1 */
TptpInput::TptpInput(AntlrInputStream& inputStream) :
  AntlrInput(inputStream, 1) {
  pANTLR3_INPUT_STREAM input = inputStream.getAntlr3InputStream();
  assert( input != NULL );

  d_pTptpLexer = TptpLexerNew(input);
  if( d_pTptpLexer == NULL ) {
    throw ParserException("Failed to create TPTP lexer.");
  }

  setAntlr3Lexer( d_pTptpLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  assert( tokenStream != NULL );

  d_pTptpParser = TptpParserNew(tokenStream);
  if( d_pTptpParser == NULL ) {
    throw ParserException("Failed to create TPTP parser.");
  }

  setAntlr3Parser(d_pTptpParser->pParser);
}


TptpInput::~TptpInput() {
  d_pTptpLexer->free(d_pTptpLexer);
  d_pTptpParser->free(d_pTptpParser);
}

Command* TptpInput::parseCommand()
  throw (ParserException, TypeCheckingException) {
  return d_pTptpParser->parseCommand(d_pTptpParser);
}

Expr TptpInput::parseExpr()
  throw (ParserException, TypeCheckingException) {
  return d_pTptpParser->parseExpr(d_pTptpParser);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

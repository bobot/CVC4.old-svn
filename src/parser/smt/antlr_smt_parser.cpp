/*
 * antlr_smt_parser.cpp
 *
 *  Created on: Feb 24, 2010
 *      Author: chris
 */

#include "antlr_smt_parser.h"
#include "parser/bounded_token_factory.h"

namespace CVC4 {
namespace parser {


AntlrSmtParser::AntlrSmtParser(ExprManager* em, const std::string& filename) :
    AntlrParser(filename) {
  setExpressionManager(em);
  pANTLR3_UINT8 fName = (pANTLR3_UINT8) filename.c_str();
  d_input = antlr3AsciiFileStreamNew(fName);
  AlwaysAssert( d_input != NULL );
  d_pSmtLexer = SmtLexerNew(d_input);
  AlwaysAssert( d_pSmtLexer != NULL );
  pANTLR3_TOKEN_FACTORY pOrigTokenFactory = d_pSmtLexer->pLexer->rec->state->tokFactory;
  if( pOrigTokenFactory != NULL ) {
    pOrigTokenFactory->close(pOrigTokenFactory);
  }
  pANTLR3_TOKEN_FACTORY pTokenFactory = BoundedTokenFactoryNew(d_input, 16);
  d_pSmtLexer->pLexer->rec->state->tokFactory = pTokenFactory;
  pTWO_PLACE_TOKEN_BUFFER buffer = TwoPlaceTokenBufferSourceNew(ANTLR3_SIZE_HINT, TOKENSOURCE(d_pSmtLexer));
  d_tokenStream = buffer->commonTstream;
//      antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT, TOKENSOURCE(d_pSmtLexer));
  d_pSmtParser = SmtParserNew(d_tokenStream);
  SmtParserSetAntlrParser(this);
}

AntlrSmtParser::~AntlrSmtParser() {
  d_pSmtLexer->free(d_pSmtLexer);
  d_tokenStream->free(d_tokenStream);
  d_pSmtParser->free(d_pSmtParser);
  d_input->close(d_input);
}

Command* AntlrSmtParser::parseCommand() {
  return d_pSmtParser->parseCommand(d_pSmtParser);
}

Expr AntlrSmtParser::parseExpr() {
  return d_pSmtParser->parseExpr(d_pSmtParser);
}

pANTLR3_LEXER AntlrSmtParser::getAntlrLexer() {
  return d_pSmtLexer->pLexer;
}

}
}

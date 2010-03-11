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

#include "util/output.h"
#include "util/Assert.h"
#include "expr/command.h"
#include "expr/type.h"
#include "parser/antlr_parser.h"
#include "parser/bounded_token_factory.h"
#include "parser/memory_mapped_input_buffer.h"
#include "parser/parser_exception.h"
#include "parser/two_place_token_buffer.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

AntlrParser::AntlrParser(ExprManager* exprManager, const std::string& filename, unsigned int lookahead, bool useMmap) :
    Parser(exprManager, filename),
    d_lookahead(lookahead),
    d_lexer(NULL),
    d_parser(NULL),
    d_tokenStream(NULL) {

  if( useMmap ) {
    d_input = MemoryMappedInputBufferNew(filename);
  } else {
    d_input = antlr3AsciiFileStreamNew((pANTLR3_UINT8) filename.c_str());
  }
  if( d_input == NULL ) {
    throw ParserException("Couldn't open file: " + filename);
  }
}

/*
AntlrParser::AntlrParser(ExprManager* exprManager, std::istream& input, const std::string& name, unsigned int lookahead)
  Parser(exprManager,name),
  d_lookahead(lookahead) {

}
*/

AntlrParser::AntlrParser(ExprManager* exprManager, const std::string& input, const std::string& name, unsigned int lookahead) :
  Parser(exprManager,name),
  d_lookahead(lookahead),
  d_lexer(NULL),
  d_parser(NULL),
  d_tokenStream(NULL) {
  char* inputStr = strdup(input.c_str());
  char* nameStr = strdup(name.c_str());
  if( inputStr==NULL || nameStr==NULL ) {
    throw ParserException("Couldn't initialize string input: '" + input + "'");
  }
  d_input = antlr3NewAsciiStringInPlaceStream((pANTLR3_UINT8)inputStr,input.size(),(pANTLR3_UINT8)nameStr);
  if( d_input == NULL ) {
    throw ParserException("Couldn't create input stream for string: '" + input + "'");
  }
}

AntlrParser::~AntlrParser() {
  d_tokenStream->free(d_tokenStream);
  d_input->close(d_input);
}

pANTLR3_INPUT_STREAM AntlrParser::getInputStream() {
  return d_input;
}

pANTLR3_COMMON_TOKEN_STREAM AntlrParser::getTokenStream() {
  return d_tokenStream;
}

void AntlrParser::setLexer(pANTLR3_LEXER pLexer) {
  d_lexer = pLexer;

  pANTLR3_TOKEN_FACTORY pTokenFactory = d_lexer->rec->state->tokFactory;
  if( pTokenFactory != NULL ) {
    pTokenFactory->close(pTokenFactory);
  }

  /* 2*lookahead should be sufficient, but we give ourselves some breathing room. */
  pTokenFactory = BoundedTokenFactoryNew(d_input, 4*d_lookahead);
  if( pTokenFactory == NULL ) {
    throw ParserException("Couldn't create token factory.");
  }
  d_lexer->rec->state->tokFactory = pTokenFactory;

  pTWO_PLACE_TOKEN_BUFFER buffer = TwoPlaceTokenBufferSourceNew(ANTLR3_SIZE_HINT, d_lexer->rec->state->tokSource);
  if( buffer == NULL ) {
    throw ParserException("Couldn't create token buffer.");
  }

  d_tokenStream = buffer->commonTstream;
}

void AntlrParser::setParser(pANTLR3_PARSER pParser) {
  d_parser = pParser;
}

void AntlrParser::parseError(const std::string& message)
    throw (ParserException) {
  throw ParserException(message, getFilename(), d_lexer->getLine(d_lexer),
                          d_lexer->getCharPositionInLine(d_lexer));
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

/*
 * smt_parser.cpp
 *
 *  Created on: Mar 5, 2010
 *      Author: chris
 */

#include <antlr3.h>

#include "expr/expr_manager.h"
#include "parser/parser_exception.h"
#include "parser/smt/smt_parser.h"
#include "parser/smt/generated/SmtLexer.h"
#include "parser/smt/generated/SmtParser.h"

namespace CVC4 {
namespace parser {

/* Use lookahead=2 */
Smt::Smt(ExprManager* exprManager, const std::string& filename, bool useMmap) :
  AntlrParser(exprManager,filename,2,useMmap) {
  init();
}

Smt::Smt(ExprManager* exprManager, const std::string& input, const std::string& name) :
  AntlrParser(exprManager,input,name,2) {
  init();
}

void Smt::init() {
  pANTLR3_INPUT_STREAM input = getInputStream();
  AlwaysAssert( input != NULL );

  d_pSmtLexer = SmtLexerNew(input);
  if( d_pSmtLexer == NULL ) {
    throw ParserException("Failed to create SMT lexer.");
  }

  setLexer( d_pSmtLexer->pLexer );

  pANTLR3_COMMON_TOKEN_STREAM tokenStream = getTokenStream();
  AlwaysAssert( tokenStream != NULL );

  d_pSmtParser = SmtParserNew(tokenStream);
  if( d_pSmtParser == NULL ) {
    throw ParserException("Failed to create SMT parser.");
  }

  setParser(d_pSmtParser->pParser);
  SetSmt(this);
}


Smt::~Smt() {
  d_pSmtLexer->free(d_pSmtLexer);
  d_pSmtParser->free(d_pSmtParser);
}

Command* Smt::doParseCommand() throw (ParserException) {
  return d_pSmtParser->parseCommand(d_pSmtParser);
}

Node Smt::doParseExpr() throw (ParserException) {
  return d_pSmtParser->parseExpr(d_pSmtParser);
}

pANTLR3_LEXER Smt::getLexer() {
  return d_pSmtLexer->pLexer;
}

} // namespace parser

} // namespace CVC4

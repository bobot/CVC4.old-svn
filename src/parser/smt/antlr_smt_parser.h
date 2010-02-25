/*
 * antlr_smt_parser.h
 *
 *  Created on: Feb 24, 2010
 *      Author: chris
 */

#ifndef ANTLR_SMT_PARSER_H_
#define ANTLR_SMT_PARSER_H_

#include <antlr3.h>
#include <string>

#include "parser/antlr_parser.h"
#include "parser/smt/generated/SmtLexer.h"
#include "parser/smt/generated/SmtParser.h"


namespace CVC4 {

class Command;
class Expr;
class ExprManager;

namespace parser {

class AntlrSmtParser : public AntlrParser {
public:
  AntlrSmtParser(ExprManager* em, const std::string& filename);
  ~AntlrSmtParser();

  Command* parseCommand();
  Expr parseExpr();

  pANTLR3_LEXER getAntlrLexer();

private:
  pANTLR3_INPUT_STREAM d_input;
  pSmtLexer d_pSmtLexer;
  pANTLR3_COMMON_TOKEN_STREAM d_tokenStream;
  pSmtParser d_pSmtParser;
}; // class AntlrSmtParser

} // namespace parser

} // namespace CVC4

#endif /* ANTLR_SMT_PARSER_H_ */

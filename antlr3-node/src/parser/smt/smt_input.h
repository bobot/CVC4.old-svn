/*
 * smt_parser.h
 *
 *  Created on: Mar 5, 2010
 *      Author: chris
 */

#ifndef SMT_PARSER_H_
#define SMT_PARSER_H_

#include "expr/node.h"
#include "parser/antlr_parser.h"
#include "parser/smt/generated/SmtLexer.h"
#include "parser/smt/generated/SmtParser.h"

// extern void SmtParserSetAntlrParser(CVC4::parser::AntlrParser* newAntlrParser);

namespace CVC4 {

class Command;
class Expr;
class NodeManager;

namespace parser {

class SmtInput : public AntlrInput {
public:
  SmtInput(ExprManager* exprManager, const std::string& filename, bool useMmap);
  SmtInput(ExprManager* exprManager, const std::string& input, const std::string& name);
  ~SmtInput();

protected:
  Command* doParseCommand() throw(ParserException);
  Node doParseExpr() throw(ParserException);
  pANTLR3_LEXER getLexer();
  pANTLR3_LEXER createLexer(pANTLR3_INPUT_STREAM input);
  pANTLR3_PARSER createParser(pANTLR3_COMMON_TOKEN_STREAM tokenStream);

private:
  void init();
  pSmtLexer d_pSmtLexer;
  pSmtParser d_pSmtParser;
}; // class AntlrSmtParser

} // namespace parser

} // namespace CVC4

#endif /* SMT_PARSER_H_ */

/*********************                                                        */
/** parser.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser implementation.
 **/

#include <iostream>
#include <fstream>
#include <string>
#include <antlr/CharBuffer.hpp>

#include "parser.h"
#include "expr/command.h"
#include "util/output.h"
#include "util/Assert.h"
#include "parser_exception.h"
#include "parser/pegtl_parser.h"
#include "parser/smt/smt_parser.h"

using namespace std;
using namespace antlr;

namespace CVC4 {
namespace parser {

Parser::Parser(PegtlParser* pegtlParser) :
  d_pegtlParser(pegtlParser),
  d_done(false) {
}

void Parser::setDone(bool done) {
  d_done = done;
}

bool Parser::done() const {
  return d_done;
}

Command* Parser::parseNextCommand() throw (ParserException, AssertionException) {
  Debug("parser") << "parseNextCommand()" << std::endl;
  Command* cmd = NULL;
  if(!done()) {
      cmd = d_pegtlParser->parseCommand();
      if(cmd == NULL) {
        setDone();
      }
  }
  Debug("parser") << "parseNextCommand() => " << cmd << std::endl;
  return cmd;
}

Expr Parser::parseNextExpression() throw (ParserException, AssertionException) {
  Debug("parser") << "parseNextExpression()" << std::endl;
  Expr result;
  if(!done()) {
      result = d_pegtlParser->parseExpr();
      if(result.isNull())
        setDone();
  }
  Debug("parser") << "parseNextExpression() => " << result << std::endl;
  return result;
}

Parser::~Parser() {
}

  /*
Parser* Parser::getNewParser(ExprManager* em, InputLanguage lang,
                             Input* input, const std::string& filename) {
  switch(lang) {
  case LANG_CVC4: {
    antlrLexer = new AntlrCvcLexer(*inputBuffer);
    antlrParser = new AntlrCvcParser(*antlrLexer);
    break;
  }
  case LANG_SMTLIB: {
    return new SmtParser(input,filename);
    //pegtl::basic_parse_file< smt::read_annotatedFormula >(filename);
    break;
  }
  default:
    Unhandled("Unknown Input language!");
  }

  antlrLexer->setFilename(filename);
  antlrParser->setFilename(filename);
  antlrParser->setExpressionManager(em);

  return new Parser(inputBuffer, antlrParser, antlrLexer);
}
*/

Parser* Parser::getMemoryMappedParser(ExprManager* em, InputLanguage lang,
                                      const std::string& filename) {
  PegtlParser* parser = new SmtParser(filename);
  //parser->setFilename(filename);
  //parser->setExpressionManager(em);
  return new Parser(parser);
/*
  ascii_file_input input = new ascii_file_input( filename );
  return getNewParser(em,lang,input,filename);
*/
}

Parser* Parser::getNewParser(ExprManager* em, InputLanguage lang,
                             istream& inputStream, const std::string& filename) {
  Unimplemented("getNewParser(istream&)");
/*
  PegtlParser* parser = new SmtParser(filename);
  parser->setFilename(filename);
  parser->setExpressionManager(em);
  return new Parser(parser);
*/

/*
    buffer_input input = new buffer_input( std::istream_iterator< char >( inputStream ), std::istream_iterator< char >() );
  return getNewParser(em, lang, input, filename);
*/
}

void Parser::disableChecks() {
  d_pegtlParser->disableChecks();
}

void Parser::enableChecks() {
  d_pegtlParser->enableChecks();
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

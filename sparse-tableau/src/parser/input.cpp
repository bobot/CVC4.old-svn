/*********************                                                        */
/*! \file input.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters, cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A super-class for input language parsers.
 **
 ** A super-class for input language parsers
 **/

#include "input.h"
#include "parser_exception.h"
#include "parser.h"

#include "expr/command.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "util/output.h"
#include "util/Assert.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

InputStreamException::InputStreamException(const std::string& msg) :
  Exception(msg) {
}

const std::string InputStream::getName() const {
  return d_name;
}

Input::Input(InputStream& inputStream) :
    d_inputStream( &inputStream ) {
}

Input::~Input() {
  delete d_inputStream;
}

InputStream *Input::getInputStream() {
  return d_inputStream;
}

Input* Input::newFileInput(InputLanguage lang,
                           const std::string& filename,
                           bool useMmap)
  throw (InputStreamException, AssertionException) {
  AntlrInputStream *inputStream = 
    AntlrInputStream::newFileInputStream(filename,useMmap);
  return AntlrInput::newInput(lang,*inputStream);
}

Input* Input::newStreamInput(InputLanguage lang, 
                             std::istream& input, 
                             const std::string& name) 
  throw (InputStreamException, AssertionException) {
  AntlrInputStream *inputStream = 
    AntlrInputStream::newStreamInputStream(input,name);
  return AntlrInput::newInput(lang,*inputStream);
}

Input* Input::newStringInput(InputLanguage lang,
                             const std::string& str,
                             const std::string& name)
  throw (InputStreamException, AssertionException) {
  AntlrInputStream *inputStream = AntlrInputStream::newStringInputStream(str,name);
  return AntlrInput::newInput(lang,*inputStream);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

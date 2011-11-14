/*********************                                                        */
/*! \file smt_options_template.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Option handling for SmtEngine
 **
 ** Option handling for SmtEngine.
 **/

#include "smt/smt_engine.h"
#include "smt/bad_option_exception.h"
#include "smt/modal_exception.h"
#include "util/sexpr.h"
#include "expr/command.h"

#include <string>
#include <sstream>

${include_all_option_headers}

#line 31 "${template}"

using namespace std;

namespace CVC4 {

void SmtEngine::setOption(const std::string& key, const CVC4::SExpr& value)
  throw(BadOptionException, ModalException) {
  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SetOptionCommand(key, value) << endl;
  }

  stringstream ss;
  ss << value;
  string optarg = ss.str();

  ${smt_setoption_handlers}

#line 50 "${template}"

  throw BadOptionException();
}

CVC4::SExpr SmtEngine::getOption(const std::string& key) const
  throw(BadOptionException) {
  Trace("smt") << "SMT getOption(" << key << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetOptionCommand(key) << endl;
  }

  ${smt_getoption_handlers}

#line 64 "${template}"

  throw BadOptionException();
}

}/* CVC4 namespace */

/*********************                                                        */
/*! \file printer.cpp
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
 ** \brief Base of the pretty-printer interface
 **
 ** Base of the pretty-printer interface.
 **/

#include "printer/printer.h"

#include "util/language.h"

#include "printer/smt/smt_printer.h"
#include "printer/smt2/smt2_printer.h"
#include "printer/cvc/cvc_printer.h"
#include "printer/ast/ast_printer.h"

#include <string>

using namespace std;

namespace CVC4 {

Printer* Printer::d_printers[language::output::LANG_MAX];

Printer* Printer::makePrinter(OutputLanguage lang) throw() {
  using namespace CVC4::language::output;

  switch(lang) {
  case LANG_SMTLIB:
    return new printer::smt::SmtPrinter();

  case LANG_SMTLIB_V2:
    return new printer::smt2::Smt2Printer();

  case LANG_TPTP: //TODO the printer
    return new printer::smt2::Smt2Printer();

  case LANG_CVC4:
    return new printer::cvc::CvcPrinter();

  case LANG_AST:
    return new printer::ast::AstPrinter();

  default:
    Unhandled(lang);
  }
}/* Printer::makePrinter() */

void Printer::toStream(std::ostream& out, const Result& r) const throw() {
  if(r.getType() == Result::TYPE_SAT) {
    switch(r.isSat()) {
    case Result::UNSAT:
      out << "unsat";
      break;
    case Result::SAT:
      out << "sat";
      break;
    case Result::SAT_UNKNOWN:
      out << "unknown";
      if(r.whyUnknown() != Result::UNKNOWN_REASON) {
        out << " (" << r.whyUnknown() << ")";
      }
      break;
    }
  } else {
    switch(r.isValid()) {
    case Result::INVALID:
      out << "invalid";
      break;
    case Result::VALID:
      out << "valid";
      break;
    case Result::VALIDITY_UNKNOWN:
      out << "unknown";
      if(r.whyUnknown() != Result::UNKNOWN_REASON) {
        out << " (" << r.whyUnknown() << ")";
      }
      break;
    }
  }
}/* Printer::toStream() */

void Printer::toStream(std::ostream& out, const SExpr& sexpr) const throw() {
  if(sexpr.isInteger()) {
    out << sexpr.getIntegerValue();
  } else if(sexpr.isRational()) {
    out << sexpr.getRationalValue();
  } else if(sexpr.isKeyword()) {
    out << sexpr.getValue();
  } else if(sexpr.isString()) {
    string s = sexpr.getValue();
    // escape backslash and quote
    for(size_t i = 0; i < s.length(); ++i) {
      if(s[i] == '"') {
        s.replace(i, 1, "\\\"");
        ++i;
      } else if(s[i] == '\\') {
        s.replace(i, 1, "\\\\");
        ++i;
      }
    }
    out << "\"" << s << "\"";
  } else {
    out << '(';
    const vector<SExpr>& kids = sexpr.getChildren();
    bool first = true;
    for(vector<SExpr>::const_iterator i = kids.begin(); i != kids.end(); ++i) {
      if(first) {
        first = false;
      } else {
        out << ' ';
      }
      out << *i;
    }
    out << ')';
  }
}/* Printer::toStream() */

}/* CVC4 namespace */

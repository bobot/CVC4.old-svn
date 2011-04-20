/*********************                                                        */
/*! \file ouroborous.cpp
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
 ** \brief "Ouroborous" test: does CVC4 read its own output?
 **
 ** The "Ouroborous" test, named after the serpent that swallows its
 ** own tail, ensures that CVC4 can parse some input, output it again
 ** (in any of its languages) and then parse it again.  The result of
 ** the first parse must be equal to the result of the second parse;
 ** both strings and expressions are compared for equality.
 **
 ** To add a new test, simply add a call to runTestString() under
 ** runTest(), below.  If you don't specify an input language,
 ** LANG_SMTLIB_V2 is used.  If your example depends on variables,
 ** you'll need to declare them in the "declarations" global, just
 ** below, in SMT-LIBv2 form (but they're good for all languages).
 **/

#include <iostream>
#include <sstream>
#include <string>

#include "expr/expr.h"
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"

using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::language;
using namespace std;

const string declarations = "\
(declare-sort U 0)\n\
(declare-fun f (U) U)\n\
(declare-fun x () U)\n\
(declare-fun y () U)\n\
(assert (= (f x) x))\n\
(declare-fun a () (Array U (Array U U)))\n\
";

Parser* psr = NULL;

int runTest();

int main() {
  try {
    return runTest();
  } catch(Exception& e) {
    cerr << e << endl;
  } catch(...) {
    cerr << "non-cvc4 exception thrown." << endl;
  }
  return 1;
}

string translate(string in, InputLanguage inlang, OutputLanguage outlang) {
  cout << "==============================================" << endl
       << "translating from " << inlang << " to " << outlang << " this string:" << endl
       << in << endl;
  psr->setInput(Input::newStringInput(inlang, in, "internal-buffer"));
  Expr e = psr->nextExpression();
  stringstream ss;
  ss << Expr::setlanguage(outlang) << Expr::setdepth(-1) << e;
  AlwaysAssert(psr->nextExpression().isNull(), "next expr should be null");
  AlwaysAssert(psr->done(), "parser should be done");
  string s = ss.str();
  cout << "got this:" << endl
       << s << endl
       << "reparsing as " << outlang << endl;

  psr->setInput(Input::newStringInput(toInputLanguage(outlang), s, "internal-buffer"));
  Expr f = psr->nextExpression();
  AlwaysAssert(e == f);
  cout << "got same expressions " << e.getId() << " and " << f.getId() << endl
       << "==============================================" << endl;

  return s;
}

void runTestString(std::string instr, InputLanguage instrlang = input::LANG_SMTLIB_V2) {
  cout << endl
       << "starting with: " << instr << endl
       << "   in language " << instrlang << endl;
  string smt2 = translate(instr, instrlang, output::LANG_SMTLIB_V2);
  cout << "in SMT2      : " << smt2 << endl;
  /* -- SMT-LIBv1 doesn't have a functional printer yet
  string smt1 = translate(smt2, input::LANG_SMTLIB_V2, output::LANG_SMTLIB);
  cout << "in SMT1      : " << smt1 << endl;
  */
  string cvc = translate(smt2, input::LANG_SMTLIB_V2, output::LANG_CVC4);
  cout << "in CVC       : " << cvc << endl;
  string out = translate(cvc, input::LANG_CVC4, output::LANG_SMTLIB_V2);
  cout << "back to SMT2 : " << out << endl << endl;

  AlwaysAssert(out == smt2, "differences in output");
}


int runTest() {
  ExprManager em;
  psr =
    ParserBuilder(&em, "internal-buffer")
      .withStringInput(declarations)
      .withInputLanguage(input::LANG_SMTLIB_V2)
      .build();

  // we don't need to execute them, but we DO need to parse them to
  // get the declarations
  while(Command* c = psr->nextCommand()) {
    delete c;
  }

  AlwaysAssert(psr->done(), "parser should be done");

  cout << Expr::setdepth(-1);

  runTestString("(= (f (f y)) x)");
  runTestString("~BVPLUS(3, 0bin00, 0bin11)[2:1] = 0bin10", input::LANG_CVC4);
  runTestString("a[x][y] = a[y][x]", input::LANG_CVC4);

  delete psr;
  psr = NULL;

  return 0;
}

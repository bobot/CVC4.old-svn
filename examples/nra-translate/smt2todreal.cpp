#include <string>
#include <iostream>
#include <typeinfo>
#include <cassert>
#include <vector>
#include <map>

#include "util/options.h"
#include "expr/expr.h"
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;

int main(int argc, char* argv[]) 
{

  // Get the filename 
  string input(argv[1]);

  // Create the expression manager
  Options options;
  options.inputLanguage = language::input::LANG_SMTLIB_V2;
  options.outputLanguage = language::output::LANG_SMTLIB_V2;
  ExprManager exprManager(options);

  cout << Expr::dag(0) << Expr::setdepth(-1);
  
  // Create the parser
  ParserBuilder parserBuilder(&exprManager, input, options);
  Parser* parser = parserBuilder.build();

  // Smt manager for simplifications
  SmtEngine engine(&exprManager);

  // Variables and assertions
  std::map<Expr, unsigned> variables;
  vector<string> info_tags;
  vector<string> info_data;
  vector<BoolExpr> assertions;

  Command* cmd;
  while ((cmd = parser->nextCommand())) {

    DeclareFunctionCommand* declare = dynamic_cast<DeclareFunctionCommand*>(cmd);
    if (declare) {
      cout << "[-10000, 10000] " << declare->getSymbol() << ";" << endl;
    }
    
    AssertCommand* assert = dynamic_cast<AssertCommand*>(cmd);
    if (assert) {
      cout << assert->getExpr() << ";" << endl;
    }

    delete cmd;  
  }
	
  // Get rid of the parser
  delete parser;
}



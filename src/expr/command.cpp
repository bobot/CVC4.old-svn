/*********************                                                        */
/*! \file command.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of command objects.
 **
 ** Implementation of command objects.
 **/

#include <iostream>
#include <vector>
#include <utility>
#include <iterator>
#include <sstream>
#include <exception>

#include "expr/command.h"
#include "smt/smt_engine.h"
#include "smt/bad_option_exception.h"
#include "util/output.h"
#include "util/dump.h"
#include "util/sexpr.h"
#include "expr/node.h"
#include "printer/printer.h"

using namespace std;

namespace CVC4 {

const int CommandPrintSuccess::s_iosIndex = std::ios_base::xalloc();
const CommandSuccess* CommandSuccess::s_instance = new CommandSuccess();

std::ostream& operator<<(std::ostream& out, const Command& c) throw() {
  c.toStream(out,
             Node::setdepth::getDepth(out),
             Node::printtypes::getPrintTypes(out),
             Node::dag::getDag(out),
             Node::setlanguage::getLanguage(out));
  return out;
}

ostream& operator<<(ostream& out, const Command* c) throw() {
  if(c == NULL) {
    out << "null";
  } else {
    out << *c;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, const CommandStatus& s) throw() {
  s.toStream(out, Node::setlanguage::getLanguage(out));
  return out;
}

ostream& operator<<(ostream& out, const CommandStatus* s) throw() {
  if(s == NULL) {
    out << "null";
  } else {
    out << *s;
  }
  return out;
}

/* class Command */

Command::Command() throw() : d_commandStatus(NULL) {
}

Command::Command(const Command& cmd) {
  d_commandStatus = (cmd.d_commandStatus == NULL) ? NULL : &cmd.d_commandStatus->clone();
}

Command::~Command() throw() {
  if(d_commandStatus != NULL && d_commandStatus != CommandSuccess::instance()) {
    delete d_commandStatus;
  }
}

bool Command::ok() const throw() {
  // either we haven't run the command yet, or it ran successfully
  return d_commandStatus == NULL || dynamic_cast<const CommandSuccess*>(d_commandStatus) != NULL;
}

void Command::invoke(SmtEngine* smtEngine, std::ostream& out) throw() {
  invoke(smtEngine);
  printResult(out);
}

std::string Command::toString() const throw() {
  std::stringstream ss;
  toStream(ss);
  return ss.str();
}

void Command::toStream(std::ostream& out, int toDepth, bool types, size_t dag,
                       OutputLanguage language) const throw() {
  Printer::getPrinter(language)->toStream(out, this, toDepth, types, dag);
}

void CommandStatus::toStream(std::ostream& out, OutputLanguage language) const throw() {
  Printer::getPrinter(language)->toStream(out, this);
}

void Command::printResult(std::ostream& out) const throw() {
  if(d_commandStatus != NULL) {
    out << *d_commandStatus;
  }
}

/* class EmptyCommand */

EmptyCommand::EmptyCommand(std::string name) throw() :
  d_name(name) {
}

std::string EmptyCommand::getName() const throw() {
  return d_name;
}

void EmptyCommand::invoke(SmtEngine* smtEngine) throw() {
  /* empty commands have no implementation */
  d_commandStatus = CommandSuccess::instance();
}

Command* EmptyCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new EmptyCommand(d_name);
}

Command* EmptyCommand::clone() const {
  return new EmptyCommand(d_name);
}

/* class EchoCommand */

EchoCommand::EchoCommand(std::string output) throw() :
  d_output(output) {
}

std::string EchoCommand::getOutput() const throw() {
  return d_output;
}

void EchoCommand::invoke(SmtEngine* smtEngine) throw() {
  /* we don't have an output stream here, nothing to do */
  d_commandStatus = CommandSuccess::instance();
}

void EchoCommand::invoke(SmtEngine* smtEngine, std::ostream& out) throw() {
  out << d_output << std::endl;
  d_commandStatus = CommandSuccess::instance();
  printResult(out);
}

Command* EchoCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new EchoCommand(d_output);
}

Command* EchoCommand::clone() const {
  return new EchoCommand(d_output);
}

/* class AssertCommand */

AssertCommand::AssertCommand(const BoolExpr& e) throw() :
  d_expr(e) {
}

BoolExpr AssertCommand::getExpr() const throw() {
  return d_expr;
}

void AssertCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    smtEngine->assertFormula(d_expr);
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* AssertCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new AssertCommand(d_expr.exportTo(exprManager, variableMap));
}

Command* AssertCommand::clone() const {
  return new AssertCommand(d_expr);
}

/* class PushCommand */

void PushCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    smtEngine->push();
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* PushCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new PushCommand();
}

Command* PushCommand::clone() const {
  return new PushCommand();
}

/* class PopCommand */

void PopCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    smtEngine->pop();
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

/* class CheckSatCommand */

CheckSatCommand::CheckSatCommand() throw() :
  d_expr() {
}

Command* PopCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new PopCommand();
}

Command* PopCommand::clone() const {
  return new PopCommand();
}

/* class CheckSatCommand */

CheckSatCommand::CheckSatCommand(const BoolExpr& expr) throw() :
  d_expr(expr) {
}

BoolExpr CheckSatCommand::getExpr() const throw() {
  return d_expr;
}

void CheckSatCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    d_result = smtEngine->checkSat(d_expr);
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Result CheckSatCommand::getResult() const throw() {
  return d_result;
}

void CheckSatCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else {
    out << d_result << endl;
  }
}

Command* CheckSatCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  CheckSatCommand* c = new CheckSatCommand(d_expr.exportTo(exprManager, variableMap));
  c->d_result = d_result;
  return c;
}

Command* CheckSatCommand::clone() const {
  CheckSatCommand* c = new CheckSatCommand(d_expr);
  c->d_result = d_result;
  return c;
}

/* class QueryCommand */

QueryCommand::QueryCommand(const BoolExpr& e) throw() :
  d_expr(e) {
}

BoolExpr QueryCommand::getExpr() const throw() {
  return d_expr;
}

void QueryCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    d_result = smtEngine->query(d_expr);
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Result QueryCommand::getResult() const throw() {
  return d_result;
}

void QueryCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else {
    out << d_result << endl;
  }
}

Command* QueryCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  QueryCommand* c = new QueryCommand(d_expr.exportTo(exprManager, variableMap));
  c->d_result = d_result;
  return c;
}

Command* QueryCommand::clone() const {
  QueryCommand* c = new QueryCommand(d_expr);
  c->d_result = d_result;
  return c;
}

/* class QuitCommand */

QuitCommand::QuitCommand() throw() {
}

void QuitCommand::invoke(SmtEngine* smtEngine) throw() {
  Dump("benchmark") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* QuitCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new QuitCommand();
}

Command* QuitCommand::clone() const {
  return new QuitCommand();
}

/* class CommentCommand */

CommentCommand::CommentCommand(std::string comment) throw() : d_comment(comment) {
}

std::string CommentCommand::getComment() const throw() {
  return d_comment;
}

void CommentCommand::invoke(SmtEngine* smtEngine) throw() {
  Dump("benchmark") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* CommentCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new CommentCommand(d_comment);
}

Command* CommentCommand::clone() const {
  return new CommentCommand(d_comment);
}

/* class CommandSequence */

CommandSequence::CommandSequence() throw() :
  d_index(0) {
}

CommandSequence::~CommandSequence() throw() {
  for(unsigned i = d_index; i < d_commandSequence.size(); ++i) {
    delete d_commandSequence[i];
  }
}

void CommandSequence::addCommand(Command* cmd) throw() {
  d_commandSequence.push_back(cmd);
}

void CommandSequence::clear() throw() {
  d_commandSequence.clear();
}

void CommandSequence::invoke(SmtEngine* smtEngine) throw() {
  for(; d_index < d_commandSequence.size(); ++d_index) {
    d_commandSequence[d_index]->invoke(smtEngine);
    if(! d_commandSequence[d_index]->ok()) {
      // abort execution
      d_commandStatus = d_commandSequence[d_index]->getCommandStatus();
      return;
    }
    delete d_commandSequence[d_index];
  }

  AlwaysAssert(d_commandStatus == NULL);
  d_commandStatus = CommandSuccess::instance();
}

void CommandSequence::invoke(SmtEngine* smtEngine, std::ostream& out) throw() {
  for(; d_index < d_commandSequence.size(); ++d_index) {
    d_commandSequence[d_index]->invoke(smtEngine, out);
    delete d_commandSequence[d_index];
  }
}

CommandSequence::const_iterator CommandSequence::begin() const throw() {
  return d_commandSequence.begin();
}

Command* CommandSequence::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  CommandSequence* seq = new CommandSequence();
  for(iterator i = begin(); i != end(); ++i) {
    seq->addCommand((*i)->exportTo(exprManager, variableMap));
  }
  seq->d_index = d_index;
  return seq;
}

Command* CommandSequence::clone() const {
  CommandSequence* seq = new CommandSequence();
  for(const_iterator i = begin(); i != end(); ++i) {
    seq->addCommand((*i)->clone());
  }
  seq->d_index = d_index;
  return seq;
}

CommandSequence::const_iterator CommandSequence::end() const throw() {
  return d_commandSequence.end();
}

CommandSequence::iterator CommandSequence::begin() throw() {
  return d_commandSequence.begin();
}

CommandSequence::iterator CommandSequence::end() throw() {
  return d_commandSequence.end();
}

/* class DeclarationSequenceCommand */

/* class DeclarationDefinitionCommand */

DeclarationDefinitionCommand::DeclarationDefinitionCommand(const std::string& id) throw() :
  d_symbol(id) {
}

std::string DeclarationDefinitionCommand::getSymbol() const throw() {
  return d_symbol;
}

/* class DeclareFunctionCommand */

DeclareFunctionCommand::DeclareFunctionCommand(const std::string& id, Type t) throw() :
  DeclarationDefinitionCommand(id),
  d_type(t) {
}

Type DeclareFunctionCommand::getType() const throw() {
  return d_type;
}

void DeclareFunctionCommand::invoke(SmtEngine* smtEngine) throw() {
  Dump("declarations") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* DeclareFunctionCommand::exportTo(ExprManager* exprManager,
                                          ExprManagerMapCollection& variableMap) {
  return new DeclareFunctionCommand(d_symbol,
                                    d_type.exportTo(exprManager, variableMap));
}

Command* DeclareFunctionCommand::clone() const {
  return new DeclareFunctionCommand(d_symbol, d_type);
}

/* class DeclareTypeCommand */

DeclareTypeCommand::DeclareTypeCommand(const std::string& id, size_t arity, Type t) throw() :
  DeclarationDefinitionCommand(id),
  d_arity(arity),
  d_type(t) {
}

size_t DeclareTypeCommand::getArity() const throw() {
  return d_arity;
}

Type DeclareTypeCommand::getType() const throw() {
  return d_type;
}

void DeclareTypeCommand::invoke(SmtEngine* smtEngine) throw() {
  Dump("declarations") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* DeclareTypeCommand::exportTo(ExprManager* exprManager,
                                      ExprManagerMapCollection& variableMap) {
  return new DeclareTypeCommand(d_symbol, d_arity,
                                d_type.exportTo(exprManager, variableMap));
}

Command* DeclareTypeCommand::clone() const {
  return new DeclareTypeCommand(d_symbol, d_arity, d_type);
}

/* class DefineTypeCommand */

DefineTypeCommand::DefineTypeCommand(const std::string& id,
                                     Type t) throw() :
  DeclarationDefinitionCommand(id),
  d_params(),
  d_type(t) {
}

DefineTypeCommand::DefineTypeCommand(const std::string& id,
                                     const std::vector<Type>& params,
                                     Type t) throw() :
  DeclarationDefinitionCommand(id),
  d_params(params),
  d_type(t) {
}

const std::vector<Type>& DefineTypeCommand::getParameters() const throw() {
  return d_params;
}

Type DefineTypeCommand::getType() const throw() {
  return d_type;
}

void DefineTypeCommand::invoke(SmtEngine* smtEngine) throw() {
  Dump("declarations") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* DefineTypeCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  vector<Type> params;
  transform(d_params.begin(), d_params.end(), back_inserter(params),
            ExportTransformer(exprManager, variableMap));
  Type type = d_type.exportTo(exprManager, variableMap);
  return new DefineTypeCommand(d_symbol, params, type);
}

Command* DefineTypeCommand::clone() const {
  return new DefineTypeCommand(d_symbol, d_params, d_type);
}

/* class DefineFunctionCommand */

DefineFunctionCommand::DefineFunctionCommand(const std::string& id,
                                             Expr func,
                                             Expr formula) throw() :
  DeclarationDefinitionCommand(id),
  d_func(func),
  d_formals(),
  d_formula(formula) {
}

DefineFunctionCommand::DefineFunctionCommand(const std::string& id,
                                             Expr func,
                                             const std::vector<Expr>& formals,
                                             Expr formula) throw() :
  DeclarationDefinitionCommand(id),
  d_func(func),
  d_formals(formals),
  d_formula(formula) {
}

Expr DefineFunctionCommand::getFunction() const throw() {
  return d_func;
}

const std::vector<Expr>& DefineFunctionCommand::getFormals() const throw() {
  return d_formals;
}

Expr DefineFunctionCommand::getFormula() const throw() {
  return d_formula;
}

void DefineFunctionCommand::invoke(SmtEngine* smtEngine) throw() {
  //Dump("declarations") << *this; -- done by SmtEngine
  try {
    if(!d_func.isNull()) {
      smtEngine->defineFunction(d_func, d_formals, d_formula);
    }
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* DefineFunctionCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  Expr func = d_func.exportTo(exprManager, variableMap);
  vector<Expr> formals;
  transform(d_formals.begin(), d_formals.end(), back_inserter(formals),
            ExportTransformer(exprManager, variableMap));
  Expr formula = d_formula.exportTo(exprManager, variableMap);
  return new DefineFunctionCommand(d_symbol, func, formals, formula);
}

Command* DefineFunctionCommand::clone() const {
  return new DefineFunctionCommand(d_symbol, d_func, d_formals, d_formula);
}

/* class DefineNamedFunctionCommand */

DefineNamedFunctionCommand::DefineNamedFunctionCommand(const std::string& id,
                                                       Expr func,
                                                       const std::vector<Expr>& formals,
                                                       Expr formula) throw() :
  DefineFunctionCommand(id, func, formals, formula) {
}

void DefineNamedFunctionCommand::invoke(SmtEngine* smtEngine) throw() {
  this->DefineFunctionCommand::invoke(smtEngine);
  if(!d_func.isNull() && d_func.getType().isBoolean()) {
    smtEngine->addToAssignment(d_func.getExprManager()->mkExpr(kind::APPLY, d_func));
  }
  d_commandStatus = CommandSuccess::instance();
}

Command* DefineNamedFunctionCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  Expr func = d_func.exportTo(exprManager, variableMap);
  vector<Expr> formals;
  transform(d_formals.begin(), d_formals.end(), back_inserter(formals),
            ExportTransformer(exprManager, variableMap));
  Expr formula = d_formula.exportTo(exprManager, variableMap);
  return new DefineNamedFunctionCommand(d_symbol, func, formals, formula);
}

Command* DefineNamedFunctionCommand::clone() const {
  return new DefineNamedFunctionCommand(d_symbol, d_func, d_formals, d_formula);
}

/* class Simplify */

SimplifyCommand::SimplifyCommand(Expr term) throw() :
  d_term(term) {
}

Expr SimplifyCommand::getTerm() const throw() {
  return d_term;
}

void SimplifyCommand::invoke(SmtEngine* smtEngine) throw() {
  d_result = smtEngine->simplify(d_term);
  d_commandStatus = CommandSuccess::instance();
}

Expr SimplifyCommand::getResult() const throw() {
  return d_result;
}

void SimplifyCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else {
    out << d_result << endl;
  }
}

Command* SimplifyCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  SimplifyCommand* c = new SimplifyCommand(d_term.exportTo(exprManager, variableMap));
  c->d_result = d_result.exportTo(exprManager, variableMap);
  return c;
}

Command* SimplifyCommand::clone() const {
  SimplifyCommand* c = new SimplifyCommand(d_term);
  c->d_result = d_result;
  return c;
}

/* class GetValueCommand */

GetValueCommand::GetValueCommand(Expr term) throw() :
  d_term(term) {
}

Expr GetValueCommand::getTerm() const throw() {
  return d_term;
}

void GetValueCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    d_result = d_term.getExprManager()->mkExpr(kind::TUPLE, d_term,
                                               smtEngine->getValue(d_term));
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Expr GetValueCommand::getResult() const throw() {
  return d_result;
}

void GetValueCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else {
    out << d_result << endl;
  }
}

Command* GetValueCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  GetValueCommand* c = new GetValueCommand(d_term.exportTo(exprManager, variableMap));
  c->d_result = d_result.exportTo(exprManager, variableMap);
  return c;
}

Command* GetValueCommand::clone() const {
  GetValueCommand* c = new GetValueCommand(d_term);
  c->d_result = d_result;
  return c;
}

/* class GetAssignmentCommand */

GetAssignmentCommand::GetAssignmentCommand() throw() {
}

void GetAssignmentCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    d_result = smtEngine->getAssignment();
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

SExpr GetAssignmentCommand::getResult() const throw() {
  return d_result;
}

void GetAssignmentCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else {
    out << d_result << endl;
  }
}

Command* GetAssignmentCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  GetAssignmentCommand* c = new GetAssignmentCommand();
  c->d_result = d_result;
  return c;
}

Command* GetAssignmentCommand::clone() const {
  GetAssignmentCommand* c = new GetAssignmentCommand();
  c->d_result = d_result;
  return c;
}

/* class GetProofCommand */

GetProofCommand::GetProofCommand() throw() {
}

void GetProofCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    d_result = smtEngine->getProof();
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Proof* GetProofCommand::getResult() const throw() {
  return d_result;
}

void GetProofCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else {
    d_result->toStream(out);
  }
}

Command* GetProofCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  GetProofCommand* c = new GetProofCommand();
  c->d_result = d_result;
  return c;
}

Command* GetProofCommand::clone() const {
  GetProofCommand* c = new GetProofCommand();
  c->d_result = d_result;
  return c;
}

/* class GetAssertionsCommand */

GetAssertionsCommand::GetAssertionsCommand() throw() {
}

void GetAssertionsCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    stringstream ss;
    const vector<Expr> v = smtEngine->getAssertions();
    ss << "(\n";
    copy( v.begin(), v.end(), ostream_iterator<Expr>(ss, "\n") );
    ss << ")\n";
    d_result = ss.str();
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

std::string GetAssertionsCommand::getResult() const throw() {
  return d_result;
}

void GetAssertionsCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else {
    out << d_result;
  }
}

Command* GetAssertionsCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  GetAssertionsCommand* c = new GetAssertionsCommand();
  c->d_result = d_result;
  return c;
}

Command* GetAssertionsCommand::clone() const {
  GetAssertionsCommand* c = new GetAssertionsCommand();
  c->d_result = d_result;
  return c;
}

/* class SetBenchmarkStatusCommand */

SetBenchmarkStatusCommand::SetBenchmarkStatusCommand(BenchmarkStatus status) throw() :
  d_status(status) {
}

BenchmarkStatus SetBenchmarkStatusCommand::getStatus() const throw() {
  return d_status;
}

void SetBenchmarkStatusCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    stringstream ss;
    ss << d_status;
    SExpr status = ss.str();
    smtEngine->setInfo("status", status);
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetBenchmarkStatusCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new SetBenchmarkStatusCommand(d_status);
}

Command* SetBenchmarkStatusCommand::clone() const {
  return new SetBenchmarkStatusCommand(d_status);
}

/* class SetBenchmarkLogicCommand */

SetBenchmarkLogicCommand::SetBenchmarkLogicCommand(std::string logic) throw() :
  d_logic(logic) {
}

std::string SetBenchmarkLogicCommand::getLogic() const throw() {
  return d_logic;
}

void SetBenchmarkLogicCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    smtEngine->setLogic(d_logic);
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetBenchmarkLogicCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new SetBenchmarkLogicCommand(d_logic);
}

Command* SetBenchmarkLogicCommand::clone() const {
  return new SetBenchmarkLogicCommand(d_logic);
}

/* class SetInfoCommand */

SetInfoCommand::SetInfoCommand(std::string flag, const SExpr& sexpr) throw() :
  d_flag(flag),
  d_sexpr(sexpr) {
}

std::string SetInfoCommand::getFlag() const throw() {
  return d_flag;
}

SExpr SetInfoCommand::getSExpr() const throw() {
  return d_sexpr;
}

void SetInfoCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    smtEngine->setInfo(d_flag, d_sexpr);
    d_commandStatus = CommandSuccess::instance();
  } catch(BadOptionException&) {
    d_commandStatus = new CommandUnsupported();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetInfoCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new SetInfoCommand(d_flag, d_sexpr);
}

Command* SetInfoCommand::clone() const {
  return new SetInfoCommand(d_flag, d_sexpr);
}

/* class GetInfoCommand */

GetInfoCommand::GetInfoCommand(std::string flag) throw() :
  d_flag(flag) {
}

std::string GetInfoCommand::getFlag() const throw() {
  return d_flag;
}

void GetInfoCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    vector<SExpr> v;
    v.push_back(SExpr(d_flag));
    v.push_back(smtEngine->getInfo(d_flag));
    stringstream ss;
    ss << SExpr(v);
    d_result = ss.str();
    d_commandStatus = CommandSuccess::instance();
  } catch(BadOptionException&) {
    d_commandStatus = new CommandUnsupported();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

std::string GetInfoCommand::getResult() const throw() {
  return d_result;
}

void GetInfoCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else if(d_result != "") {
    out << d_result << endl;
  }
}

Command* GetInfoCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  GetInfoCommand* c = new GetInfoCommand(d_flag);
  c->d_result = d_result;
  return c;
}

Command* GetInfoCommand::clone() const {
  GetInfoCommand* c = new GetInfoCommand(d_flag);
  c->d_result = d_result;
  return c;
}

/* class SetOptionCommand */

SetOptionCommand::SetOptionCommand(std::string flag, const SExpr& sexpr) throw() :
  d_flag(flag),
  d_sexpr(sexpr) {
}

std::string SetOptionCommand::getFlag() const throw() {
  return d_flag;
}

SExpr SetOptionCommand::getSExpr() const throw() {
  return d_sexpr;
}

void SetOptionCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    smtEngine->setOption(d_flag, d_sexpr);
    d_commandStatus = CommandSuccess::instance();
  } catch(BadOptionException&) {
    d_commandStatus = new CommandUnsupported();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

Command* SetOptionCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  return new SetOptionCommand(d_flag, d_sexpr);
}

Command* SetOptionCommand::clone() const {
  return new SetOptionCommand(d_flag, d_sexpr);
}

/* class GetOptionCommand */

GetOptionCommand::GetOptionCommand(std::string flag) throw() :
  d_flag(flag) {
}

std::string GetOptionCommand::getFlag() const throw() {
  return d_flag;
}

void GetOptionCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    vector<SExpr> v;
    v.push_back(SExpr(d_flag));
    v.push_back(smtEngine->getOption(d_flag));
    stringstream ss;
    ss << SExpr(v);
    d_result = ss.str();
    d_commandStatus = CommandSuccess::instance();
  } catch(BadOptionException&) {
    d_commandStatus = new CommandUnsupported();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
}

std::string GetOptionCommand::getResult() const throw() {
  return d_result;
}

void GetOptionCommand::printResult(std::ostream& out) const throw() {
  if(! ok()) {
    this->Command::printResult(out);
  } else if(d_result != "") {
    out << d_result << endl;
  }
}

Command* GetOptionCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  GetOptionCommand* c = new GetOptionCommand(d_flag);
  c->d_result = d_result;
  return c;
}

Command* GetOptionCommand::clone() const {
  GetOptionCommand* c = new GetOptionCommand(d_flag);
  c->d_result = d_result;
  return c;
}

/* class DatatypeDeclarationCommand */

DatatypeDeclarationCommand::DatatypeDeclarationCommand(const DatatypeType& datatype) throw() :
  d_datatypes() {
  d_datatypes.push_back(datatype);
}

DatatypeDeclarationCommand::DatatypeDeclarationCommand(const std::vector<DatatypeType>& datatypes) throw() :
  d_datatypes(datatypes) {
}

const std::vector<DatatypeType>&
DatatypeDeclarationCommand::getDatatypes() const throw() {
  return d_datatypes;
}

void DatatypeDeclarationCommand::invoke(SmtEngine* smtEngine) throw() {
  Dump("declarations") << *this;
  d_commandStatus = CommandSuccess::instance();
}

Command* DatatypeDeclarationCommand::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap) {
  Warning() << "We currently do not support exportTo with Datatypes" << std::endl;
  return NULL;
}

Command* DatatypeDeclarationCommand::clone() const {
  return new DatatypeDeclarationCommand(d_datatypes);
}

/* output stream insertion operator for benchmark statuses */
std::ostream& operator<<(std::ostream& out,
                         BenchmarkStatus status) throw() {
  switch(status) {

  case SMT_SATISFIABLE:
    return out << "sat";

  case SMT_UNSATISFIABLE:
    return out << "unsat";

  case SMT_UNKNOWN:
    return out << "unknown";

  default:
    return out << "BenchmarkStatus::[UNKNOWNSTATUS!]";
  }
}

}/* CVC4 namespace */

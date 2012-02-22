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

void Command::toStream(std::ostream& out, int toDepth, bool types,
                       OutputLanguage language) const throw() {
  Printer::getPrinter(language)->toStream(out, this, toDepth, types);
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

/* class PushCommand */

void PushCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    smtEngine->push();
    d_commandStatus = CommandSuccess::instance();
  } catch(exception& e) {
    d_commandStatus = new CommandFailure(e.what());
  }
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

/* class QuitCommand */

QuitCommand::QuitCommand() throw() {
}

void QuitCommand::invoke(SmtEngine* smtEngine) throw() {
  Dump("benchmark") << *this;
  d_commandStatus = CommandSuccess::instance();
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
  Dump("declarations") << *this << endl;
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
  Dump("declarations") << *this << endl;
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
  Dump("declarations") << *this << endl;
  d_commandStatus = CommandSuccess::instance();
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
  //Dump("declarations") << *this << endl; -- done by SmtEngine
  if(!d_func.isNull()) {
    smtEngine->defineFunction(d_func, d_formals, d_formula);
  }
  d_commandStatus = CommandSuccess::instance();
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

/* class GetAssertionsCommand */

GetAssertionsCommand::GetAssertionsCommand() throw() {
}

void GetAssertionsCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    stringstream ss;
    const vector<Expr> v = smtEngine->getAssertions();
    copy( v.begin(), v.end(), ostream_iterator<Expr>(ss, "\n") );
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

/* class GetInfoCommand */

GetInfoCommand::GetInfoCommand(std::string flag) throw() :
  d_flag(flag) {
}

std::string GetInfoCommand::getFlag() const throw() {
  return d_flag;
}

void GetInfoCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    stringstream ss;
    ss << smtEngine->getInfo(d_flag);
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

/* class GetOptionCommand */

GetOptionCommand::GetOptionCommand(std::string flag) throw() :
  d_flag(flag) {
}

std::string GetOptionCommand::getFlag() const throw() {
  return d_flag;
}

void GetOptionCommand::invoke(SmtEngine* smtEngine) throw() {
  try {
    d_result = smtEngine->getOption(d_flag).getValue();
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
  Dump("declarations") << *this << endl;
  d_commandStatus = CommandSuccess::instance();
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
    return out << "SetBenchmarkStatusCommand::[UNKNOWNSTATUS!]";
  }
}

}/* CVC4 namespace */

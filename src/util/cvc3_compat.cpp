/*********************                                                        */
/*! \file cvc3_compat.cpp
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
** \brief CVC3 compatibility layer for CVC4
**
** CVC3 compatibility layer for CVC4.
**/

#include "cvc3_compat.h"

#include <iostream>

using namespace std;

namespace CVC3 {

std::ostream& operator<<(std::ostream& out, QueryResult qr) {
  switch(qr) {
  case SATISFIABLE: out << "SATISFIABLE/INVALID"; break;
  case UNSATISFIABLE: out << "VALID/UNSATISFIABLE"; break;
  case ABORT: out << "ABORT"; break;
  case UNKNOWN: out << "UNKNOWN"; break;
  default: out << "QueryResult!UNKNOWN";
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, FormulaValue fv) {
  switch(fv) {
  case TRUE_VAL: out << "TRUE_VAL"; break;
  case FALSE_VAL: out << "FALSE_VAL"; break;
  case UNKNOWN_VAL: out << "UNKNOWN_VAL"; break;
  default: out << "FormulaValue!UNKNOWN";
  }

  return out;
}

ValidityChecker::ValidityChecker() {
}

ValidityChecker::~ValidityChecker() {
}

CLFlags& ValidityChecker::getFlags() const {
  Unimplemented();
}

void ValidityChecker::reprocessFlags() {
  Unimplemented();
}

CLFlags ValidityChecker::createFlags() {
  Unimplemented();
}

ValidityChecker* ValidityChecker::create(const CLFlags& flags) {
  Unimplemented();
}

ValidityChecker* ValidityChecker::create() {
  Unimplemented();
}

Type ValidityChecker::boolType() {
  Unimplemented();
}

Type ValidityChecker::realType() {
  Unimplemented();
}

Type ValidityChecker::intType() {
  Unimplemented();
}

Type ValidityChecker::subrangeType(const Expr& l, const Expr& r) {
  Unimplemented();
}

Type ValidityChecker::subtypeType(const Expr& pred, const Expr& witness) {
  Unimplemented();
}

Type ValidityChecker::tupleType(const Type& type0, const Type& type1) {
  Unimplemented();
}

Type ValidityChecker::tupleType(const Type& type0, const Type& type1, const Type& type2) {
  Unimplemented();
}

Type ValidityChecker::tupleType(const std::vector<Type>& types) {
  Unimplemented();
}

Type ValidityChecker::recordType(const std::string& field, const Type& type) {
  Unimplemented();
}

Type ValidityChecker::recordType(const std::string& field0, const Type& type0,
                                 const std::string& field1, const Type& type1) {
  Unimplemented();
}

Type ValidityChecker::recordType(const std::string& field0, const Type& type0,
                                 const std::string& field1, const Type& type1,
                                 const std::string& field2, const Type& type2) {
  Unimplemented();
}

Type ValidityChecker::recordType(const std::vector<std::string>& fields,
                                 const std::vector<Type>& types) {
  Unimplemented();
}

Type ValidityChecker::dataType(const std::string& name,
                               const std::string& constructor,
                               const std::vector<std::string>& selectors,
                               const std::vector<Expr>& types) {
  Unimplemented();
}

Type ValidityChecker::dataType(const std::string& name,
                               const std::vector<std::string>& constructors,
                               const std::vector<std::vector<std::string> >& selectors,
                               const std::vector<std::vector<Expr> >& types) {
  Unimplemented();
}

void ValidityChecker::dataType(const std::vector<std::string>& names,
                               const std::vector<std::vector<std::string> >& constructors,
                               const std::vector<std::vector<std::vector<std::string> > >& selectors,
                               const std::vector<std::vector<std::vector<Expr> > >& types,
                               std::vector<Type>& returnTypes) {
  Unimplemented();
}

Type ValidityChecker::arrayType(const Type& typeIndex, const Type& typeData) {
  Unimplemented();
}

Type ValidityChecker::bitvecType(int n) {
  Unimplemented();
}

Type ValidityChecker::funType(const Type& typeDom, const Type& typeRan) {
  Unimplemented();
}

Type ValidityChecker::funType(const std::vector<Type>& typeDom, const Type& typeRan) {
  Unimplemented();
}

Type ValidityChecker::createType(const std::string& typeName) {
  Unimplemented();
}

Type ValidityChecker::createType(const std::string& typeName, const Type& def) {
  Unimplemented();
}

Type ValidityChecker::lookupType(const std::string& typeName) {
  Unimplemented();
}

ExprManager* ValidityChecker::getEM() {
  Unimplemented();
}

Expr ValidityChecker::varExpr(const std::string& name, const Type& type) {
  Unimplemented();
}

Expr ValidityChecker::varExpr(const std::string& name, const Type& type,
                              const Expr& def) {
  Unimplemented();
}

Expr ValidityChecker::lookupVar(const std::string& name, Type* type) {
  Unimplemented();
}

Type ValidityChecker::getType(const Expr& e) {
  Unimplemented();
}

Type ValidityChecker::getBaseType(const Expr& e) {
  Unimplemented();
}

Type ValidityChecker::getBaseType(const Type& t) {
  Unimplemented();
}

Expr ValidityChecker::getTypePred(const Type&t, const Expr& e) {
  Unimplemented();
}

Expr ValidityChecker::stringExpr(const std::string& str) {
  Unimplemented();
}

Expr ValidityChecker::idExpr(const std::string& name) {
  Unimplemented();
}

Expr ValidityChecker::listExpr(const std::vector<Expr>& kids) {
  Unimplemented();
}

Expr ValidityChecker::listExpr(const Expr& e1) {
  Unimplemented();
}

Expr ValidityChecker::listExpr(const Expr& e1, const Expr& e2) {
  Unimplemented();
}

Expr ValidityChecker::listExpr(const Expr& e1, const Expr& e2, const Expr& e3) {
  Unimplemented();
}

Expr ValidityChecker::listExpr(const std::string& op,
                               const std::vector<Expr>& kids) {
  Unimplemented();
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1) {
  Unimplemented();
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1,
                               const Expr& e2) {
  Unimplemented();
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1,
                               const Expr& e2, const Expr& e3) {
  Unimplemented();
}

void ValidityChecker::printExpr(const Expr& e) {
  Unimplemented();
}

void ValidityChecker::printExpr(const Expr& e, std::ostream& os) {
  Unimplemented();
}

Expr ValidityChecker::parseExpr(const Expr& e) {
  Unimplemented();
}

Type ValidityChecker::parseType(const Expr& e) {
  Unimplemented();
}

Expr ValidityChecker::importExpr(const Expr& e) {
  Unimplemented();
}

Type ValidityChecker::importType(const Type& t) {
  Unimplemented();
}

void ValidityChecker::cmdsFromString(const std::string& s, InputLanguage lang) {
  Unimplemented();
}

Expr ValidityChecker::exprFromString(const std::string& e) {
  Unimplemented();
}

Expr ValidityChecker::trueExpr() {
  Unimplemented();
}

Expr ValidityChecker::falseExpr() {
  Unimplemented();
}

Expr ValidityChecker::notExpr(const Expr& child) {
  Unimplemented();
}

Expr ValidityChecker::andExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::andExpr(const std::vector<Expr>& children) {
  Unimplemented();
}

Expr ValidityChecker::orExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::orExpr(const std::vector<Expr>& children) {
  Unimplemented();
}

Expr ValidityChecker::impliesExpr(const Expr& hyp, const Expr& conc) {
  Unimplemented();
}

Expr ValidityChecker::iffExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::eqExpr(const Expr& child0, const Expr& child1) {
  Unimplemented();
}

Expr ValidityChecker::iteExpr(const Expr& ifpart, const Expr& thenpart,
                              const Expr& elsepart) {
  Unimplemented();
}

Expr ValidityChecker::distinctExpr(const std::vector<Expr>& children) {
  Unimplemented();
}

Op ValidityChecker::createOp(const std::string& name, const Type& type) {
  Unimplemented();
}

Op ValidityChecker::createOp(const std::string& name, const Type& type,
                             const Expr& def) {
  Unimplemented();
}

Op ValidityChecker::lookupOp(const std::string& name, Type* type) {
  Unimplemented();
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& child) {
  Unimplemented();
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& child0,
                              const Expr& child1, const Expr& child2) {
  Unimplemented();
}

Expr ValidityChecker::funExpr(const Op& op, const std::vector<Expr>& children) {
  Unimplemented();
}

bool ValidityChecker::addPairToArithOrder(const Expr& smaller, const Expr& bigger) {
  Unimplemented();
}

Expr ValidityChecker::ratExpr(int n, int d) {
  Unimplemented();
}

Expr ValidityChecker::ratExpr(const std::string& n, const std::string& d, int base) {
  Unimplemented();
}

Expr ValidityChecker::ratExpr(const std::string& n, int base) {
  Unimplemented();
}

Expr ValidityChecker::uminusExpr(const Expr& child) {
  Unimplemented();
}

Expr ValidityChecker::plusExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::plusExpr(const std::vector<Expr>& children) {
  Unimplemented();
}

Expr ValidityChecker::minusExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::multExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::powExpr(const Expr& x, const Expr& n) {
  Unimplemented();
}

Expr ValidityChecker::divideExpr(const Expr& numerator, const Expr& denominator) {
  Unimplemented();
}

Expr ValidityChecker::ltExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::leExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::gtExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::geExpr(const Expr& left, const Expr& right) {
  Unimplemented();
}

Expr ValidityChecker::recordExpr(const std::string& field, const Expr& expr) {
  Unimplemented();
}

Expr ValidityChecker::recordExpr(const std::string& field0, const Expr& expr0,
                                 const std::string& field1, const Expr& expr1) {
  Unimplemented();
}

Expr ValidityChecker::recordExpr(const std::string& field0, const Expr& expr0,
                                 const std::string& field1, const Expr& expr1,
                                 const std::string& field2, const Expr& expr2) {
  Unimplemented();
}

Expr ValidityChecker::recordExpr(const std::vector<std::string>& fields,
                                 const std::vector<Expr>& exprs) {
  Unimplemented();
}

Expr ValidityChecker::recSelectExpr(const Expr& record, const std::string& field) {
  Unimplemented();
}

Expr ValidityChecker::recUpdateExpr(const Expr& record, const std::string& field,
                                    const Expr& newValue) {
  Unimplemented();
}

Expr ValidityChecker::readExpr(const Expr& array, const Expr& index) {
  Unimplemented();
}

Expr ValidityChecker::writeExpr(const Expr& array, const Expr& index,
                                const Expr& newValue) {
  Unimplemented();
}

Expr ValidityChecker::newBVConstExpr(const std::string& s, int base) {
  Unimplemented();
}

Expr ValidityChecker::newBVConstExpr(const std::vector<bool>& bits) {
  Unimplemented();
}

Expr ValidityChecker::newBVConstExpr(const Rational& r, int len) {
  Unimplemented();
}

Expr ValidityChecker::newConcatExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newConcatExpr(const std::vector<Expr>& kids) {
  Unimplemented();
}

Expr ValidityChecker::newBVExtractExpr(const Expr& e, int hi, int low) {
  Unimplemented();
}

Expr ValidityChecker::newBVNegExpr(const Expr& t1) {
  Unimplemented();
}

Expr ValidityChecker::newBVAndExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVAndExpr(const std::vector<Expr>& kids) {
  Unimplemented();
}

Expr ValidityChecker::newBVOrExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVOrExpr(const std::vector<Expr>& kids) {
  Unimplemented();
}

Expr ValidityChecker::newBVXorExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVXorExpr(const std::vector<Expr>& kids) {
  Unimplemented();
}

Expr ValidityChecker::newBVXnorExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVXnorExpr(const std::vector<Expr>& kids) {
  Unimplemented();
}

Expr ValidityChecker::newBVNandExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVNorExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVCompExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVLTExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVLEExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVSLTExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVSLEExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newSXExpr(const Expr& t1, int len) {
  Unimplemented();
}

Expr ValidityChecker::newBVUminusExpr(const Expr& t1) {
  Unimplemented();
}

Expr ValidityChecker::newBVSubExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVPlusExpr(int numbits, const std::vector<Expr>& k) {
  Unimplemented();
}

Expr ValidityChecker::newBVPlusExpr(int numbits, const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVMultExpr(int numbits,
                                    const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVUDivExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVURemExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVSDivExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVSRemExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVSModExpr(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newFixedLeftShiftExpr(const Expr& t1, int r) {
  Unimplemented();
}

Expr ValidityChecker::newFixedConstWidthLeftShiftExpr(const Expr& t1, int r) {
  Unimplemented();
}

Expr ValidityChecker::newFixedRightShiftExpr(const Expr& t1, int r) {
  Unimplemented();
}

Expr ValidityChecker::newBVSHL(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVLSHR(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Expr ValidityChecker::newBVASHR(const Expr& t1, const Expr& t2) {
  Unimplemented();
}

Rational ValidityChecker::computeBVConst(const Expr& e) {
  Unimplemented();
}

Expr ValidityChecker::tupleExpr(const std::vector<Expr>& exprs) {
  Unimplemented();
}

Expr ValidityChecker::tupleSelectExpr(const Expr& tuple, int index) {
  Unimplemented();
}

Expr ValidityChecker::tupleUpdateExpr(const Expr& tuple, int index,
                                      const Expr& newValue) {
  Unimplemented();
}

Expr ValidityChecker::datatypeConsExpr(const std::string& constructor, const std::vector<Expr>& args) {
  Unimplemented();
}

Expr ValidityChecker::datatypeSelExpr(const std::string& selector, const Expr& arg) {
  Unimplemented();
}

Expr ValidityChecker::datatypeTestExpr(const std::string& constructor, const Expr& arg) {
  Unimplemented();
}

Expr ValidityChecker::boundVarExpr(const std::string& name,
                                   const std::string& uid,
                                   const Type& type) {
  Unimplemented();
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented();
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const Expr& trigger) {
  Unimplemented();
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const std::vector<Expr>& triggers) {
  Unimplemented();
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const std::vector<std::vector<Expr> >& triggers) {
  Unimplemented();
}

void ValidityChecker::setTriggers(const Expr& e, const std::vector<std::vector<Expr> > & triggers) {
  Unimplemented();
}

void ValidityChecker::setTriggers(const Expr& e, const std::vector<Expr>& triggers) {
  Unimplemented();
}

void ValidityChecker::setTrigger(const Expr& e, const Expr& trigger) {
  Unimplemented();
}

void ValidityChecker::setMultiTrigger(const Expr& e, const std::vector<Expr>& multiTrigger) {
  Unimplemented();
}

Expr ValidityChecker::existsExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented();
}

Op ValidityChecker::lambdaExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented();
}

Op ValidityChecker::transClosure(const Op& op) {
  Unimplemented();
}

Expr ValidityChecker::simulateExpr(const Expr& f, const Expr& s0,
                                   const std::vector<Expr>& inputs,
                                   const Expr& n) {
  Unimplemented();
}

void ValidityChecker::setResourceLimit(unsigned limit) {
  Unimplemented();
}

void ValidityChecker::setTimeLimit(unsigned limit) {
  Unimplemented();
}

void ValidityChecker::assertFormula(const Expr& e) {
  Unimplemented();
}

void ValidityChecker::registerAtom(const Expr& e) {
  Unimplemented();
}

Expr ValidityChecker::getImpliedLiteral() {
  Unimplemented();
}

Expr ValidityChecker::simplify(const Expr& e) {
  Unimplemented();
}

QueryResult ValidityChecker::query(const Expr& e) {
  Unimplemented();
}

QueryResult ValidityChecker::checkUnsat(const Expr& e) {
  Unimplemented();
}

QueryResult ValidityChecker::checkContinue() {
  Unimplemented();
}

QueryResult ValidityChecker::restart(const Expr& e) {
  Unimplemented();
}

void ValidityChecker::returnFromCheck() {
  Unimplemented();
}

void ValidityChecker::getUserAssumptions(std::vector<Expr>& assumptions) {
  Unimplemented();
}

void ValidityChecker::getInternalAssumptions(std::vector<Expr>& assumptions) {
  Unimplemented();
}

void ValidityChecker::getAssumptions(std::vector<Expr>& assumptions) {
  Unimplemented();
}

void ValidityChecker::getAssumptionsUsed(std::vector<Expr>& assumptions) {
  Unimplemented();
}

Expr ValidityChecker::getProofQuery() {
  Unimplemented();
}

void ValidityChecker::getCounterExample(std::vector<Expr>& assumptions,
                                        bool inOrder) {
  Unimplemented();
}

void ValidityChecker::getConcreteModel(ExprMap<Expr> & m) {
  Unimplemented();
}

QueryResult ValidityChecker::tryModelGeneration() {
  Unimplemented();
}

FormulaValue ValidityChecker::value(const Expr& e) {
  Unimplemented();
}

bool ValidityChecker::inconsistent(std::vector<Expr>& assumptions) {
  Unimplemented();
}

bool ValidityChecker::inconsistent() {
  Unimplemented();
}

bool ValidityChecker::incomplete() {
  Unimplemented();
}

bool ValidityChecker::incomplete(std::vector<std::string>& reasons) {
  Unimplemented();
}

Proof ValidityChecker::getProof() {
  Unimplemented();
}

Expr ValidityChecker::getTCC() {
  Unimplemented();
}

void ValidityChecker::getAssumptionsTCC(std::vector<Expr>& assumptions) {
  Unimplemented();
}

Proof ValidityChecker::getProofTCC() {
  Unimplemented();
}

Expr ValidityChecker::getClosure() {
  Unimplemented();
}

Proof ValidityChecker::getProofClosure() {
  Unimplemented();
}

int ValidityChecker::stackLevel() {
  Unimplemented();
}

void ValidityChecker::push() {
  Unimplemented();
}

void ValidityChecker::pop() {
  Unimplemented();
}

void ValidityChecker::popto(int stackLevel) {
  Unimplemented();
}

int ValidityChecker::scopeLevel() {
  Unimplemented();
}

void ValidityChecker::pushScope() {
  Unimplemented();
}

void ValidityChecker::popScope() {
  Unimplemented();
}

void ValidityChecker::poptoScope(int scopeLevel) {
  Unimplemented();
}

Context* ValidityChecker::getCurrentContext() {
  Unimplemented();
}

void ValidityChecker::reset() {
  Unimplemented();
}

void ValidityChecker::logAnnotation(const Expr& annot) {
  Unimplemented();
}

void ValidityChecker::loadFile(const std::string& fileName,
                               InputLanguage lang,
                               bool interactive,
                               bool calledFromParser) {
  Unimplemented();
}

void ValidityChecker::loadFile(std::istream& is,
                               InputLanguage lang,
                               bool interactive) {
  Unimplemented();
}

Statistics& ValidityChecker::getStatistics() {
  Unimplemented();
}

void ValidityChecker::printStatistics() {
  Unimplemented();
}

}/* CVC3 namespace */

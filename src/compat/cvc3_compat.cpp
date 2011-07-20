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

#include "compat/cvc3_compat.h"

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
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::reprocessFlags() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

CLFlags ValidityChecker::createFlags() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

ValidityChecker* ValidityChecker::create(const CLFlags& flags) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

ValidityChecker* ValidityChecker::create() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::boolType() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::realType() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::intType() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::subrangeType(const Expr& l, const Expr& r) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::subtypeType(const Expr& pred, const Expr& witness) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::tupleType(const Type& type0, const Type& type1) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::tupleType(const Type& type0, const Type& type1, const Type& type2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::tupleType(const std::vector<Type>& types) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::recordType(const std::string& field, const Type& type) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::recordType(const std::string& field0, const Type& type0,
                                 const std::string& field1, const Type& type1) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::recordType(const std::string& field0, const Type& type0,
                                 const std::string& field1, const Type& type1,
                                 const std::string& field2, const Type& type2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::recordType(const std::vector<std::string>& fields,
                                 const std::vector<Type>& types) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::dataType(const std::string& name,
                               const std::string& constructor,
                               const std::vector<std::string>& selectors,
                               const std::vector<Expr>& types) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::dataType(const std::string& name,
                               const std::vector<std::string>& constructors,
                               const std::vector<std::vector<std::string> >& selectors,
                               const std::vector<std::vector<Expr> >& types) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::dataType(const std::vector<std::string>& names,
                               const std::vector<std::vector<std::string> >& constructors,
                               const std::vector<std::vector<std::vector<std::string> > >& selectors,
                               const std::vector<std::vector<std::vector<Expr> > >& types,
                               std::vector<Type>& returnTypes) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::arrayType(const Type& typeIndex, const Type& typeData) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::bitvecType(int n) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::funType(const Type& typeDom, const Type& typeRan) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::funType(const std::vector<Type>& typeDom, const Type& typeRan) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::createType(const std::string& typeName) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::createType(const std::string& typeName, const Type& def) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::lookupType(const std::string& typeName) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

ExprManager* ValidityChecker::getEM() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::varExpr(const std::string& name, const Type& type) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::varExpr(const std::string& name, const Type& type,
                              const Expr& def) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::lookupVar(const std::string& name, Type* type) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::getType(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::getBaseType(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::getBaseType(const Type& t) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getTypePred(const Type&t, const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::stringExpr(const std::string& str) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::idExpr(const std::string& name) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::listExpr(const std::vector<Expr>& kids) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::listExpr(const Expr& e1) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::listExpr(const Expr& e1, const Expr& e2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::listExpr(const Expr& e1, const Expr& e2, const Expr& e3) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::listExpr(const std::string& op,
                               const std::vector<Expr>& kids) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1,
                               const Expr& e2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1,
                               const Expr& e2, const Expr& e3) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::printExpr(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::printExpr(const Expr& e, std::ostream& os) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::parseExpr(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::parseType(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::importExpr(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Type ValidityChecker::importType(const Type& t) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::cmdsFromString(const std::string& s, InputLanguage lang) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::exprFromString(const std::string& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::trueExpr() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::falseExpr() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::notExpr(const Expr& child) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::andExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::andExpr(const std::vector<Expr>& children) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::orExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::orExpr(const std::vector<Expr>& children) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::impliesExpr(const Expr& hyp, const Expr& conc) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::iffExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::eqExpr(const Expr& child0, const Expr& child1) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::iteExpr(const Expr& ifpart, const Expr& thenpart,
                              const Expr& elsepart) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::distinctExpr(const std::vector<Expr>& children) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Op ValidityChecker::createOp(const std::string& name, const Type& type) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Op ValidityChecker::createOp(const std::string& name, const Type& type,
                             const Expr& def) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Op ValidityChecker::lookupOp(const std::string& name, Type* type) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& child) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& child0,
                              const Expr& child1, const Expr& child2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::funExpr(const Op& op, const std::vector<Expr>& children) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool ValidityChecker::addPairToArithOrder(const Expr& smaller, const Expr& bigger) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::ratExpr(int n, int d) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::ratExpr(const std::string& n, const std::string& d, int base) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::ratExpr(const std::string& n, int base) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::uminusExpr(const Expr& child) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::plusExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::plusExpr(const std::vector<Expr>& children) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::minusExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::multExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::powExpr(const Expr& x, const Expr& n) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::divideExpr(const Expr& numerator, const Expr& denominator) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::ltExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::leExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::gtExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::geExpr(const Expr& left, const Expr& right) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::recordExpr(const std::string& field, const Expr& expr) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::recordExpr(const std::string& field0, const Expr& expr0,
                                 const std::string& field1, const Expr& expr1) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::recordExpr(const std::string& field0, const Expr& expr0,
                                 const std::string& field1, const Expr& expr1,
                                 const std::string& field2, const Expr& expr2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::recordExpr(const std::vector<std::string>& fields,
                                 const std::vector<Expr>& exprs) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::recSelectExpr(const Expr& record, const std::string& field) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::recUpdateExpr(const Expr& record, const std::string& field,
                                    const Expr& newValue) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::readExpr(const Expr& array, const Expr& index) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::writeExpr(const Expr& array, const Expr& index,
                                const Expr& newValue) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVConstExpr(const std::string& s, int base) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVConstExpr(const std::vector<bool>& bits) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVConstExpr(const Rational& r, int len) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newConcatExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newConcatExpr(const std::vector<Expr>& kids) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVExtractExpr(const Expr& e, int hi, int low) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVNegExpr(const Expr& t1) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVAndExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVAndExpr(const std::vector<Expr>& kids) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVOrExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVOrExpr(const std::vector<Expr>& kids) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVXorExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVXorExpr(const std::vector<Expr>& kids) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVXnorExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVXnorExpr(const std::vector<Expr>& kids) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVNandExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVNorExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVCompExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVLTExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVLEExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVSLTExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVSLEExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newSXExpr(const Expr& t1, int len) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVUminusExpr(const Expr& t1) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVSubExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVPlusExpr(int numbits, const std::vector<Expr>& k) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVPlusExpr(int numbits, const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVMultExpr(int numbits,
                                    const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVUDivExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVURemExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVSDivExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVSRemExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVSModExpr(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newFixedLeftShiftExpr(const Expr& t1, int r) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newFixedConstWidthLeftShiftExpr(const Expr& t1, int r) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newFixedRightShiftExpr(const Expr& t1, int r) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVSHL(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVLSHR(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVASHR(const Expr& t1, const Expr& t2) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Rational ValidityChecker::computeBVConst(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::tupleExpr(const std::vector<Expr>& exprs) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::tupleSelectExpr(const Expr& tuple, int index) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::tupleUpdateExpr(const Expr& tuple, int index,
                                      const Expr& newValue) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::datatypeConsExpr(const std::string& constructor, const std::vector<Expr>& args) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::datatypeSelExpr(const std::string& selector, const Expr& arg) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::datatypeTestExpr(const std::string& constructor, const Expr& arg) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::boundVarExpr(const std::string& name,
                                   const std::string& uid,
                                   const Type& type) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const Expr& trigger) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const std::vector<Expr>& triggers) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const std::vector<std::vector<Expr> >& triggers) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setTriggers(const Expr& e, const std::vector<std::vector<Expr> > & triggers) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setTriggers(const Expr& e, const std::vector<Expr>& triggers) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setTrigger(const Expr& e, const Expr& trigger) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setMultiTrigger(const Expr& e, const std::vector<Expr>& multiTrigger) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::existsExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Op ValidityChecker::lambdaExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Op ValidityChecker::transClosure(const Op& op) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::simulateExpr(const Expr& f, const Expr& s0,
                                   const std::vector<Expr>& inputs,
                                   const Expr& n) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setResourceLimit(unsigned limit) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setTimeLimit(unsigned limit) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::assertFormula(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::registerAtom(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getImpliedLiteral() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::simplify(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::query(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::checkUnsat(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::checkContinue() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::restart(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::returnFromCheck() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getUserAssumptions(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getInternalAssumptions(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getAssumptions(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getAssumptionsUsed(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getProofQuery() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getCounterExample(std::vector<Expr>& assumptions,
                                        bool inOrder) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getConcreteModel(ExprMap<Expr> & m) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::tryModelGeneration() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

FormulaValue ValidityChecker::value(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool ValidityChecker::inconsistent(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool ValidityChecker::inconsistent() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool ValidityChecker::incomplete() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool ValidityChecker::incomplete(std::vector<std::string>& reasons) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Proof ValidityChecker::getProof() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getTCC() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getAssumptionsTCC(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Proof ValidityChecker::getProofTCC() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getClosure() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Proof ValidityChecker::getProofClosure() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

int ValidityChecker::stackLevel() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::push() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::pop() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::popto(int stackLevel) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

int ValidityChecker::scopeLevel() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::pushScope() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::popScope() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::poptoScope(int scopeLevel) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Context* ValidityChecker::getCurrentContext() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::reset() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::logAnnotation(const Expr& annot) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::loadFile(const std::string& fileName,
                               InputLanguage lang,
                               bool interactive,
                               bool calledFromParser) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::loadFile(std::istream& is,
                               InputLanguage lang,
                               bool interactive) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Statistics& ValidityChecker::getStatistics() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::printStatistics() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

}/* CVC3 namespace */

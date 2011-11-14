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

#include "expr/kind.h"
#include "expr/command.h"

#include "util/rational.h"
#include "util/integer.h"
#include "util/bitvector.h"
#include "util/hash.h"

#include "parser/parser.h"
#include "parser/parser_builder.h"

#include "parser/options.h"
#include "smt/options.h"
#include "expr/options.h"

#include <iostream>
#include <string>
#include <sstream>
#include <algorithm>
#include <iterator>

using namespace std;

namespace CVC3 {

static std::hash_map<Type, Expr, CVC4::TypeHashFunction> s_typeToExpr;
static std::hash_map<Expr, Type, CVC4::ExprHashFunction> s_exprToType;

static bool typeHasExpr(const Type& t) {
  std::hash_map<Type, Expr, CVC4::TypeHashFunction>::const_iterator i = s_typeToExpr.find(t);
  return i != s_typeToExpr.end();
}

static Expr typeToExpr(const Type& t) {
  std::hash_map<Type, Expr, CVC4::TypeHashFunction>::const_iterator i = s_typeToExpr.find(t);
  AlwaysAssert(i != s_typeToExpr.end());
  return (*i).second;
}

static Type exprToType(const Expr& e) {
  std::hash_map<Expr, Type, CVC4::ExprHashFunction>::const_iterator i = s_exprToType.find(e);
  AlwaysAssert(i != s_exprToType.end());
  return (*i).second;
}

std::string int2string(int n) {
  std::ostringstream ss;
  ss << n;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, CLFlagType clft) {
  switch(clft) {
  case CLFLAG_NULL: out << "CLFLAG_NULL";
  case CLFLAG_BOOL: out << "CLFLAG_BOOL";
  case CLFLAG_INT: out << "CLFLAG_INT";
  case CLFLAG_STRING: out << "CLFLAG_STRING";
  case CLFLAG_STRVEC: out << "CLFLAG_STRVEC";
  default: out << "CLFlagType!UNKNOWN";
  }

  return out;
}

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

std::string QueryResultToString(QueryResult qr) {
  stringstream sstr;
  sstr << qr;
  return sstr.str();
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

std::ostream& operator<<(std::ostream& out, CVC3CardinalityKind c) {
  switch(c) {
  case CARD_FINITE: out << "CARD_FINITE"; break;
  case CARD_INFINITE: out << "CARD_INFINITE"; break;
  case CARD_UNKNOWN: out << "CARD_UNKNOWN"; break;
  default: out << "CVC3CardinalityKind!UNKNOWN";
  }

  return out;
}

static string toString(CLFlagType clft) {
  stringstream sstr;
  sstr << clft;
  return sstr.str();
}

bool operator==(const Cardinality& c, CVC3CardinalityKind d) {
  switch(d) {
  case CARD_FINITE:
    return c.isFinite();
  case CARD_INFINITE:
    return c.isInfinite();
  case CARD_UNKNOWN:
    return c.isUnknown();
  }

  Unhandled(d);
}

bool operator==(CVC3CardinalityKind d, const Cardinality& c) {
  return c == d;
}

bool operator!=(const Cardinality& c, CVC3CardinalityKind d) {
  return !(c == d);
}

bool operator!=(CVC3CardinalityKind d, const Cardinality& c) {
  return !(c == d);
}

Type::Type() :
  CVC4::Type() {
}

Type::Type(const CVC4::Type& type) :
  CVC4::Type(type) {
}

Type::Type(const Type& type) :
  CVC4::Type(type) {
}

Expr Type::getExpr() const {
  if(typeHasExpr(*this)) {
    return typeToExpr(*this);
  }
  Expr e = getExprManager()->mkVar("compatibility-layer-expr-type", *this);
  s_typeToExpr[*this] = e;
  s_exprToType[e] = *this;
  return e;
}

int Type::arity() const {
  return isSort() ? CVC4::SortType(*this).getParamTypes().size() : 0;
}

Type Type::operator[](int i) const {
  return Type(CVC4::Type(CVC4::SortType(*this).getParamTypes()[i]));
}

bool Type::isBool() const {
  return isBoolean();
}

bool Type::isSubtype() const {
  return false;
}

Cardinality Type::card() const {
  return getCardinality();
}

Expr Type::enumerateFinite(Unsigned n) const {
  Unimplemented();
}

Unsigned Type::sizeFinite() const {
  return getCardinality().getFiniteCardinality().getUnsignedLong();
}

Type Type::typeBool(ExprManager* em) {
  return Type(CVC4::Type(em->booleanType()));
}

Type Type::funType(const std::vector<Type>& typeDom,
                   const Type& typeRan) {
  const vector<CVC4::Type>& dom =
    *reinterpret_cast<const vector<CVC4::Type>*>(&typeDom);
  return Type(typeRan.getExprManager()->mkFunctionType(dom, typeRan));
}

Type Type::funType(const Type& typeRan) const {
  return Type(getExprManager()->mkFunctionType(*this, typeRan));
}

Expr::Expr() : CVC4::Expr() {
}

Expr::Expr(const Expr& e) : CVC4::Expr(e) {
}

Expr::Expr(const CVC4::Expr& e) : CVC4::Expr(e) {
}

Expr Expr::eqExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::EQUAL, *this, right);
}

Expr Expr::notExpr() const {
  return getEM()->mkExpr(CVC4::kind::NOT, *this);
}

Expr Expr::negate() const {
  // avoid double-negatives
  return (getKind() == CVC4::kind::NOT) ?
    (*this)[0] :
    Expr(getEM()->mkExpr(CVC4::kind::NOT, *this));
}

Expr Expr::andExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::AND, *this, right);
}

Expr Expr::orExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::OR, *this, right);
}

Expr Expr::iteExpr(const Expr& thenpart, const Expr& elsepart) const {
  return getEM()->mkExpr(CVC4::kind::ITE, *this, thenpart, elsepart);
}

Expr Expr::iffExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::IFF, *this, right);
}

Expr Expr::impExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::IMPLIES, *this, right);
}

Expr Expr::xorExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::XOR, *this, right);
}

Expr Expr::substExpr(const std::vector<Expr>& oldTerms,
                     const std::vector<Expr>& newTerms) const {
  const vector<CVC4::Expr>& o =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&oldTerms);
  const vector<CVC4::Expr>& n =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&newTerms);

  return Expr(substitute(o, n));
}

Expr Expr::substExpr(const ExprHashMap<Expr>& oldToNew) const {
  const hash_map<CVC4::Expr, CVC4::Expr, CVC4::ExprHashFunction>& o2n =
    *reinterpret_cast<const hash_map<CVC4::Expr, CVC4::Expr, CVC4::ExprHashFunction>*>(&oldToNew);

  return Expr(substitute(o2n));
}

Expr Expr::operator!() const {
  return notExpr();
}

Expr Expr::operator&&(const Expr& right) const {
  return andExpr(right);
}

Expr Expr::operator||(const Expr& right) const {
  return orExpr(right);
}

size_t Expr::hash(const Expr& e) {
  return CVC4::ExprHashFunction()(e);
}

size_t Expr::hash() const {
  return CVC4::ExprHashFunction()(*this);
}

bool Expr::isFalse() const {
  return getKind() == CVC4::kind::CONST_BOOLEAN && getConst<bool>() == false;
}

bool Expr::isTrue() const {
  return getKind() == CVC4::kind::CONST_BOOLEAN && getConst<bool>() == true;
}

bool Expr::isBoolConst() const {
  return getKind() == CVC4::kind::CONST_BOOLEAN;
}

bool Expr::isVar() const {
  return isVariable();
}

bool Expr::isString() const {
  return false;
}

bool Expr::isApply() const {
  return hasOperator();
}

bool Expr::isTheorem() const {
  return false;
}

bool Expr::isConstant() const {
  return isConst();
}

bool Expr::isRawList() const {
  return false;
}

bool Expr::isEq() const {
  return getKind() == CVC4::kind::EQUAL;
}

bool Expr::isNot() const {
  return getKind() == CVC4::kind::NOT;
}

bool Expr::isAnd() const {
  return getKind() == CVC4::kind::AND;
}

bool Expr::isOr() const {
  return getKind() == CVC4::kind::OR;
}

bool Expr::isITE() const {
  return getKind() == CVC4::kind::ITE;
}

bool Expr::isIff() const {
  return getKind() == CVC4::kind::IFF;
}

bool Expr::isImpl() const {
  return getKind() == CVC4::kind::IMPLIES;
}

bool Expr::isXor() const {
  return getKind() == CVC4::kind::XOR;
}

bool Expr::isRational() const {
  return getKind() == CVC4::kind::CONST_RATIONAL;
}

bool Expr::isSkolem() const {
  return getKind() == CVC4::kind::SKOLEM;
}

Op Expr::mkOp() const {
  return *this;
}

Op Expr::getOp() const {
  return getOperator();
}

Expr Expr::getOpExpr() const {
  return getOperator();
}

int Expr::getOpKind() const {
  Expr op = getOperator();
  int k = op.getKind();
  return k == BUILTIN ? getKind() : k;
}

Expr Expr::getExpr() const {
  return *this;
}

std::vector< std::vector<Expr> > Expr::getTriggers() const {
  return vector< vector<Expr> >();
}

ExprManager* Expr::getEM() const {
  return getExprManager();
}

std::vector<Expr> Expr::getKids() const {
  vector<CVC4::Expr> v = getChildren();
  return *reinterpret_cast<vector<Expr>*>(&v);
}

ExprIndex Expr::getIndex() const {
  return getId();
}

int Expr::arity() const {
  return getNumChildren();
}

Expr Expr::unnegate() const {
  return isNot() ? Expr((*this)[0]) : *this;
}

bool Expr::isInitialized() const {
  return !isNull();
}

Type Expr::getType() const {
  return Type(this->CVC4::Expr::getType());
}

Type Expr::lookupType() const {
  return getType();
}

Expr Expr::operator[](int i) const {
  return Expr(this->CVC4::Expr::operator[](i));
}

CLFlag::CLFlag(bool b, const std::string& help, bool display) :
  d_tp(CLFLAG_BOOL) {
  d_data.b = b;
}

CLFlag::CLFlag(int i, const std::string& help, bool display) :
  d_tp(CLFLAG_INT) {
  d_data.i = i;
}

CLFlag::CLFlag(const std::string& s, const std::string& help, bool display) :
  d_tp(CLFLAG_STRING) {
  d_data.s = new string(s);
}

CLFlag::CLFlag(const char* s, const std::string& help, bool display) :
  d_tp(CLFLAG_STRING) {
  d_data.s = new string(s);
}

CLFlag::CLFlag(const std::vector<std::pair<string,bool> >& sv,
               const std::string& help, bool display) :
  d_tp(CLFLAG_STRVEC) {
  d_data.sv = new vector<pair<string, bool> >(sv);
}

CLFlag::CLFlag() :
  d_tp(CLFLAG_NULL) {
}

CLFlag::CLFlag(const CLFlag& f) :
  d_tp(f.d_tp) {
  switch(d_tp) {
  case CLFLAG_STRING:
    d_data.s = new string(*f.d_data.s);
    break;
  case CLFLAG_STRVEC:
    d_data.sv = new vector<pair<string, bool> >(*f.d_data.sv);
    break;
  default:
    d_data = f.d_data;
  }
}

CLFlag::~CLFlag() {
  switch(d_tp) {
  case CLFLAG_STRING:
    delete d_data.s;
    break;
  case CLFLAG_STRVEC:
    delete d_data.sv;
    break;
  default:
    ; // nothing to do
  }
}

CLFlag& CLFlag::operator=(const CLFlag& f) {
  if(this == &f) {
    // self-assignment
    return *this;
  }

  // try to preserve the existing heap objects if possible
  if(d_tp == f.d_tp) {
    switch(d_tp) {
    case CLFLAG_STRING:
      *d_data.s = *f.d_data.s;
      break;
    case CLFLAG_STRVEC:
      *d_data.sv = *f.d_data.sv;
      break;
    default:
      d_data = f.d_data;
    }
  } else {
    switch(d_tp) {
    case CLFLAG_STRING:
      delete d_data.s;
      break;
    case CLFLAG_STRVEC:
      delete d_data.sv;
      break;
    default:
      ; // nothing to do here
    }

    switch(f.d_tp) {
    case CLFLAG_STRING:
      d_data.s = new string(*f.d_data.s);
      break;
    case CLFLAG_STRVEC:
      d_data.sv = new vector<pair<string, bool> >(*f.d_data.sv);
      break;
    default:
      d_data = f.d_data;
    }
  }
  d_tp = f.d_tp;
  return *this;
}

CLFlag& CLFlag::operator=(bool b) {
  CheckArgument(d_tp == CLFLAG_BOOL, this);
  d_data.b = b;
  return *this;
}

CLFlag& CLFlag::operator=(int i) {
  CheckArgument(d_tp == CLFLAG_INT, this);
  d_data.i = i;
  return *this;
}

CLFlag& CLFlag::operator=(const std::string& s) {
  CheckArgument(d_tp == CLFLAG_STRING, this);
  *d_data.s = s;
  return *this;
}

CLFlag& CLFlag::operator=(const char* s) {
  CheckArgument(d_tp == CLFLAG_STRING, this);
  *d_data.s = s;
  return *this;
}

CLFlag& CLFlag::operator=(const std::pair<string, bool>& p) {
  CheckArgument(d_tp == CLFLAG_STRVEC, this);
  d_data.sv->push_back(p);
  return *this;
}

CLFlag& CLFlag::operator=(const std::vector<std::pair<string, bool> >& sv) {
  CheckArgument(d_tp == CLFLAG_STRVEC, this);
  *d_data.sv = sv;
  return *this;
}

CLFlagType CLFlag::getType() const {
  return d_tp;
}

bool CLFlag::modified() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool CLFlag::display() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

const bool& CLFlag::getBool() const {
  CheckArgument(d_tp == CLFLAG_BOOL, this);
  return d_data.b;
}

const int& CLFlag::getInt() const {
  CheckArgument(d_tp == CLFLAG_INT, this);
  return d_data.i;
}

const std::string& CLFlag::getString() const {
  CheckArgument(d_tp == CLFLAG_STRING, this);
  return *d_data.s;
}

const std::vector<std::pair<string, bool> >& CLFlag::getStrVec() const {
  CheckArgument(d_tp == CLFLAG_STRVEC, this);
  return *d_data.sv;
}

const std::string& CLFlag::getHelp() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void CLFlags::addFlag(const std::string& name, const CLFlag& f) {
  d_map[name] = f;
}

size_t CLFlags::countFlags(const std::string& name) const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

size_t CLFlags::countFlags(const std::string& name,
                           std::vector<std::string>& names) const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

const CLFlag& CLFlags::getFlag(const std::string& name) const {
  FlagMap::const_iterator i = d_map.find(name);
  CheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  return (*i).second;
}

const CLFlag& CLFlags::operator[](const std::string& name) const {
  return getFlag(name);
}

void CLFlags::setFlag(const std::string& name, const CLFlag& f) {
  FlagMap::iterator i = d_map.find(name);
  CheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  CheckArgument((*i).second.getType() == f.getType(), f,
                "Command-line flag `%s' has type %s, but caller tried to set to a %s.",
                name.c_str(),
                toString((*i).second.getType()).c_str(),
                toString(f.getType()).c_str());
  (*i).second = f;
}

void CLFlags::setFlag(const std::string& name, bool b) {
  FlagMap::iterator i = d_map.find(name);
  CheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = b;
}

void CLFlags::setFlag(const std::string& name, int i) {
  FlagMap::iterator it = d_map.find(name);
  CheckArgument(it != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*it).second = i;
}

void CLFlags::setFlag(const std::string& name, const std::string& s) {
  FlagMap::iterator i = d_map.find(name);
  CheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = s;
}

void CLFlags::setFlag(const std::string& name, const char* s) {
  FlagMap::iterator i = d_map.find(name);
  CheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = s;
}

void CLFlags::setFlag(const std::string& name, const std::pair<string, bool>& p) {
  FlagMap::iterator i = d_map.find(name);
  CheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = p;
}

void CLFlags::setFlag(const std::string& name,
                      const std::vector<std::pair<string, bool> >& sv) {
  FlagMap::iterator i = d_map.find(name);
  CheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = sv;
}

void ValidityChecker::setUpOptions(CVC4::OptionsClass& options, const CLFlags& clflags) {
  // always incremental and model-producing in CVC3 compatibility mode
  d_smt->setOption("incremental", string("true"));
  d_smt->setOption("produce-models", string("true"));

  d_smt->setOption("statistics", string(clflags["stats"].getBool() ? "true" : "false"));
  //d_smt->setOption("random-seed", double(clflags["seed"].getInt()));
  d_smt->setOption("interactive-mode", string(clflags["interactive"].getBool() ? "true" : "false"));
  if(options[CVC4::interactive]) {
    //options[CVC4::interactiveSetByUser] = true;
  }
  d_smt->setOption("parse-only", string(clflags["parse-only"].getBool() ? "true" : "false"));
  d_smt->setOption("input-language", clflags["lang"].getString());
  if(clflags["output-lang"].getString() == "") {
    //d_smt->setOption("output-language", CVC4::language::toOutputLanguage(options[CVC4::inputLanguage]));
  } else {
    d_smt->setOption("output-language", clflags["output-lang"].getString());
  }
}

ValidityChecker::ValidityChecker() :
  d_clflags(new CLFlags()),
  d_options() {
  setUpOptions(d_options, *d_clflags);
  d_em = new CVC4::ExprManager(d_options);
  d_smt = new CVC4::SmtEngine(d_em);
  d_parserContext = CVC4::parser::ParserBuilder(d_em, "<internal>").withInputLanguage(CVC4::language::input::LANG_CVC4).withStringInput("").build();
}

ValidityChecker::ValidityChecker(const CLFlags& clflags) :
  d_clflags(new CLFlags(clflags)),
  d_options() {
  setUpOptions(d_options, *d_clflags);
  d_em = new CVC4::ExprManager(d_options);
  d_smt = new CVC4::SmtEngine(d_em);
  d_parserContext = CVC4::parser::ParserBuilder(d_em, "<internal>").withInputLanguage(CVC4::language::input::LANG_CVC4).withStringInput("").build();
}

ValidityChecker::~ValidityChecker() {
  delete d_parserContext;
  delete d_clflags;
}

CLFlags& ValidityChecker::getFlags() const {
  return *d_clflags;
}

void ValidityChecker::reprocessFlags() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

CLFlags ValidityChecker::createFlags() {
  CLFlags flags;

  // We expect the user to type cvc3 -h to get help, which will set
  // the "help" flag to false; that's why it's initially true.

  // Overall system control flags
  flags.addFlag("timeout", CLFlag(0, "Kill cvc3 process after given number of seconds (0==no limit)"));
  flags.addFlag("stimeout", CLFlag(0, "Set time resource limit in tenths of seconds for a query(0==no limit)"));
  flags.addFlag("resource", CLFlag(0, "Set finite resource limit (0==no limit)"));
  flags.addFlag("mm", CLFlag("chunks", "Memory manager (chunks, malloc)"));

  // Information printing flags
  flags.addFlag("help",CLFlag(true, "print usage information and exit"));
  flags.addFlag("unsupported",CLFlag(true, "print usage for old/unsupported/experimental options"));
  flags.addFlag("version",CLFlag(true, "print version information and exit"));
  flags.addFlag("interactive", CLFlag(false, "Interactive mode"));
  flags.addFlag("stats", CLFlag(false, "Print run-time statistics"));
  flags.addFlag("seed", CLFlag(91648253, "Set the seed for random sequence"));
  flags.addFlag("printResults", CLFlag(true, "Print results of interactive commands."));
  flags.addFlag("dump-log", CLFlag("", "Dump API call log in CVC3 input "
                                   "format to given file "
                                   "(off when file name is \"\")"));
  flags.addFlag("parse-only", CLFlag(false,"Parse the input, then exit."));

  //Translation related flags
  flags.addFlag("expResult", CLFlag("", "For smtlib translation.  Give the expected result", false));
  flags.addFlag("category", CLFlag("unknown", "For smtlib translation.  Give the category", false));
  flags.addFlag("translate", CLFlag(false, "Produce a complete translation from "
                                    "the input language to output language.  "));
  flags.addFlag("real2int", CLFlag(false, "When translating, convert reals to integers.", false));
  flags.addFlag("convertArith", CLFlag(false, "When translating, try to rewrite arith terms into smt-lib subset", false));
  flags.addFlag("convert2diff", CLFlag("", "When translating, try to force into difference logic.  Legal values are int and real.", false));
  flags.addFlag("iteLiftArith", CLFlag(false, "For translation.  If true, ite's are lifted out of arith exprs.", false));
  flags.addFlag("convertArray", CLFlag(false, "For translation.  If true, arrays are converted to uninterpreted functions if possible.", false));
  flags.addFlag("combineAssump", CLFlag(false, "For translation.  If true, assumptions are combined into the query.", false));
  flags.addFlag("convert2array", CLFlag(false, "For translation. If true, try to convert to array-only theory", false));
  flags.addFlag("convertToBV",CLFlag(0, "For translation.  Set to nonzero to convert ints to bv's of that length", false));
  flags.addFlag("convert-eq-iff",CLFlag(false, "Convert equality on Boolean expressions to iff.", false));
  flags.addFlag("preSimplify",CLFlag(false, "Simplify each assertion or query before translating it", false));
  flags.addFlag("dump-tcc", CLFlag(false, "Compute and dump TCC only"));
  flags.addFlag("trans-skip-pp", CLFlag(false, "Skip preprocess step in translation module", false));
  flags.addFlag("trans-skip-difficulty", CLFlag(false, "Leave out difficulty attribute during translation to SMT v2.0", false));
  flags.addFlag("promote", CLFlag(true, "Promote undefined logic combinations to defined logic combinations during translation to SMT", false));

  // Parser related flags
  flags.addFlag("old-func-syntax",CLFlag(false, "Enable parsing of old-style function syntax", false));

  // Pretty-printing related flags
  flags.addFlag("dagify-exprs",
                CLFlag(true, "Print expressions with sharing as DAGs"));
  flags.addFlag("lang", CLFlag("presentation", "Input language "
                               "(presentation, smt, smt2, internal)"));
  flags.addFlag("output-lang", CLFlag("", "Output language "
                                      "(presentation, smtlib, simplify, internal, lisp, tptp, spass)"));
  flags.addFlag("indent", CLFlag(false, "Print expressions with indentation"));
  flags.addFlag("width", CLFlag(80, "Suggested line width for printing"));
  flags.addFlag("print-depth", CLFlag(-1, "Max. depth to print expressions "));
  flags.addFlag("print-assump", CLFlag(false, "Print assumptions in Theorems "));

  // Search Engine (SAT) related flags
  flags.addFlag("sat",CLFlag("minisat", "choose a SAT solver to use "
                             "(sat, minisat)"));
  flags.addFlag("de",CLFlag("dfs", "choose a decision engine to use "
                            "(dfs, sat)"));

  // Proofs and Assumptions
  flags.addFlag("proofs", CLFlag(false, "Produce proofs"));
  flags.addFlag("check-proofs", CLFlag(false, "Check proofs on-the-fly"));
  flags.addFlag("minimizeClauses", CLFlag(false, "Use brute-force minimization of clauses", false));
  flags.addFlag("dynack", CLFlag(false, "Use dynamic Ackermannization", false));
  flags.addFlag("smart-clauses", CLFlag(true, "Learn multiple clauses per conflict"));
  // Core framework switches
  flags.addFlag("tcc", CLFlag(false, "Check TCCs for each ASSERT and QUERY"));
  flags.addFlag("cnf", CLFlag(true, "Convert top-level Boolean formulas to CNF", false));
  flags.addFlag("ignore-cnf-vars", CLFlag(false, "Do not split on aux. CNF vars (with +cnf)", false));
  flags.addFlag("orig-formula", CLFlag(false, "Preserve the original formula with +cnf (for splitter heuristics)", false));
  flags.addFlag("liftITE", CLFlag(false, "Eagerly lift all ITE exprs"));
  flags.addFlag("iflift", CLFlag(false, "Translate if-then-else terms to CNF (with +cnf)", false));
  flags.addFlag("circuit", CLFlag(false, "With +cnf, use circuit propagation", false));
  flags.addFlag("un-ite-ify", CLFlag(false, "Unconvert ITE expressions", false));
  flags.addFlag("ite-cond-simp",
                CLFlag(false, "Replace ITE condition by TRUE/FALSE in subexprs", false));
  flags.addFlag("preprocess", CLFlag(true, "Preprocess queries"));
  flags.addFlag("pp-pushneg", CLFlag(false, "Push negation in preprocessor"));
  flags.addFlag("pp-bryant", CLFlag(false, "Enable Bryant algorithm for UF", false));
  flags.addFlag("pp-budget", CLFlag(0, "Budget for new preprocessing step", false));
  flags.addFlag("pp-care", CLFlag(true, "Enable care-set preprocessing step", false));
  flags.addFlag("simp-and", CLFlag(false, "Rewrite x&y to x&y[x/true]", false));
  flags.addFlag("simp-or", CLFlag(false, "Rewrite x|y to x|y[x/false]", false));
  flags.addFlag("pp-batch", CLFlag(false, "Ignore assumptions until query, then process all at once"));

  // Negate the query when translate into tptp
  flags.addFlag("negate-query", CLFlag(true, "Negate the query when translate into TPTP format"));;

  // Concrete model generation (counterexamples) flags
  flags.addFlag("counterexample", CLFlag(false, "Dump counterexample if formula is invalid or satisfiable"));
  flags.addFlag("model", CLFlag(false, "Dump model if formula is invalid or satisfiable"));
  flags.addFlag("unknown-check-model", CLFlag(false, "Try to generate model if formula is unknown"));
  flags.addFlag("applications", CLFlag(true, "Add relevant function applications and array accesses to the concrete countermodel"));
  // Debugging flags (only for the debug build)
  // #ifdef _CVC3_DEBUG_MODE
  vector<pair<string,bool> > sv;
  flags.addFlag("trace", CLFlag(sv, "Tracing.  Multiple flags add up."));
  flags.addFlag("dump-trace", CLFlag("", "Dump debugging trace to "
                                   "given file (off when file name is \"\")"));
  // #endif
  // DP-specific flags

  // Arithmetic
  flags.addFlag("arith-new",CLFlag(false, "Use new arithmetic dp", false));
  flags.addFlag("arith3",CLFlag(false, "Use old arithmetic dp that works well with combined theories", false));
  flags.addFlag("var-order",
                CLFlag(false, "Use simple variable order in arith", false));
  flags.addFlag("ineq-delay", CLFlag(0, "Accumulate this many inequalities before processing (-1 for don't process until necessary)"));

  flags.addFlag("nonlinear-sign-split", CLFlag(true, "Whether to split on the signs of nontrivial nonlinear terms"));

  flags.addFlag("grayshadow-threshold", CLFlag(-1, "Ignore gray shadows bigger than this (makes solver incomplete)"));
  flags.addFlag("pathlength-threshold", CLFlag(-1, "Ignore gray shadows bigger than this (makes solver incomplete)"));

  // Arrays
  flags.addFlag("liftReadIte", CLFlag(true, "Lift read of ite"));

  //for LFSC stuff, disable Tseitin CNF conversion, by Yeting
  flags.addFlag("cnf-formula", CLFlag(false, "The input must be in CNF. This option automatically enables '-de sat' and disable preprocess"));

  //for LFSC print out, by Yeting
  //flags.addFlag("lfsc", CLFlag(false, "the input is already in CNF. This option automatically enables -de sat and disable -preprocess"));

  // for LFSC print, allows different modes by Liana
  flags.addFlag("lfsc-mode",
                  CLFlag(0, "lfsc mode 0: off, 1:normal, 2:cvc3-mimic etc."));


  // Quantifiers
  flags.addFlag("max-quant-inst", CLFlag(200, "The maximum number of"
                                " naive instantiations"));

  flags.addFlag("quant-new",
                 CLFlag(true, "If this option is false, only naive instantiation is called"));

  flags.addFlag("quant-lazy", CLFlag(false, "Instantiate lazily", false));

  flags.addFlag("quant-sem-match",
                CLFlag(false, "Attempt to match semantically when instantiating", false));

//   flags.addFlag("quant-const-match",
//                 CLFlag(true, "When matching semantically, only match with constants", false));

  flags.addFlag("quant-complete-inst",
                CLFlag(false, "Try complete instantiation heuristic.  +pp-batch will be automatically enabled"));

  flags.addFlag("quant-max-IL",
                CLFlag(100, "The maximum Instantiation Level allowed"));

  flags.addFlag("quant-inst-lcache",
                CLFlag(true, "Cache instantiations"));

  flags.addFlag("quant-inst-gcache",
                CLFlag(false, "Cache instantiations", false));

  flags.addFlag("quant-inst-tcache",
                CLFlag(false, "Cache instantiations", false));


  flags.addFlag("quant-inst-true",
                CLFlag(true, "Ignore true instantiations"));

  flags.addFlag("quant-pullvar",
                CLFlag(false, "Pull out vars", false));

  flags.addFlag("quant-score",
                CLFlag(true, "Use instantiation level"));

  flags.addFlag("quant-polarity",
                CLFlag(false, "Use polarity ", false));

  flags.addFlag("quant-eqnew",
                CLFlag(true, "Use new equality matching"));

  flags.addFlag("quant-max-score",
                CLFlag(0, "Maximum initial dynamic score"));

  flags.addFlag("quant-trans3",
                CLFlag(true, "Use trans heuristic"));

  flags.addFlag("quant-trans2",
                CLFlag(true, "Use trans2 heuristic"));

  flags.addFlag("quant-naive-num",
                CLFlag(1000, "Maximum number to call naive instantiation"));

  flags.addFlag("quant-naive-inst",
                CLFlag(true, "Use naive instantiation"));

  flags.addFlag("quant-man-trig",
                CLFlag(true, "Use manual triggers"));

  flags.addFlag("quant-gfact",
                CLFlag(false, "Send facts to core directly", false));

  flags.addFlag("quant-glimit",
                CLFlag(1000, "Limit for gfacts", false));

  flags.addFlag("print-var-type", //by yeting, as requested by Sascha Boehme for proofs
                CLFlag(false, "Print types for bound variables"));

  // Bitvectors
  flags.addFlag("bv32-flag",
                CLFlag(false, "assume that all bitvectors are 32bits with no overflow", false));

  // Uninterpreted Functions
  flags.addFlag("trans-closure",
                CLFlag(false,"enables transitive closure of binary relations", false));

  // Datatypes
  flags.addFlag("dt-smartsplits",
                CLFlag(true, "enables smart splitting in datatype theory", false));
  flags.addFlag("dt-lazy",
                CLFlag(false, "lazy splitting on datatypes", false));

  return flags;
}

ValidityChecker* ValidityChecker::create(const CLFlags& flags) {
  return new ValidityChecker(flags);
}

ValidityChecker* ValidityChecker::create() {
  return new ValidityChecker(createFlags());
}

Type ValidityChecker::boolType() {
  return d_em->booleanType();
}

Type ValidityChecker::realType() {
  return d_em->realType();
}

Type ValidityChecker::intType() {
  return d_em->integerType();
}

Type ValidityChecker::subrangeType(const Expr& l, const Expr& r) {
  Unimplemented("Subranges not supported by CVC4 yet (sorry!)");
}

Type ValidityChecker::subtypeType(const Expr& pred, const Expr& witness) {
  Unimplemented("Predicate subtyping not supported by CVC4 yet (sorry!)");
}

Type ValidityChecker::tupleType(const Type& type0, const Type& type1) {
  vector<CVC4::Type> types;
  types.push_back(type0);
  types.push_back(type1);
  return d_em->mkTupleType(types);
}

Type ValidityChecker::tupleType(const Type& type0, const Type& type1, const Type& type2) {
  vector<CVC4::Type> types;
  types.push_back(type0);
  types.push_back(type1);
  types.push_back(type2);
  return d_em->mkTupleType(types);
}

Type ValidityChecker::tupleType(const std::vector<Type>& types) {
  const vector<CVC4::Type>& v =
    *reinterpret_cast<const vector<CVC4::Type>*>(&types);
  return Type(d_em->mkTupleType(v));
}

Type ValidityChecker::recordType(const std::string& field, const Type& type) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Type ValidityChecker::recordType(const std::string& field0, const Type& type0,
                                 const std::string& field1, const Type& type1) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Type ValidityChecker::recordType(const std::string& field0, const Type& type0,
                                 const std::string& field1, const Type& type1,
                                 const std::string& field2, const Type& type2) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Type ValidityChecker::recordType(const std::vector<std::string>& fields,
                                 const std::vector<Type>& types) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Type ValidityChecker::dataType(const std::string& name,
                               const std::string& constructor,
                               const std::vector<std::string>& selectors,
                               const std::vector<Expr>& types) {
  AlwaysAssert(selectors.size() == types.size());
  vector<string> cv;
  vector< vector<string> > sv;
  vector< vector<Expr> > tv;
  cv.push_back(constructor);
  sv.push_back(selectors);
  tv.push_back(types);
  return dataType(name, cv, sv, tv);
}

Type ValidityChecker::dataType(const std::string& name,
                               const std::vector<std::string>& constructors,
                               const std::vector<std::vector<std::string> >& selectors,
                               const std::vector<std::vector<Expr> >& types) {
  AlwaysAssert(constructors.size() == selectors.size());
  AlwaysAssert(constructors.size() == types.size());
  vector<string> nv;
  vector< vector<string> > cv;
  vector< vector< vector<string> > > sv;
  vector< vector< vector<Expr> > > tv;
  nv.push_back(name);
  cv.push_back(constructors);
  sv.push_back(selectors);
  tv.push_back(types);
  vector<Type> dtts;
  dataType(nv, cv, sv, tv, dtts);
  AlwaysAssert(dtts.size() == 1);
  return dtts[0];
}

void ValidityChecker::dataType(const std::vector<std::string>& names,
                               const std::vector<std::vector<std::string> >& constructors,
                               const std::vector<std::vector<std::vector<std::string> > >& selectors,
                               const std::vector<std::vector<std::vector<Expr> > >& types,
                               std::vector<Type>& returnTypes) {

  AlwaysAssert(names.size() == constructors.size());
  AlwaysAssert(names.size() == selectors.size());
  AlwaysAssert(names.size() == types.size());
  vector<CVC4::Datatype> dv;

  // Set up the datatype specifications.
  for(unsigned i = 0; i < names.size(); ++i) {
    CVC4::Datatype dt(names[i]);
    AlwaysAssert(constructors[i].size() == selectors[i].size());
    AlwaysAssert(constructors[i].size() == types[i].size());
    for(unsigned j = 0; j < constructors[i].size(); ++j) {
      CVC4::Datatype::Constructor ctor(constructors[i][j]);
      AlwaysAssert(selectors[i][j].size() == types[i][j].size());
      for(unsigned k = 0; k < selectors[i][j].size(); ++k) {
        if(types[i][j][k].getType().isString()) {
          ctor.addArg(selectors[i][j][k], CVC4::Datatype::UnresolvedType(types[i][j][k].getConst<string>()));
        } else {
          ctor.addArg(selectors[i][j][k], exprToType(types[i][j][k]));
        }
      }
      dt.addConstructor(ctor);
    }
    dv.push_back(dt);
  }

  // Make the datatypes.
  vector<CVC4::DatatypeType> dtts = d_em->mkMutualDatatypeTypes(dv);

  // Post-process to register the names of everything with this validity checker.
  // This is necessary for the compatibility layer because cons/sel operations are
  // constructed without appealing explicitly to the Datatype they belong to.
  for(vector<CVC4::DatatypeType>::iterator i = dtts.begin(); i != dtts.end(); ++i) {
    // For each datatype...
    const CVC4::Datatype& dt = (*i).getDatatype();
    for(CVC4::Datatype::const_iterator j = dt.begin(); j != dt.end(); ++j) {
      // For each constructor, register its name and its selectors names.
      AlwaysAssert(d_constructors.find((*j).getName()) == d_constructors.end(), "cannot have two constructors with the same name in a ValidityChecker");
      d_constructors[(*j).getName()] = &dt;
      for(CVC4::Datatype::Constructor::const_iterator k = (*j).begin(); k != (*j).end(); ++k) {
        AlwaysAssert(d_selectors.find((*k).getName()) == d_selectors.end(), "cannot have two selectors with the same name in a ValidityChecker");
        d_selectors[(*k).getName()] = make_pair(&dt, (*j).getName());
      }
    }
  }

  // Copy into the output buffer.
  returnTypes.clear();
  copy(dtts.begin(), dtts.end(), back_inserter(returnTypes));
}

Type ValidityChecker::arrayType(const Type& typeIndex, const Type& typeData) {
  return d_em->mkArrayType(typeIndex, typeData);
}

Type ValidityChecker::bitvecType(int n) {
  CheckArgument(n >= 0, n, "cannot construct a bitvector type of negative size");
  return d_em->mkBitVectorType(n);
}

Type ValidityChecker::funType(const Type& typeDom, const Type& typeRan) {
  return d_em->mkFunctionType(typeDom, typeRan);
}

Type ValidityChecker::funType(const std::vector<Type>& typeDom, const Type& typeRan) {
  const vector<CVC4::Type>& dom =
    *reinterpret_cast<const vector<CVC4::Type>*>(&typeDom);
  return Type(d_em->mkFunctionType(dom, typeRan));
}

Type ValidityChecker::createType(const std::string& typeName) {
  return d_em->mkSort(typeName);
}

Type ValidityChecker::createType(const std::string& typeName, const Type& def) {
  d_parserContext->defineType(typeName, def);
}

Type ValidityChecker::lookupType(const std::string& typeName) {
  return d_parserContext->getSort(typeName);
}

ExprManager* ValidityChecker::getEM() {
  return d_em;
}

Expr ValidityChecker::varExpr(const std::string& name, const Type& type) {
  return d_parserContext->mkVar(name, type);
}

Expr ValidityChecker::varExpr(const std::string& name, const Type& type,
                              const Expr& def) {
  FatalAssert(def.getType() == type, "expected types to match");
  d_parserContext->defineVar(name, def);
}

Expr ValidityChecker::lookupVar(const std::string& name, Type* type) {
  return d_parserContext->getVariable(name);
}

Type ValidityChecker::getType(const Expr& e) {
  return d_em->getType(e);
}

Type ValidityChecker::getBaseType(const Expr& e) {
  Type t = d_em->getType(e);
  return t.isInteger() ? Type(d_em->realType()) : t;
}

Type ValidityChecker::getBaseType(const Type& t) {
  return t.isInteger() ? Type(d_em->realType()) : t;
}

Expr ValidityChecker::getTypePred(const Type&t, const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::stringExpr(const std::string& str) {
  return d_em->mkConst(str);
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
  printExpr(e, Message());
}

void ValidityChecker::printExpr(const Expr& e, std::ostream& os) {
  Expr::setdepth::Scope sd(os, -1);
  Expr::printtypes::Scope pt(os, false);
  Expr::setlanguage::Scope sl(os, d_em->getOptions()[CVC4::outputLanguage]);
  os << e;
}

Expr ValidityChecker::parseExpr(const Expr& e) {
  return e;
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
  std::stringstream ss(s, std::stringstream::in);
  return loadFile(ss, lang, false);
}

Expr ValidityChecker::exprFromString(const std::string& s, InputLanguage lang) {
  std::stringstream ss;

  if( lang != PRESENTATION_LANG && lang != SMTLIB_V2_LANG ) {
    ss << lang;
    throw Exception("Unsupported language in exprFromString: " + ss.str());
  }

  CVC4::parser::Parser* p = CVC4::parser::ParserBuilder(d_em, "<internal>").withStringInput(s).withInputLanguage(lang).build();
  p->useDeclarationsFrom(d_parserContext);
  Expr e = p->nextExpression();
  if( e.isNull() ) {
    throw CVC4::parser::ParserException("Parser result is null: '" + s + "'");
  }

  delete p;

  return e;
}

Expr ValidityChecker::trueExpr() {
  return d_em->mkConst(true);
}

Expr ValidityChecker::falseExpr() {
  return d_em->mkConst(false);
}

Expr ValidityChecker::notExpr(const Expr& child) {
  return d_em->mkExpr(CVC4::kind::NOT, child);
}

Expr ValidityChecker::andExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::AND, left, right);
}

Expr ValidityChecker::andExpr(const std::vector<Expr>& children) {
  const vector<CVC4::Expr>& v =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&children);
  return d_em->mkExpr(CVC4::kind::AND, v);
}

Expr ValidityChecker::orExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::OR, left, right);
}

Expr ValidityChecker::orExpr(const std::vector<Expr>& children) {
  const vector<CVC4::Expr>& v =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&children);
  return d_em->mkExpr(CVC4::kind::OR, v);
}

Expr ValidityChecker::impliesExpr(const Expr& hyp, const Expr& conc) {
  return d_em->mkExpr(CVC4::kind::IMPLIES, hyp, conc);
}

Expr ValidityChecker::iffExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::IFF, left, right);
}

Expr ValidityChecker::eqExpr(const Expr& child0, const Expr& child1) {
  return d_em->mkExpr(CVC4::kind::EQUAL, child0, child1);
}

Expr ValidityChecker::iteExpr(const Expr& ifpart, const Expr& thenpart,
                              const Expr& elsepart) {
  return d_em->mkExpr(CVC4::kind::ITE, ifpart, thenpart, elsepart);
}

Expr ValidityChecker::distinctExpr(const std::vector<Expr>& children) {
  const vector<CVC4::Expr>& v =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&children);
  return d_em->mkExpr(CVC4::kind::DISTINCT, v);
}

Op ValidityChecker::createOp(const std::string& name, const Type& type) {
  return d_parserContext->mkVar(name, type);
}

Op ValidityChecker::createOp(const std::string& name, const Type& type,
                             const Expr& def) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Op ValidityChecker::lookupOp(const std::string& name, Type* type) {
  Op op = d_parserContext->getFunction(name);
  *type = op.getType();
  return op;
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& child) {
  return d_em->mkExpr(CVC4::kind::APPLY_UF, op, child);
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::APPLY_UF, op, left, right);
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& child0,
                              const Expr& child1, const Expr& child2) {
  return d_em->mkExpr(CVC4::kind::APPLY_UF, op, child0, child1, child2);
}

Expr ValidityChecker::funExpr(const Op& op, const std::vector<Expr>& children) {
  vector<CVC4::Expr> opkids;
  opkids.push_back(op);
  opkids.insert(opkids.end(), children.begin(), children.end());
  return d_em->mkExpr(CVC4::kind::APPLY_UF, opkids);
}

bool ValidityChecker::addPairToArithOrder(const Expr& smaller, const Expr& bigger) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::ratExpr(int n, int d) {
  return d_em->mkConst(Rational(n, d));
}

Expr ValidityChecker::ratExpr(const std::string& n, const std::string& d, int base) {
  return d_em->mkConst(Rational(n + '/' + d, base));
}

Expr ValidityChecker::ratExpr(const std::string& n, int base) {
  return d_em->mkConst(Rational(n, base));
}

Expr ValidityChecker::uminusExpr(const Expr& child) {
  return d_em->mkExpr(CVC4::kind::UMINUS, child);
}

Expr ValidityChecker::plusExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::PLUS, left, right);
}

Expr ValidityChecker::plusExpr(const std::vector<Expr>& children) {
  const vector<CVC4::Expr>& v =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&children);
  return d_em->mkExpr(CVC4::kind::PLUS, v);
}

Expr ValidityChecker::minusExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::MINUS, left, right);
}

Expr ValidityChecker::multExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::MULT, left, right);
}

Expr ValidityChecker::powExpr(const Expr& x, const Expr& n) {
  return d_em->mkExpr(CVC4::kind::POW, x, n);
}

Expr ValidityChecker::divideExpr(const Expr& numerator,
                                 const Expr& denominator) {
  return d_em->mkExpr(CVC4::kind::DIVISION, numerator, denominator);
}

Expr ValidityChecker::ltExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::LT, left, right);
}

Expr ValidityChecker::leExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::LEQ, left, right);
}

Expr ValidityChecker::gtExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::GT, left, right);
}

Expr ValidityChecker::geExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::GEQ, left, right);
}

Expr ValidityChecker::recordExpr(const std::string& field, const Expr& expr) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::recordExpr(const std::string& field0, const Expr& expr0,
                                 const std::string& field1, const Expr& expr1) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::recordExpr(const std::string& field0, const Expr& expr0,
                                 const std::string& field1, const Expr& expr1,
                                 const std::string& field2, const Expr& expr2) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::recordExpr(const std::vector<std::string>& fields,
                                 const std::vector<Expr>& exprs) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::recSelectExpr(const Expr& record, const std::string& field) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::recUpdateExpr(const Expr& record, const std::string& field,
                                    const Expr& newValue) {
  Unimplemented("Records not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::readExpr(const Expr& array, const Expr& index) {
  return d_em->mkExpr(CVC4::kind::SELECT, array, index);
}

Expr ValidityChecker::writeExpr(const Expr& array, const Expr& index,
                                const Expr& newValue) {
  return d_em->mkExpr(CVC4::kind::STORE, array, index, newValue);
}

Expr ValidityChecker::newBVConstExpr(const std::string& s, int base) {
  return d_em->mkConst(CVC4::BitVector(s, base));
}

Expr ValidityChecker::newBVConstExpr(const std::vector<bool>& bits) {
  Integer value = 0;
  for(vector<bool>::const_iterator i = bits.begin(); i != bits.end(); ++i) {
    value *= 2;
    value += *i ? 1 : 0;
  }
  return d_em->mkConst(CVC4::BitVector(bits.size(), value));
}

Expr ValidityChecker::newBVConstExpr(const Rational& r, int len) {
  // implementation based on CVC3's TheoryBitvector::newBVConstExpr()

  CheckArgument(r.getDenominator() == 1, r, "ValidityChecker::newBVConstExpr: "
                "not an integer: `%s'", r.toString().c_str());
  CheckArgument(len > 0, len, "ValidityChecker::newBVConstExpr: "
                "len = %d", len);

  string s(r.toString(2));
  size_t strsize = s.size();
  size_t length = len;
  Expr res;
  if(length > 0 && length != strsize) {
    //either (length > strsize) or (length < strsize)
    if(length < strsize) {
      s = s.substr(strsize - length, length);
    } else {
      string zeros("");
      for(size_t i = 0, pad = length - strsize; i < pad; ++i)
	zeros += "0";
      s = zeros + s;
    }
  }

  return newBVConstExpr(s, 2);
}

Expr ValidityChecker::newConcatExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only concat a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only concat a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_CONCAT, t1, t2);
}

Expr ValidityChecker::newConcatExpr(const std::vector<Expr>& kids) {
  const vector<CVC4::Expr>& v =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&kids);
  return d_em->mkExpr(CVC4::kind::BITVECTOR_CONCAT, v);
}

Expr ValidityChecker::newBVExtractExpr(const Expr& e, int hi, int low) {
  CheckArgument(e.getType().isBitVector(), e, "can only bvextract from a bitvector, not a `%s'", e.getType().toString().c_str());
  CheckArgument(hi >= low, hi, "extraction [%d:%d] is bad; possibly inverted?", hi, low);
  CheckArgument(low >= 0, low, "extraction [%d:%d] is bad (negative)", hi, low);
  CheckArgument(CVC4::BitVectorType(e.getType()).getSize() > unsigned(hi), hi, "bitvector is of size %u, extraction [%d:%d] is off-the-end", CVC4::BitVectorType(e.getType()).getSize(), hi, low);
  return d_em->mkExpr(CVC4::kind::BITVECTOR_EXTRACT,
                     d_em->mkConst(CVC4::BitVectorExtract(hi, low)), e);
}

Expr ValidityChecker::newBVNegExpr(const Expr& t1) {
  // CVC3's BVNEG => SMT-LIBv2 bvnot
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvneg a bitvector, not a `%s'", t1.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_NOT, t1);
}

Expr ValidityChecker::newBVAndExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvand a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvand a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_AND, t1, t2);
}

Expr ValidityChecker::newBVAndExpr(const std::vector<Expr>& kids) {
  // BVAND is not N-ary
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVOrExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvor a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvor a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_OR, t1, t2);
}

Expr ValidityChecker::newBVOrExpr(const std::vector<Expr>& kids) {
  // BVOR is not N-ary
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVXorExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvxor a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvxor a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_XOR, t1, t2);
}

Expr ValidityChecker::newBVXorExpr(const std::vector<Expr>& kids) {
  // BVXOR is not N-ary
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVXnorExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvxnor a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvxnor a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_XNOR, t1, t2);
}

Expr ValidityChecker::newBVXnorExpr(const std::vector<Expr>& kids) {
  // BVXNOR is not N-ary
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVNandExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvnand a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvnand a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_NAND, t1, t2);
}

Expr ValidityChecker::newBVNorExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvnor a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvnor a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_NOR, t1, t2);
}

Expr ValidityChecker::newBVCompExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvcomp a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvcomp a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_COMP, t1, t2);
}

Expr ValidityChecker::newBVLTExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvlt a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvlt a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_ULT, t1, t2);
}

Expr ValidityChecker::newBVLEExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvle a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvle a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_ULE, t1, t2);
}

Expr ValidityChecker::newBVSLTExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvslt a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvslt a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SLT, t1, t2);
}

Expr ValidityChecker::newBVSLEExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvsle a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvsle a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SLE, t1, t2);
}

Expr ValidityChecker::newSXExpr(const Expr& t1, int len) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only sx a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(len >= 0, len, "must sx by a positive integer");
  CheckArgument(unsigned(len) >= CVC4::BitVectorType(t1.getType()).getSize(), len, "cannot sx by something smaller than the bitvector (%d < %u)", len, CVC4::BitVectorType(t1.getType()).getSize());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SIGN_EXTEND,
                     d_em->mkConst(CVC4::BitVectorSignExtend(len)), t1);
}

Expr ValidityChecker::newBVUminusExpr(const Expr& t1) {
  // CVC3's BVUMINUS => SMT-LIBv2 bvneg
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvuminus a bitvector, not a `%s'", t1.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_NEG, t1);
}

Expr ValidityChecker::newBVSubExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvsub a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvsub by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SUB, t1, t2);
}

Expr ValidityChecker::newBVPlusExpr(int numbits, const std::vector<Expr>& k) {
  // BVPLUS is not N-ary
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::newBVPlusExpr(int numbits, const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvplus a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvplus a bitvector, not a `%s'", t2.getType().toString().c_str());
  Expr e = d_em->mkExpr(CVC4::kind::BITVECTOR_PLUS, t1, t2);
  unsigned size = CVC4::BitVectorType(e.getType()).getSize();
  CheckArgument(numbits > 0, numbits,
                "argument must be positive integer, not %u", numbits);
  CheckArgument(unsigned(numbits) == size, numbits,
                "argument must match computed size of bitvector sum: "
                "passed size == %u, computed size == %u", numbits, size);
  return e;
}

Expr ValidityChecker::newBVMultExpr(int numbits, const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvmult a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvmult by a bitvector, not a `%s'", t2.getType().toString().c_str());
  Expr e = d_em->mkExpr(CVC4::kind::BITVECTOR_MULT, t1, t2);
  unsigned size = CVC4::BitVectorType(e.getType()).getSize();
  CheckArgument(numbits > 0, numbits,
                "argument must be positive integer, not %u", numbits);
  CheckArgument(unsigned(numbits) == size, numbits,
                "argument must match computed size of bitvector product: "
                "passed size == %u, computed size == %u", numbits, size);
  return e;
}

Expr ValidityChecker::newBVUDivExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvudiv a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvudiv by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_UDIV, t1, t2);
}

Expr ValidityChecker::newBVURemExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvurem a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvurem by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_UREM, t1, t2);
}

Expr ValidityChecker::newBVSDivExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvsdiv a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvsdiv by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SDIV, t1, t2);
}

Expr ValidityChecker::newBVSRemExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvsrem a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvsrem by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SREM, t1, t2);
}

Expr ValidityChecker::newBVSModExpr(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only bvsmod a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only bvsmod by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SMOD, t1, t2);
}

Expr ValidityChecker::newFixedLeftShiftExpr(const Expr& t1, int r) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only left-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(r >= 0, r, "left shift amount must be >= 0 (you passed %d)", r);
  // Defined in:
  // http://www.cs.nyu.edu/acsys/cvc3/doc/user_doc.html#user_doc_pres_lang_expr_bit
  return d_em->mkExpr(CVC4::kind::BITVECTOR_CONCAT, t1, d_em->mkConst(CVC4::BitVector(r)));
}

Expr ValidityChecker::newFixedConstWidthLeftShiftExpr(const Expr& t1, int r) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(r >= 0, r, "const-width left shift amount must be >= 0 (you passed %d)", r);
  // just turn it into a BVSHL
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SHL, t1, d_em->mkConst(CVC4::BitVector(CVC4::BitVectorType(t1.getType()).getSize(), unsigned(r))));
}

Expr ValidityChecker::newFixedRightShiftExpr(const Expr& t1, int r) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(r >= 0, r, "right shift amount must be >= 0 (you passed %d)", r);
  // Defined in:
  // http://www.cs.nyu.edu/acsys/cvc3/doc/user_doc.html#user_doc_pres_lang_expr_bit
  // Should be equivalent to a BVLSHR; just turn it into that.
  return d_em->mkExpr(CVC4::kind::BITVECTOR_LSHR, t1, d_em->mkConst(CVC4::BitVector(CVC4::BitVectorType(t1.getType()).getSize(), unsigned(r))));
}

Expr ValidityChecker::newBVSHL(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only right-shift by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SHL, t1, t2);
}

Expr ValidityChecker::newBVLSHR(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only right-shift by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_LSHR, t1, t2);
}

Expr ValidityChecker::newBVASHR(const Expr& t1, const Expr& t2) {
  CheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CheckArgument(t2.getType().isBitVector(), t2, "can only right-shift by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_ASHR, t1, t2);
}

Rational ValidityChecker::computeBVConst(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::tupleExpr(const std::vector<Expr>& exprs) {
  const vector<CVC4::Expr>& v =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&exprs);
  return d_em->mkExpr(CVC4::kind::TUPLE, v);
}

Expr ValidityChecker::tupleSelectExpr(const Expr& tuple, int index) {
  Unimplemented("Tuples not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::tupleUpdateExpr(const Expr& tuple, int index,
                                      const Expr& newValue) {
  Unimplemented("Tuples not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::datatypeConsExpr(const std::string& constructor, const std::vector<Expr>& args) {
  ConstructorMap::const_iterator i = d_constructors.find(constructor);
  AlwaysAssert(i != d_constructors.end(), "no such constructor");
  const CVC4::Datatype& dt = *(*i).second;
  const CVC4::Datatype::Constructor& ctor = dt[constructor];
  AlwaysAssert(ctor.getNumArgs() == args.size(), "arity mismatch in constructor application");
  return d_em->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, ctor.getConstructor(), vector<CVC4::Expr>(args.begin(), args.end()));
}

Expr ValidityChecker::datatypeSelExpr(const std::string& selector, const Expr& arg) {
  SelectorMap::const_iterator i = d_selectors.find(selector);
  AlwaysAssert(i != d_selectors.end(), "no such selector");
  const CVC4::Datatype& dt = *(*i).second.first;
  string constructor = (*i).second.second;
  const CVC4::Datatype::Constructor& ctor = dt[constructor];
  return d_em->mkExpr(CVC4::kind::APPLY_SELECTOR, ctor.getSelector(selector), arg);
}

Expr ValidityChecker::datatypeTestExpr(const std::string& constructor, const Expr& arg) {
  ConstructorMap::const_iterator i = d_constructors.find(constructor);
  AlwaysAssert(i != d_constructors.end(), "no such constructor");
  const CVC4::Datatype& dt = *(*i).second;
  const CVC4::Datatype::Constructor& ctor = dt[constructor];
  return d_em->mkExpr(CVC4::kind::APPLY_TESTER, ctor.getTester(), arg);
}

Expr ValidityChecker::boundVarExpr(const std::string& name, const std::string& uid,
                                   const Type& type) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const Expr& trigger) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const std::vector<Expr>& triggers) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const std::vector<std::vector<Expr> >& triggers) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

void ValidityChecker::setTriggers(const Expr& e, const std::vector<std::vector<Expr> > & triggers) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

void ValidityChecker::setTriggers(const Expr& e, const std::vector<Expr>& triggers) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

void ValidityChecker::setTrigger(const Expr& e, const Expr& trigger) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

void ValidityChecker::setMultiTrigger(const Expr& e, const std::vector<Expr>& multiTrigger) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

Expr ValidityChecker::existsExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented("Quantifiers not supported by CVC4 yet (sorry!)");
}

Op ValidityChecker::lambdaExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented("Lambda expressions not supported by CVC4 yet (sorry!)");
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
  d_smt->assertFormula(CVC4::BoolExpr(e));
}

void ValidityChecker::registerAtom(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getImpliedLiteral() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::simplify(const Expr& e) {
  return d_smt->simplify(e);
}

static QueryResult cvc4resultToCvc3result(CVC4::Result r) {
  switch(r.isSat()) {
  case CVC4::Result::SAT:
    return SATISFIABLE;
  case CVC4::Result::UNSAT:
    return UNSATISFIABLE;
  default:
    ;
  }

  switch(r.isValid()) {
  case CVC4::Result::VALID:
    return VALID;
  case CVC4::Result::INVALID:
    return INVALID;
  default:
    return UNKNOWN;
  }
}

QueryResult ValidityChecker::query(const Expr& e) {
  return cvc4resultToCvc3result(d_smt->query(CVC4::BoolExpr(e)));
}

QueryResult ValidityChecker::checkUnsat(const Expr& e) {
  return cvc4resultToCvc3result(d_smt->checkSat(CVC4::BoolExpr(e)));
}

QueryResult ValidityChecker::checkContinue() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::restart(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::returnFromCheck() {
  // CVC4 has this behavior by default
}

void ValidityChecker::getUserAssumptions(std::vector<Expr>& assumptions) {
  CheckArgument(assumptions.empty(), assumptions, "assumptions arg must be empty");
  vector<CVC4::Expr> v = d_smt->getAssertions();
  assumptions.swap(*reinterpret_cast<vector<Expr>*>(&v));
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

void ValidityChecker::getConcreteModel(ExprMap<Expr>& m) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::tryModelGeneration() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

FormulaValue ValidityChecker::value(const Expr& e) {
  CheckArgument(e.getType() == d_em->booleanType(), e, "argument must be a formula");
  return d_smt->getValue(e).getConst<bool>() ? TRUE_VAL : FALSE_VAL;
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
  return d_smt->getStackLevel();
}

void ValidityChecker::push() {
  d_smt->push();
}

void ValidityChecker::pop() {
  d_smt->pop();
}

void ValidityChecker::popto(int stackLevel) {
  CheckArgument(stackLevel >= 0, stackLevel,
                "Cannot pop to a negative stack level %u", stackLevel);
  CheckArgument(unsigned(stackLevel) <= d_smt->getStackLevel(), stackLevel,
                "Cannot pop to a level higher than the current one!  "
                "At level %u, user requested level %d",
                d_smt->getStackLevel(), stackLevel);
  while(unsigned(stackLevel) < d_smt->getStackLevel()) {
    pop();
  }
}

int ValidityChecker::scopeLevel() {
  return d_parserContext->getDeclarationLevel();
}

void ValidityChecker::pushScope() {
  d_parserContext->pushScope();
}

void ValidityChecker::popScope() {
  d_parserContext->popScope();
}

void ValidityChecker::poptoScope(int scopeLevel) {
  CheckArgument(scopeLevel >= 0, scopeLevel,
                "Cannot pop to a negative scope level %u", scopeLevel);
  CheckArgument(unsigned(scopeLevel) <= d_parserContext->getDeclarationLevel(),
                scopeLevel,
                "Cannot pop to a scope level higher than the current one!  "
                "At scope level %u, user requested scope level %d",
                d_parserContext->getDeclarationLevel(), scopeLevel);
  CheckArgument(scopeLevel <= d_parserContext->getDeclarationLevel(),
                scopeLevel,
                "Cannot pop to a higher scope level");
  while(unsigned(scopeLevel) < d_parserContext->getDeclarationLevel()) {
    popScope();
  }
}

Context* ValidityChecker::getCurrentContext() {
  Unimplemented("Contexts are not part of the public interface of CVC4");
}

void ValidityChecker::reset() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::logAnnotation(const Expr& annot) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

static void doCommands(CVC4::parser::Parser* parser, CVC4::SmtEngine* smt, CVC4::OptionsClass& opts) {
  while(CVC4::Command* cmd = parser->nextCommand()) {
    if(opts[CVC4::verbosity] >= 0) {
      cmd->invoke(smt, *opts[CVC4::out]);
    } else {
      cmd->invoke(smt);
    }
    delete cmd;
  }
}

void ValidityChecker::loadFile(const std::string& fileName,
                               InputLanguage lang,
                               bool interactive,
                               bool calledFromParser) {
  CVC4::OptionsClass opts = d_em->getOptions();
  //d_smt->setOption("input-language", lang);
  d_smt->setOption("interactive-mode", string(interactive ? "true" : "false"));
  //opts[CVC4::interactiveSetByUser] = true;
  CVC4::parser::ParserBuilder parserBuilder(d_em, fileName, opts);
  CVC4::parser::Parser* p = parserBuilder.build();
  p->useDeclarationsFrom(d_parserContext);
  doCommands(p, d_smt, opts);
  delete p;
}

void ValidityChecker::loadFile(std::istream& is,
                               InputLanguage lang,
                               bool interactive) {
  CVC4::OptionsClass opts = d_em->getOptions();
  //d_smt->setOption("input-language", lang);
  d_smt->setOption("interactive-mode", string(interactive ? "true" : "false"));
  //opts[CVC4::interactiveSetByUser] = true;
  CVC4::parser::ParserBuilder parserBuilder(d_em, "[stream]", opts);
  CVC4::parser::Parser* p = parserBuilder.withStreamInput(is).build();
  d_parserContext = p;
  p->useDeclarationsFrom(d_parserContext);
  doCommands(p, d_smt, opts);
  delete p;
}

Statistics& ValidityChecker::getStatistics() {
  return *d_smt->getStatisticsRegistry();
}

void ValidityChecker::printStatistics() {
  Message() << d_smt->getStatisticsRegistry();
}

int compare(const Expr& e1, const Expr& e2) {
  // Quick equality check (operator== is implemented independently
  // and more efficiently)
  if(e1 == e2) return 0;

  if(e1.isNull()) return -1;
  if(e2.isNull()) return 1;

  // Both are non-Null.  Check for constant
  bool e1c = e1.isConstant();
  if (e1c != e2.isConstant()) {
    return e1c ? -1 : 1;
  }

  // Compare the indices
  return (e1.getIndex() < e2.getIndex())? -1 : 1;
}

}/* CVC3 namespace */

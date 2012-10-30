/*********************                                                        */
/*! \file sexpr.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simple representation of S-expressions
 **
 ** Simple representation of S-expressions.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SEXPR_H
#define __CVC4__SEXPR_H

#include <vector>
#include <string>
#include <iomanip>
#include <sstream>

#include "util/integer.h"
#include "util/rational.h"
#include "util/exception.h"

namespace CVC4 {

/**
 * A simple S-expression. An S-expression is either an atom with a
 * string value, or a list of other S-expressions.
 */
class CVC4_PUBLIC SExpr {

  enum SExprTypes {
    SEXPR_STRING,
    SEXPR_KEYWORD,
    SEXPR_INTEGER,
    SEXPR_RATIONAL,
    SEXPR_NOT_ATOM
  } d_sexprType;

  /** The value of an atomic integer-valued S-expression. */
  CVC4::Integer d_integerValue;

  /** The value of an atomic rational-valued S-expression. */
  CVC4::Rational d_rationalValue;

  /** The value of an atomic S-expression. */
  std::string d_stringValue;

  /** The children of a list S-expression. */
  std::vector<SExpr> d_children;

public:

  class CVC4_PUBLIC Keyword : protected std::string {
  public:
    Keyword(const std::string& s) : std::string(s) {}
    const std::string& getString() const { return *this; }
  };/* class SExpr::Keyword */

  SExpr() :
    d_sexprType(SEXPR_STRING),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  SExpr(const CVC4::Integer& value) :
    d_sexprType(SEXPR_INTEGER),
    d_integerValue(value),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  SExpr(const CVC4::Rational& value) :
    d_sexprType(SEXPR_RATIONAL),
    d_integerValue(0),
    d_rationalValue(value),
    d_stringValue(""),
    d_children() {
  }

  SExpr(const std::string& value) :
    d_sexprType(SEXPR_STRING),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(value),
    d_children() {
  }

  SExpr(const Keyword& value) :
    d_sexprType(SEXPR_KEYWORD),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(value.getString()),
    d_children() {
  }

  SExpr(const std::vector<SExpr>& children) :
    d_sexprType(SEXPR_NOT_ATOM),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(""),
    d_children(children) {
  }

  /** Is this S-expression an atom? */
  bool isAtom() const;

  /** Is this S-expression an integer? */
  bool isInteger() const;

  /** Is this S-expression a rational? */
  bool isRational() const;

  /** Is this S-expression a string? */
  bool isString() const;

  /** Is this S-expression a keyword? */
  bool isKeyword() const;

  /**
   * Get the string value of this S-expression. This will cause an
   * error if this S-expression is not an atom.
   */
  std::string getValue() const;

  /**
   * Get the integer value of this S-expression. This will cause an
   * error if this S-expression is not an integer.
   */
  const CVC4::Integer& getIntegerValue() const;

  /**
   * Get the rational value of this S-expression. This will cause an
   * error if this S-expression is not a rational.
   */
  const CVC4::Rational& getRationalValue() const;

  /**
   * Get the children of this S-expression. This will cause an error
   * if this S-expression is not a list.
   */
  const std::vector<SExpr>& getChildren() const;

  /** Is this S-expression equal to another? */
  bool operator==(const SExpr& s) const;

  /** Is this S-expression different from another? */
  bool operator!=(const SExpr& s) const;

};/* class SExpr */

inline bool SExpr::isAtom() const {
  return d_sexprType != SEXPR_NOT_ATOM;
}

inline bool SExpr::isInteger() const {
  return d_sexprType == SEXPR_INTEGER;
}

inline bool SExpr::isRational() const {
  return d_sexprType == SEXPR_RATIONAL;
}

inline bool SExpr::isString() const {
  return d_sexprType == SEXPR_STRING;
}

inline bool SExpr::isKeyword() const {
  return d_sexprType == SEXPR_KEYWORD;
}

inline std::string SExpr::getValue() const {
  CheckArgument( isAtom(), this );
  switch(d_sexprType) {
  case SEXPR_INTEGER:
    return d_integerValue.toString();
  case SEXPR_RATIONAL: {
    // We choose to represent rationals as decimal strings rather than
    // "numerator/denominator."  Perhaps an additional SEXPR_DECIMAL
    // could be added if we need both styles, even if it's backed by
    // the same Rational object.
    std::stringstream ss;
    ss << std::fixed << d_rationalValue.getDouble();
    return ss.str();
  }
  case SEXPR_STRING:
  case SEXPR_KEYWORD:
    return d_stringValue;
  case SEXPR_NOT_ATOM:
    return std::string();
  }
  return std::string();
}

inline const CVC4::Integer& SExpr::getIntegerValue() const {
  CheckArgument( isInteger(), this );
  return d_integerValue;
}

inline const CVC4::Rational& SExpr::getRationalValue() const {
  CheckArgument( isRational(), this );
  return d_rationalValue;
}

inline const std::vector<SExpr>& SExpr::getChildren() const {
  CheckArgument( !isAtom(), this );
  return d_children;
}

inline bool SExpr::operator==(const SExpr& s) const {
  return d_sexprType == s.d_sexprType &&
         d_integerValue == s.d_integerValue &&
         d_rationalValue == s.d_rationalValue &&
         d_stringValue == s.d_stringValue &&
         d_children == s.d_children;
}

inline bool SExpr::operator!=(const SExpr& s) const {
  return !(*this == s);
}

std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__SEXPR_H */

/*********************                                                        */
/*! \file rational.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Multi-precision rational constants.
 **
 ** Multi-precision rational constants.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__RATIONAL_H
#define __CVC4__RATIONAL_H

#include <gmp.h>
#include <string>
#include "util/integer.h"

namespace CVC4 {

/**
 ** A multi-precision rational constant.
 ** This stores the rational as a pair of multi-precision integers,
 ** one for the numerator and one for the denominator.
 ** The number is always stored so that the gcd of the numerator and denominator
 ** is 1.  (This is referred to as referred to as canonical form in GMP's
 ** literature.) A consequence is that that the numerator and denominator may be
 ** different than the values used to construct the Rational.
 **
 ** NOTE: The correct way to create a Rational from an int is to use one of the
 ** int numerator/int denominator constructors with the denominator 1.  Trying
 ** to construct a Rational with a single int, e.g., Rational(0), will put you
 ** in danger of invoking the char* constructor, from whence you will segfault.
 **/


class CVC4_PUBLIC Rational {
private:


  /**
   * Stores the value of the rational is stored in a C++ GMP rational class.
   * Using this instead of mpq_t allows for easier destruction.
   */
  mpq_t d_value;

  /**
   * Constructs a Rational from a mpq_class object.
   * Does a deep copy.
   * Assumes that the value is in canonical form, and thus does not
   * have to call canonicalize() on the value.
   */
  Rational(mpq_t val){
    mpq_set(d_value, val);
  }

public:

  /** Creates a rational from a decimal string (e.g., <code>"1.5"</code>).
   *
   * @param dec a string encoding a decimal number in the format
   * <code>[0-9]*\.[0-9]*</code>
   */
  static Rational fromDecimal(const std::string& dec);

  /** Constructs a rational with the value 0/1. */
  Rational(){
    mpq_init(d_value);
  }

  /**
   * Constructs a Rational from a stl string in a given base (defaults to 10).
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  Rational(const std::string& s, unsigned base = 10){
    mpq_init(d_value);
    int suc = mpq_set_str(d_value, s.c_str(), base);
    if(suc == -1)
      throw std::invalid_argument("mpq_set_str failed");
    mpq_canonicalize(d_value);
  }

  /**
   * Creates a Rational from another Rational, q, by performing a deep copy.
   */
  Rational(const Rational& q){
    mpq_init(d_value);
    mpq_set(d_value,q.d_value);
    mpq_canonicalize(d_value);
  }

  /**
   * Constructs a canonical Rational from a numerator.
   */
  Rational(signed long int n){
    mpq_init(d_value);
    mpq_set_si(d_value, n,1);
    mpq_canonicalize(d_value);
  }
  Rational(unsigned long int n){
    mpq_init(d_value);
    mpq_set_ui(d_value, n,1);
    mpq_canonicalize(d_value);
  }

  /**
   * Constructs a canonical Rational from a numerator and denominator.
   */
  Rational(signed int n, unsigned int d){
    mpq_init(d_value);
    mpq_set_si(d_value,(signed long int)n, (signed long int)d);
    mpq_canonicalize(d_value);
  }
  Rational(unsigned int n, unsigned int d){
    mpq_init(d_value);
    mpq_set_ui(d_value,(unsigned long int)n,(unsigned long int)d);
    mpq_canonicalize(d_value);
  }
  
  Rational(signed long int n, unsigned long int d){
    mpq_init(d_value);
    mpq_set_si(d_value,n,d);
    mpq_canonicalize(d_value);
  }
  Rational(unsigned long int n, unsigned long int d){
    mpq_init(d_value);
    mpq_set_ui(d_value, n,d);
    mpq_canonicalize(d_value);
  }

  Rational(const Integer& n, const Integer& d){
    mpq_init(d_value);
    Integer::set(mpq_numref(d_value),n);
    Integer::set(mpq_denref(d_value),d);
    mpq_canonicalize(d_value);
  }
  Rational(const Integer& n){
    mpq_init(d_value);
    Integer::set(mpq_numref(d_value),n);
    mpq_canonicalize(d_value);
  }
  ~Rational() {
    mpq_clear(d_value);
  }


  /**
   * Returns the value of numerator of the Rational.
   * Note that this makes a deep copy of the numerator.
   */
  Integer getNumerator() const {
    return Integer(mpq_numref(d_value));
  }

  /**
   * Returns the value of denominator of the Rational.
   * Note that this makes a deep copy of the denominator.
   */
  Integer getDenominator() const{
    return Integer(mpq_denref(d_value));
  }

  Rational inverse() const {
    Rational ret;
    mpq_inv(ret.d_value,d_value);
    return ret;
  }

  static int cmp(const Rational& x, const Rational& y) {
    return mpq_cmp(x.d_value, y.d_value);
  }


  int sgn() {
    return mpq_sgn(d_value);
  }

  Rational& operator=(const Rational& x){
    if(this == &x) return *this;
    mpq_set(d_value,x.d_value);
    return *this;
  }

  Rational operator-() const{
    Rational ret;
    mpq_neg(ret.d_value, d_value);
    return ret;
  }

  bool operator==(const Rational& y) const {
    return mpq_equal(d_value, y.d_value) != 0;
  }

  bool operator!=(const Rational& y) const {
    return mpq_equal(d_value, y.d_value) == 0;
  }

  bool operator< (const Rational& y) const {
    return Rational::cmp(*this, y) < 0;
  }

  bool operator<=(const Rational& y) const {
    return Rational::cmp(*this, y) <= 0;
  }

  bool operator> (const Rational& y) const {
    return Rational::cmp(*this, y) > 0;
  }

  bool operator>=(const Rational& y) const {
    return Rational::cmp(*this, y) >= 0;
  }

  Rational operator+(const Rational& y) const{
    Rational ret;
    mpq_add(ret.d_value, d_value, y.d_value);
    return ret;
  }
  Rational operator-(const Rational& y) const {
    Rational ret;
    mpq_sub(ret.d_value, d_value, y.d_value);
    return ret;
  }

  Rational operator*(const Rational& y) const {
    Rational ret;
    mpq_mul(ret.d_value, d_value, y.d_value);
    return ret;
  }
  Rational operator/(const Rational& y) const {
    Rational ret;
    mpq_div(ret.d_value, d_value, y.d_value);
    return ret;
  }

  Rational& operator+=(const Rational& y){
    mpq_add(d_value, d_value, y.d_value);
    return (*this);
  }

  Rational& operator*=(const Rational& y){
    mpq_mul(d_value, d_value, y.d_value);
    return (*this);
  }

  /** Returns a string representing the rational in the given base. */
  std::string toString(int base = 10) const {
    return std::string(mpq_get_str(NULL, base, d_value));
  }

  /**
   * Computes the hash of the rational from hashes of the numerator and the
   * denominator.
   */
  size_t hash() const {
    size_t numeratorHash = gmpz_hash(mpq_numref(d_value));
    size_t denominatorHash = gmpz_hash(mpq_denref(d_value));

    return numeratorHash xor denominatorHash;
  }

};/* class Rational */

struct RationalHashStrategy {
  static inline size_t hash(const CVC4::Rational& r) {
    return r.hash();
  }
};/* struct RationalHashStrategy */

std::ostream& operator<<(std::ostream& os, const Rational& n);

}/* CVC4 namespace */

#endif /* __CVC4__RATIONAL_H */

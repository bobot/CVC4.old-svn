/*********************                                                        */
/*! \file integer.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A multiprecision integer constant.
 **
 ** A multiprecision integer constant.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__INTEGER_H
#define __CVC4__INTEGER_H

#include <string>
#include <iostream>
#include <limits.h>
#include "util/Assert.h"
#include "util/gmp_util.h"

namespace CVC4 {

struct mpz_mimic {
  signed long int value;
  uint_ptr_t fakePointer;
};

union stuffed_mpz_t {
  struct mpz_mimic mimic;
  mpz_t mpz;
};

class Rational;

class Integer {
private:
  /**
   * Stores the value of the rational is stored in a C++ GMP integer class.
   * Using this instead of mpz_t allows for easier destruction.
   */
  stuffed_mpz_t d_value;

  /**
   * Constructs an Integer by copying a GMP C++ primitive.
   */
  explicit Integer(const mpz_t val){
    mpz_init_set(d_value.mpz, val);
  }

  inline bool isMpz() const{
    return (d_value.mimic.fakePointer & 0x1) == 0;
  }

  inline void makeMpz(){
    Assert(!isMpz());
    mpz_init_set_si(d_value.mpz, d_value.mimic.value);
  }

  inline void initMimic(signed long int v){
    d_value.mimic.fakePointer = 0x1;
    setValue(v);
  }

  inline void makeMimicIfPossible(){
    Assert(isMpz());
    if(mpz_fits_slong_p(d_value.mpz)){
      signed long int si = mpz_get_si(d_value.mpz);
      mpz_clear(d_value.mpz);
      initMimic(si);
    }
  }

  inline void makeMimicByForce(signed long int value){
    Assert(isMpz());
    mpz_clear(d_value.mpz);
    initMimic(value);
  }

  inline void setValue(signed long int v){
    d_value.mimic.value = v;
    if(d_value.mimic.value == LONG_MIN){
      makeMpz();
    }
  }

public:

  /** Constructs a rational with the value 0. */
  Integer(){
    initMimic(0);
  }

  /**
   * Constructs a Integer from a C string.
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  explicit Integer(const char * s, int base = 10){
    int res = mpz_init_set_str(d_value.mpz,s,base);
    if(res == -1){
      throw std::invalid_argument("mpz_init_set_str failed");
    }
    makeMimicIfPossible();
  }
  Integer(const std::string& s, unsigned base = 10){
    int res = mpz_init_set_str(d_value.mpz,s.c_str(),base);
    if(res == -1){
      throw std::invalid_argument("mpz_init_set_str failed");
    }
    makeMimicIfPossible();
  }

  Integer(const Integer& q) {
    if(q.isMpz()){
      mpz_init_set(d_value.mpz, q.d_value.mpz);
    }else{
      initMimic(q.d_value.mimic.value);
    }
  }
  Integer(  signed long int z){
    initMimic(z);
  }
  Integer(unsigned long int z){
    if(z <= LONG_MAX){
      initMimic((signed long int)z);
    }else{
      mpz_init_set_ui(d_value.mpz, z);
    }
  }

  ~Integer() {
    if(isMpz()){
      mpz_clear(d_value.mpz);
    }
  }


  Integer& operator=(const Integer& x){
    if(this == &x) return *this;
    if(isMpz()){
      if(x.isMpz()){
        mpz_set(d_value.mpz, x.d_value.mpz);
      }else{
        makeMimicByForce(x.d_value.mimic.value);
      }
    }else{
      if(x.isMpz()){
        makeMpz();
        mpz_set(d_value.mpz, x.d_value.mpz);
      }else{
        d_value.mimic.value = x.d_value.mimic.value;
      }
    }
    return *this;
  }

  Integer operator-() const{
    Integer ret;
    if(isMpz()){
      ret.makeMpz();
      mpz_neg(ret.d_value.mpz, this->d_value.mpz);
    }else{
      ret.setMimicValue( -d_value.mimic.value );
    }
    return ret;
  }

  static int cmp(const Integer& a, const Integer& b){
    if(a.isMpz() && b.isMpz()){
      return mpz_cmp(a.d_value.mpz, b.d_value.mpz);
    }else if(a.isMpz() && !b.isMpz()){
      return mpz_cmp_si(a.d_value.mpz, b.d_value.mimic.value);
    }else if(!a.isMpz() && b.isMpz()){
      return (-1) * mpz_cmp_si(b.d_value.mpz, a.d_value.mimic.value);
    }else{
      return sgn(a.d_value.mimic.value - b.d_value.mimic.value);
    }
  }

  bool operator==(const Integer& y) const {
    return Integer::cmp(*this, y) == 0;
  }



  bool operator!=(const Integer& y) const {
    return Integer::cmp(*this, y) != 0;
  }

  bool operator< (const Integer& y) const {
    return Integer::cmp(*this, y) < 0;
  }

  bool operator<=(const Integer& y) const {
    return Integer::cmp(*this, y) <= 0;
  }

  bool operator> (const Integer& y) const {
    return Integer::cmp(*this, y) > 0;
  }

  bool operator>=(const Integer& y) const {
    return Integer::cmp(*this, y) >= 0;
  }


  Integer operator+(const Integer& y) const{
    if(isMpz() && y.isMpz()){
      Integer ret;
      ret.makeMpz();
      mpz_add(ret.d_value.mpz, d_value.mpz, y.d_value.mpz);
      return ret;
    }else if(isMpz() && !y.isMpz()){
      Integer ret(y.d_value.mimic.value);
      ret.makeMpz();
      mpz_add(ret.d_value.mpz, d_value.mpz, ret.d_value.mpz);
      return ret;
    }else if(!isMpz() && y.isMpz()){
      Integer ret(d_value.mimic.value);
      ret.makeMpz();
      mpz_add(ret.d_value.mpz, y.d_value.mpz, ret.d_value.mpz);
      return ret;
    }else{
      signed long int res;
      res = d_value.mimic.value + y.d_value.mimic.value;
      if(res < d_value.mimic.value && res < y.d_value.mimic.value);
        return Integer(res);
      }else{
        Integer ret(d_value.mimic.value);
        ret.makeMpz();
        mpz_t other;
        mpz_init_set_si(other, y.d_value.mimic.value);
        mpz_add(ret.d_value.mpz, other, ret.d_value.mpz);
        mpz_clear(other);
        return ret;
      }
    }
  }

  Integer operator-(const Integer& y) const {
    Integer neg = -y;
    return (*this) + neg;
  }

  Integer operator*(const Integer& y) const {
    if(!isMpz() && d_value.mimic.value == LONG_MIN)
      makeMpz();

    if(!isMpz() && d_value.mimic.value == LONG_MIN)
      makeMpz();

    if(isMpz() && y.isMpz()){
      Integer ret;
      ret.makeMpz();
      mpz_mul(ret.d_value.mpz, d_value.mpz, y.d_value.mpz);
      return ret;
    }else if(isMpz() && !y.isMpz()){
      Integer ret(y.d_value.mimic.value);
      ret.makeMpz();
      mpz_mul(ret.d_value.mpz, d_value.mpz, ret.d_value.mpz);
      return ret;
    }else if(!isMpz() && y.isMpz()){
      Integer ret(d_value.mimic.value);
      ret.makeMpz();
      mpz_mul(ret.d_value.mpz, y.d_value.mpz, ret.d_value.mpz);
      return ret;
    }else{
      bool sameSign = sgn(ret.d_value.mimic.value) == sgn(ret.d_value.mimic.value);
      unsigned long int a = abs(d_value.mimic.value);
      unsigned long int b = abs(ret.d_value.mimic.value);

      unsigned long int a1 = a + shifting;
      unsigned long int a0 = a + bitmask;
      unsigned long int b1 = b + shifting;
      unsigned long int b0 = b + bitmask;

      bool overflow = false;

      if(a1 != 0 && b1 != 0) overflow = true;
      else if()

  (a1 shift + a0) * (b1 shift + b0) ==
  a1 b1 shift shift + a1 b0 shift + a0 b1 shift + a0 b0
The first term is shifted by 64 bits, so if both a1 and b1 are nonzero, we have an overflow right there and can abort.

For the second and third part we do the 32x32->64 multiplication we just used to check for overflow for 32-bit numbers. This is shifted by 32 bits, so we have an overflow if the upper half of it is nonzero. Since we already know that either a1 or b1 is zero, we can simply calculate

  a=(uint64_t)(a1)*b0+(uint64_t)(a0)*b1;
At least one half of this term will be zero, so we cant have an overflow in the addition. Then, if a > 0xffffffff, we have an overflow in the multiplication and can abort.

If we got this far, the result is

  (a << 32) + (uint64_t)(a0)*b0;

  }

  /** Raise this Integer to the power <code>exp</code>.
   *
   * @param exp the exponent
   */
  Integer pow(unsigned long int exp) const {
    Integer ret;
    ret.makeMpz();
    mpz_pow_ui(ret.d_value.mpz,d_value.mpz,exp);
    ret.makeMimicIfPossible();
    return ret;
  }

  std::string toString(int base = 10) const{
    return std::string(mpz_get_str(NULL, base, d_value.mpz));
  }

  //friend std::ostream& operator<<(std::ostream& os, const Integer& n);

  long getLong() const { return mpz_get_si(d_value.mpz); }
  unsigned long getUnsignedLong() const {return  mpz_get_ui(d_value.mpz); }

  /**
   * Computes the hash of the node from the first word of the
   * numerator, the denominator.
   */
  size_t hash() const {
    return gmpz_hash(d_value.mpz);
  }
private:
  friend class Rational;
  static void set(mpz_t rop, const Integer& n){
    mpz_set(rop, n.d_value.mpz);
  }

};/* class Integer */

struct IntegerHashStrategy {
  static inline size_t hash(const CVC4::Integer& i) {
    return i.hash();
  }
};/* struct IntegerHashStrategy */

std::ostream& operator<<(std::ostream& os, const Integer& n);

}/* CVC4 namespace */

#endif /* __CVC4__INTEGER_H */

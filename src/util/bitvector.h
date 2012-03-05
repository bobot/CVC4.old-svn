/*********************                                                        */
/*! \file bitvector.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__BITVECTOR_H
#define __CVC4__BITVECTOR_H

#include <iostream>
#include "util/Assert.h"
#include "util/integer.h"

namespace CVC4 {


  // static  BitVector intToTwosComplement(const Integer& val, unsigned size) {
  //   Integer res = val;
  //   if (res < 0) {
  //     // Take absolute value
  //     res = res.abs();
  //     // truncate to fit bitwidth
  //     res = res.modByPow2(size);
  //     return - BitVector(size, res);
  //   }
  //   // do i really need this?
  //   if (res >= Integer(1).multiplyByPow2(size)) {
  //     res = res.modByPow2(size); 
  //   }
  //   return BitVector(size, res); 
  // }



class CVC4_PUBLIC BitVector {

private:

  /*
    Class invariants:
    * no overflows: 2^d_size < d_value
    * no negative numbers: d_value >= 0
   */
  unsigned d_size;
  Integer d_value;

  Integer toSignedInt() const {
    // returns Integer corresponding to two's complement interpretation of bv 
    unsigned size = d_size; 
    Integer sign_bit = d_value.extractBitRange(1,size-1);
    Integer val = d_value.extractBitRange(size-1, 0); 
    Integer res = Integer(-1) * sign_bit.multiplyByPow2(size - 1) + val;
    return res; 
  }
  
 
public:

  BitVector(unsigned size, const Integer& val):
    d_size(size),
    d_value(val.modByPow2(size))
      {}
  
  BitVector(unsigned size = 0)
    : d_size(size), d_value(0) {}

  BitVector(unsigned size, unsigned int z)
    : d_size(size), d_value(z) {
    d_value = d_value.modByPow2(size);
  }
  
  BitVector(unsigned size, unsigned long int z)
    : d_size(size), d_value(z) {
    d_value = d_value.modByPow2(size);
  }

  BitVector(unsigned size, const BitVector& q)
    : d_size(size), d_value(q.d_value) {}
  
  BitVector(const std::string& num, unsigned base = 2);

  ~BitVector() {}

  BitVector& operator =(const BitVector& x) {
    if(this == &x)
      return *this;
    d_size = x.d_size;
    d_value = x.d_value;
    return *this;
  }

  bool operator ==(const BitVector& y) const {
    if (d_size != y.d_size) return false; 
    return d_value == y.d_value;
  }

  bool operator !=(const BitVector& y) const {
    if (d_size != y.d_size) return true; 
    return d_value != y.d_value;
  }

  BitVector equals(const BitVector&  y) const {
    Assert(d_size == y.d_size);
    return d_value == y.d_value; 
  }

  BitVector concat (const BitVector& other) const {
    return BitVector(d_size + other.d_size, (d_value.multiplyByPow2(other.d_size)) + other.d_value);
  }

  BitVector extract(unsigned high, unsigned low) const {
    return BitVector(high - low + 1, d_value.extractBitRange(high - low + 1, low));
  }

  /*
    Bitwise operations on BitVectors
   */

  // xor
  BitVector operator ^(const BitVector& y) const {
    Assert (d_size == y.d_size); 
    return BitVector(d_size, d_value.bitwiseXor(y.d_value)); 
  }
  
  // or
  BitVector operator |(const BitVector& y) const {
    Assert (d_size == y.d_size); 
    return BitVector(d_size, d_value.bitwiseOr(y.d_value)); 
  }
  
  // and
  BitVector operator &(const BitVector& y) const {
    Assert (d_size == y.d_size); 
    return BitVector(d_size, d_value.bitwiseAnd(y.d_value)); 
  }

  // not
  BitVector operator ~() const {
    return BitVector(d_size, d_value.bitwiseNot()); 
  }

  /*
    Arithmetic operations on BitVectors
   */

  BitVector operator +(const BitVector& y) const {
    Assert (d_size == y.d_size);
    Integer sum = d_value +  y.d_value;
    return BitVector(d_size, sum);
  }

  BitVector operator -(const BitVector& y) const {
    Assert (d_size == y.d_size);
    // to maintain the invariant that we are only adding BitVectors of the
    // same size
    BitVector one(d_size, Integer(1)); 
    return *this + ~y + one;
  }

  BitVector operator -() const {
    BitVector one(d_size, Integer(1)); 
    return ~(*this) + one;
  }

  BitVector operator *(const BitVector& y) const {
    Assert (d_size == y.d_size);
    Integer prod = d_value * y.d_value;
    return BitVector(d_size, prod);
  }
  
  BitVector unsignedDiv (const BitVector& y) const {
    Assert (d_size == y.d_size);
    Assert (d_value >= 0 && y.d_value > 0); 
    return BitVector(d_size, d_value.floorDivideQuotient(y.d_value)); 
  }

  BitVector unsignedRem(const BitVector& y) const {
    Assert (d_size == y.d_size);
    Assert (d_value >= 0 && y.d_value > 0); 
    return BitVector(d_size, d_value.floorDivideRemainder(y.d_value)); 
  }
  
  
  bool signedLessThan(const BitVector& y) const {
    Assert(d_size == y.d_size);
    Assert(d_value >= 0 && y.d_value >= 0);
    Integer a = (*this).toSignedInt();
    Integer b = y.toSignedInt(); 
    
    return a < b; 
  }

  bool unsignedLessThan(const BitVector& y) const {
    Assert(d_size == y.d_size);
    Assert(d_value >= 0 && y.d_value >= 0);
    return d_value < y.d_value; 
  }

  bool signedLessThanEq(const BitVector& y) const {
    Assert(d_size == y.d_size);
    Assert(d_value >= 0 && y.d_value >= 0);
    Integer a = (*this).toSignedInt();
    Integer b = y.toSignedInt(); 
    
    return a <= b; 
  }

  bool unsignedLessThanEq(const BitVector& y) const {
    Assert(d_size == y.d_size);
    Assert(d_value >= 0 && y.d_value >= 0);
    return d_value <= y.d_value; 
  }

  
  /*
    Extend operations
   */

  BitVector zeroExtend(unsigned amount) const {
    return BitVector(d_size + amount, d_value); 
  }

  BitVector signExtend(unsigned amount) const {
    Integer sign_bit = d_value.extractBitRange(1, d_size -1);
    if(sign_bit == Integer(0)) {
      return BitVector(d_size + amount, d_value); 
    } else {
      Integer val = d_value.oneExtend(d_size, amount);
      return BitVector(d_size+ amount, val);
    }
  }
  
  /*
    Shifts on BitVectors
   */

  BitVector leftShift(const BitVector& y) const {
    if (y.d_value > Integer(d_size)) {
      return BitVector(d_size, Integer(0)); 
    }
    if (y.d_value == 0) {
      return *this; 
    }

    // making sure we don't lose information casting
    Assert(y.d_value < Integer(1).multiplyByPow2(32));
    uint32_t amount = y.d_value.toUnsignedInt(); 
    Integer res = d_value.multiplyByPow2(amount);
    return BitVector(d_size, res);
  }

  BitVector logicalRightShift(const BitVector& y) const {
    if(y.d_value > Integer(d_size)) {
      return BitVector(d_size, Integer(0)); 
    }

    // making sure we don't lose information casting
    Assert(y.d_value < Integer(1).multiplyByPow2(32));
    uint32_t amount = y.d_value.toUnsignedInt(); 
    Integer res = d_value.divByPow2(amount); 
    return BitVector(d_size, res);
  }

  BitVector arithRightShift(const BitVector& y) const {
    Integer sign_bit = d_value.extractBitRange(1, d_size - 1); 
    if(y.d_value > Integer(d_size)) {
      if(sign_bit == Integer(0)) {
        return BitVector(d_size, Integer(0)); 
      } else {
        return BitVector(d_size, Integer(d_size).multiplyByPow2(d_size) -1 ); 
      }
    }
    
    if (y.d_value == 0) {
      return *this; 
    }

    // making sure we don't lose information casting
    Assert(y.d_value < Integer(1).multiplyByPow2(32));

    uint32_t amount  = y.d_value.toUnsignedInt();
    Integer res = d_value.divByPow2(amount);
    BitVector res_bv(d_size - amount, res);
    res_bv = res_bv.signExtend(amount); 
    return res_bv;
  }
  

  /*
    Convenience functions
   */
  
  size_t hash() const {
    return d_value.hash() + d_size;
  }

  std::string toString(unsigned int base = 2) const {
    std::string str = d_value.toString(base);
    if( base == 2 && d_size > str.size() ) {
      std::string zeroes;
      for( unsigned int i=0; i < d_size - str.size(); ++i ) {
        zeroes.append("0");
      }
      return zeroes + str;
    } else {
      return str;
    }
  }

  unsigned getSize() const {
    return d_size;
  }

  const Integer& getValue() const {
    return d_value;
  }
};/* class BitVector */



inline BitVector::BitVector(const std::string& num, unsigned base) {
  AlwaysAssert( base == 2 || base == 16 );

  if( base == 2 ) {
    d_size = num.size();
  } else if( base == 16 ) {
    d_size = num.size() * 4;
  } else {
    Unreachable("Unsupported base in BitVector(std::string&, unsigned int).");
  }

  d_value = Integer(num,base);
}/* BitVector::BitVector() */


/**
 * Hash function for the BitVector constants.
 */
struct CVC4_PUBLIC BitVectorHashStrategy {
  static inline size_t hash(const BitVector& bv) {
    return bv.hash();
  }
};/* struct BitVectorHashStrategy */

/**
 * The structure representing the extraction operation for bit-vectors. The
 * operation map bit-vectors to bit-vector of size <code>high - low + 1</code>
 * by taking the bits at indices <code>high ... low</code>
 */
struct CVC4_PUBLIC BitVectorExtract {
  /** The high bit of the range for this extract */
  unsigned high;
  /** The low bit of the range for this extract */
  unsigned low;

  BitVectorExtract(unsigned high, unsigned low)
  : high(high), low(low) {}

  bool operator == (const BitVectorExtract& extract) const {
    return high == extract.high && low == extract.low;
  }
};/* struct BitVectorExtract */

/**
 * Hash function for the BitVectorExtract objects.
 */
class CVC4_PUBLIC BitVectorExtractHashStrategy {
public:
  static size_t hash(const BitVectorExtract& extract) {
    size_t hash = extract.low;
    hash ^= extract.high + 0x9e3779b9 + (hash << 6) + (hash >> 2);
    return hash;
  }
};/* class BitVectorExtractHashStrategy */


/**
 * The structure representing the extraction of one Boolean bit. 
 */
struct CVC4_PUBLIC BitVectorBitOf {
  /** The index of the bit */
  unsigned bitIndex;
  BitVectorBitOf(unsigned i)
    : bitIndex(i) {}

  bool operator == (const BitVectorBitOf& other) const {
    return bitIndex == other.bitIndex; 
  }
};/* struct BitVectorBitOf */

/**
 * Hash function for the BitVectorBitOf objects.
 */
class CVC4_PUBLIC BitVectorBitOfHashStrategy {
public:
  static size_t hash(const BitVectorBitOf& b) {
    return b.bitIndex;
  }
};/* class BitVectorBitOfHashStrategy */



struct CVC4_PUBLIC BitVectorSize {
  unsigned size;
  BitVectorSize(unsigned size)
  : size(size) {}
  operator unsigned () const { return size; }
};/* struct BitVectorSize */

struct CVC4_PUBLIC BitVectorRepeat {
  unsigned repeatAmount;
  BitVectorRepeat(unsigned repeatAmount)
  : repeatAmount(repeatAmount) {}
  operator unsigned () const { return repeatAmount; }
};/* struct BitVectorRepeat */

struct CVC4_PUBLIC BitVectorZeroExtend {
  unsigned zeroExtendAmount;
  BitVectorZeroExtend(unsigned zeroExtendAmount)
  : zeroExtendAmount(zeroExtendAmount) {}
  operator unsigned () const { return zeroExtendAmount; }
};/* struct BitVectorZeroExtend */

struct CVC4_PUBLIC BitVectorSignExtend {
  unsigned signExtendAmount;
  BitVectorSignExtend(unsigned signExtendAmount)
  : signExtendAmount(signExtendAmount) {}
  operator unsigned () const { return signExtendAmount; }
};/* struct BitVectorSignExtend */

struct CVC4_PUBLIC BitVectorRotateLeft {
  unsigned rotateLeftAmount;
  BitVectorRotateLeft(unsigned rotateLeftAmount)
  : rotateLeftAmount(rotateLeftAmount) {}
  operator unsigned () const { return rotateLeftAmount; }
};/* struct BitVectorRotateLeft */

struct CVC4_PUBLIC BitVectorRotateRight {
  unsigned rotateRightAmount;
  BitVectorRotateRight(unsigned rotateRightAmount)
  : rotateRightAmount(rotateRightAmount) {}
  operator unsigned () const { return rotateRightAmount; }
};/* struct BitVectorRotateRight */

template <typename T>
struct CVC4_PUBLIC UnsignedHashStrategy {
  static inline size_t hash(const T& x) {
    return (size_t)x;
  }
};/* struct UnsignedHashStrategy */

inline std::ostream& operator <<(std::ostream& os, const BitVector& bv) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const BitVector& bv) {
  return os << bv.toString();
}

inline std::ostream& operator <<(std::ostream& os, const BitVectorExtract& bv) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const BitVectorExtract& bv) {
  return os << "[" << bv.high << ":" << bv.low << "]";
}

inline std::ostream& operator <<(std::ostream& os, const BitVectorBitOf& bv) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const BitVectorBitOf& bv) {
  return os << "[" << bv.bitIndex << "]";
}



}/* CVC4 namespace */

#endif /* __CVC4__BITVECTOR_H */

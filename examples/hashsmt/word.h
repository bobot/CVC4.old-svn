/*
 * word.h
 *
 *  Created on: Jul 13, 2012
 *      Author: dejan
 */

#ifndef WORD_H_
#define WORD_H_

#include <string>
#include <iostream>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "options/options.h"

namespace hashsmt {

class Word {

  /** Expression managaer we're using for all word expressions */
  static CVC4::ExprManager* s_manager;

protected:

  /** The expression of this word */
  CVC4::Expr d_expr;

  /** Get the expression manager words are using */
  static CVC4::ExprManager* em();

  Word(CVC4::Expr expr = CVC4::Expr())
  : d_expr(expr) {}

  /** Extend the representing expression to the given size >= size() */
  CVC4::Expr extendToSize(unsigned size) const;

public:

  Word(unsigned size, unsigned value = 0);
  Word(unsigned size, std::string name);

  Word& operator =  (const Word& b);
  Word  operator +  (const Word& b) const;
  Word& operator += (const Word& b);
  Word  operator ~  () const;
  Word  operator &  (const Word& b) const;
  Word  operator |  (const Word& b) const;
  Word& operator |= (const Word& b);
  Word  operator ^  (const Word& b) const;
  Word  operator << (unsigned amount) const;
  Word  operator >> (unsigned amount) const;

  unsigned size() const;

  void print(std::ostream& out) const;

  CVC4::Expr getExpr() const {
    return d_expr;
  }

  /** Returns the comparison expression */  
  CVC4::BoolExpr operator == (const Word& b) const;
};

inline std::ostream& operator << (std::ostream& out, const Word& word) {
  word.print(out);
  return out;
}

/** Symbolic 32-bit unsigned integer as a CVC4 bitvector expression */
class cvc4_uint32 : public Word {
public:

  /** Construction from constants of the right size */
  cvc4_uint32(unsigned value = 0)
  : Word(32, value) {}

  /** Construction of variables of the right size */
  cvc4_uint32(std::string name)
  : Word(32, name) {}

  /** Automatic extend/cut to uint32 */
  cvc4_uint32(const Word& word);
};

/** Symbolic 8-bit unsigned char as a CVC4 bitvector expression */
class cvc4_uchar8 : public Word {
public:

  /** Construction from constants of the right size */
  cvc4_uchar8(unsigned value = 0)
  : Word(8, value) {}

  /** Construction of variables of the right size */
  cvc4_uchar8(std::string name)
  : Word(8, name) {}

  /** Automatic extend/cut to uchar8 */
  cvc4_uchar8(const Word& word);
};


}

#endif /* WORD_H_ */

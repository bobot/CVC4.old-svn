/*********************                                                        */
/*! \file simple_vc_cxx.cpp
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
 ** \brief A simple demonstration of the C++ interface
 **
 ** A simple demonstration of the C++ interface.  Compare to the Java
 ** interface in SimpleVC.java; they are virtually line-by-line
 ** identical.
 **/

#include <iostream>

//#include <cvc4/cvc4.h> // use this after CVC4 is properly installed
#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);

  // Prove that for integers x and y:
  //   x > 0 AND y > 0  =>  2x + y >= 3

  Type integer = em.integerType();

  Expr x = em.mkVar("x", integer);
  Expr y = em.mkVar("y", integer);
  Expr zero = em.mkConst(Rational(0));

  Expr x_positive = em.mkExpr(kind::GT, x, zero);
  Expr y_positive = em.mkExpr(kind::GT, y, zero);

  Expr two = em.mkConst(Rational(2));
  Expr twox = em.mkExpr(kind::MULT, two, x);
  Expr twox_plus_y = em.mkExpr(kind::PLUS, twox, y);

  Expr three = em.mkConst(Rational(3));
  Expr twox_plus_y_geq_3 = em.mkExpr(kind::GEQ, twox_plus_y, three);

  Expr formula =
    em.mkExpr(kind::AND, x_positive, y_positive).
    impExpr(twox_plus_y_geq_3);

  cout << "Checking validity of formula " << formula << " with CVC4." << endl;
  cout << "CVC4 should report VALID." << endl;
  cout << "Result from CVC4 is: " << smt.query(formula) << endl;

  return 0;
}

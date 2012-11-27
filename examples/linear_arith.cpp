/*********************                                                        */
/*! \file linear_arith.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A simple demonstration of the linear arithmetic capabilities of CVC4
 **
 ** A simple demonstration of the linear real, integer and mixed real integer
 ** solving capabilities of CVC4.
 **/

#include <iostream>

//#include <cvc4/cvc4.h> // use this after CVC4 is properly installed
#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);
  smt.setOption("incremental", SExpr("true")); // Enable incremental solving

  // Prove that if given x (Integer) and y (Real) then
  // the maximum value of y - x is 2/3

  // Types
  Type real = em.realType();
  Type integer = em.integerType();

  // Variables
  Expr x = em.mkVar("x", integer);
  Expr y = em.mkVar("y", real);

  // Constants
  Expr three = em.mkConst(Rational(3));
  Expr neg2 = em.mkConst(Rational(-2));
  Expr two_thirds = em.mkConst(Rational(2,3));

  // Terms
  Expr three_y = em.mkExpr(kind::MULT, three, y);
  Expr diff = em.mkExpr(kind::MINUS, y, x);

  // Formulas
  Expr x_geq_3y = em.mkExpr(kind::GEQ, x, three_y);
  Expr x_leq_y = em.mkExpr(kind::LEQ, x, y);
  Expr neg2_lt_x = em.mkExpr(kind::LT, neg2, x);

  Expr assumptions =
    em.mkExpr(kind::AND, x_geq_3y, x_leq_y, neg2_lt_x);

  cout << "Given the assumptions " << assumptions << endl;
  smt.assertFormula(assumptions);


  Expr diff_leq_two_thirds = em.mkExpr(kind::LEQ, diff, two_thirds);
  smt.push();
  cout << "Prove that " << diff_leq_two_thirds << " with CVC4." << endl;
  cout << "CVC4 should report VALID." << endl;
  cout << "Result from CVC4 is: " << smt.query(diff_leq_two_thirds) << endl;
  smt.pop();

  cout << endl;

  Expr diff_is_two_thirds = em.mkExpr(kind::EQUAL, diff, two_thirds);
  smt.push();
  cout << "Show that the asserts are consistent with " << endl;
  cout << diff_is_two_thirds << " with CVC4." << endl;
  cout << "CVC4 should report SAT." << endl;
  cout << "Result from CVC4 is: " << smt.checkSat(diff_is_two_thirds) << endl;
  smt.pop();

  cout << "Thus the maximum value of (y - x) is 2/3."<< endl;

  return 0;
}

/*********************                                                        */
/*! \file bitvectors.cpp
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A simple demonstration of the solving capabilities of the CVC4
 ** bit-vector solver.
 **
 **/

#include <iostream>

//#include <cvc4/cvc4.h> // use this after CVC4 is properly installed
#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);
  smt.setOption("incremental", true); // Enable incremental solving
  smt.setLogic("QF_BV");              // Set the logic

  // The following example has been adapted from the book A Hacker's Delight by
  // Henry S. Warren.
  //
  // Given a variable x that can only have two values, a or b. We want to
  // assign to x a value other than the current one. The straightforward code
  // to do that is:
  //
  //(0) if (x == a ) x = b;
  //    else x = a;
  //
  // Two more efficient yet equivalent methods are:
  //
  //(1) x = a ⊕ b ⊕ x;
  //
  //(2) x = a + b - x;
  //
  // We will use CVC4 to prove that the three pieces of code above are all
  // equivalent by encoding the problem in the bit-vector theory.

  // Creating a bit-vector type of width 32
  Type bitvector32 = em.mkBitVectorType(32);

  // Variables
  Expr x = em.mkVar("x", bitvector32);
  Expr a = em.mkVar("a", bitvector32);
  Expr b = em.mkVar("b", bitvector32);

  // First encode the assumption that x must be equal to a or b
  Expr x_eq_a = em.mkExpr(kind::EQUAL, x, a);
  Expr x_eq_b = em.mkExpr(kind::EQUAL, x, b);
  Expr assumption = em.mkExpr(kind::OR, x_eq_a, x_eq_b);

  // Assert the assumption
  smt.assertFormula(assumption);

  // Introduce a new variable for the new value of x after assignment.
  Expr new_x = em.mkVar("new_x", bitvector32); // x after executing code (0)
  Expr new_x_ = em.mkVar("new_x_", bitvector32); // x after executing code (1) or (2)

  // Encoding code (0)
  // new_x = x == a ? b : a;
  Expr ite = em.mkExpr(kind::ITE, x_eq_a, b, a);
  Expr assignment0 = em.mkExpr(kind::EQUAL, new_x, ite);

  // Assert the encoding of code (0)
  cout << "Asserting " << assignment0 << " to CVC4 " << endl;
  smt.assertFormula(assignment0);
  cout << "Pushing a new context." << endl;
  smt.push();

  // Encoding code (1)
  // new_x_ = a xor b xor x
  Expr a_xor_b_xor_x = em.mkExpr(kind::BITVECTOR_XOR, a, b, x);
  Expr assignment1 = em.mkExpr(kind::EQUAL, new_x_, a_xor_b_xor_x);

  // Assert encoding to CVC4 in current context;
  cout << "Asserting " << assignment1 << " to CVC4 " << endl;
  smt.assertFormula(assignment1);
  Expr new_x_eq_new_x_ = em.mkExpr(kind::EQUAL, new_x, new_x_);

  cout << " Querying: " << new_x_eq_new_x_ << endl;
  cout << " Expect valid. " << endl;
  cout << " CVC4: " << smt.query(new_x_eq_new_x_) << endl;
  cout << " Popping context. " << endl;
  smt.pop();

  // Encoding code (2)
  // new_x_ = a + b - x
  Expr a_plus_b = em.mkExpr(kind::BITVECTOR_PLUS, a, b);
  Expr a_plus_b_minus_x = em.mkExpr(kind::BITVECTOR_SUB, a_plus_b, x);
  Expr assignment2 = em.mkExpr(kind::EQUAL, new_x_, a_plus_b_minus_x);

  // Assert encoding to CVC4 in current context;
  cout << "Asserting " << assignment2 << " to CVC4 " << endl;
  smt.assertFormula(assignment1);

  cout << " Querying: " << new_x_eq_new_x_ << endl;
  cout << " Expect valid. " << endl;
  cout << " CVC4: " << smt.query(new_x_eq_new_x_) << endl;

  return 0;
}

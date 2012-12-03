/*********************                                                        */
/*! \file HelloWorld.java
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A very simple CVC4 example
 **
 ** A very simple CVC4 tutorial example.
 **/

import edu.nyu.acsys.CVC4.*;

public class HelloWorld {
  public static void main(String[] args) {
    System.loadLibrary("cvc4jni");

    ExprManager em = new ExprManager();
    Expr helloworld = em.mkVar("Hello World!", em.booleanType());
    SmtEngine smt = new SmtEngine(em);

    System.out.println(helloworld + " is " + smt.query(helloworld));
  }
}

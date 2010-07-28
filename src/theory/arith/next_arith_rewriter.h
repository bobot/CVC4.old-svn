/*********************                                                        */
/*! \file arith_rewriter.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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




class ArithRewriter{
private:
  ArithConstants* d_constants;


  Node makeSubtractionNode(TNode l, TNode r);
  Node makeUnaryMinusNode(TNode n);

  /** Returns a node of kind CONST_RATIONAL */
  Node evaluateConstantExpression(TNode n);

  Node rewriteTerm(TNode t);

  Node rewriteTerm(TNode t);
  Node rewriteMult(TNode t);
  Node rewritePlus(TNode t);
  Node rewriteMinus(TNode t);

public:
  ArithRewriter(ArithConstants* ac) :
    d_constants(ac)
  {}

  RewriteResponse preRewrite(TNode n, bool topLevel);
  RewriteResponse postRewrite(TNode n, bool topLevel);

};


}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__REWRITER_H */

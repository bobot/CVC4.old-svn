/*********************                                                        */
/*! \file arith_rewriter.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters, dejan
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

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_REWRITER_H
#define __CVC4__THEORY__ARITH__ARITH_REWRITER_H

#include "theory/theory.h"
#include "theory/arith/arith_constants.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithRewriter {

private:

  static __thread arith::ArithConstants* s_constants;

  static Node makeSubtractionNode(TNode l, TNode r);
  static Node makeUnaryMinusNode(TNode n);

  static RewriteResponse preRewriteTerm(TNode t);
  static RewriteResponse postRewriteTerm(TNode t);

  static RewriteResponse rewriteVariable(TNode t);
  static RewriteResponse rewriteConstant(TNode t);
  static RewriteResponse rewriteMinus(TNode t, bool pre);
  static RewriteResponse rewriteUMinus(TNode t, bool pre);
  static RewriteResponse rewriteDivByConstant(TNode t, bool pre);

  static RewriteResponse preRewritePlus(TNode t);
  static RewriteResponse postRewritePlus(TNode t);

  static RewriteResponse preRewriteMult(TNode t);
  static RewriteResponse postRewriteMult(TNode t);


  static RewriteResponse preRewriteAtom(TNode t);
  static RewriteResponse postRewriteAtom(TNode t);
  static RewriteResponse postRewriteAtomConstantRHS(TNode t);

public:

  static RewriteResponse preRewrite(TNode n);
  static RewriteResponse postRewrite(TNode n);

  static void init() {
    if (s_constants == NULL) {
      s_constants = new arith::ArithConstants(NodeManager::currentNM());
    }
  }

  static void shutdown() {
    if (s_constants != NULL) {
      delete s_constants;
      s_constants = NULL;
    }
  }

private:

  static inline bool isAtom(TNode n) {
    return arith::isRelationOperator(n.getKind());
  }

  static inline bool isTerm(TNode n) {
    return !isAtom(n);
  }

};/* class ArithRewriter */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_REWRITER_H */

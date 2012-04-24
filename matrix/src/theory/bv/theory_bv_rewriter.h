/*********************                                                        */
/*! \file theory_bv_rewriter.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
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

#ifndef __CVC4__THEORY__BV__THEORY_BV_REWRITER_H
#define __CVC4__THEORY__BV__THEORY_BV_REWRITER_H

#include "theory/rewriter.h"
#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace bv {

struct AllRewriteRules;
typedef RewriteResponse (*RewriteFunction) (TNode, bool);

class TheoryBVRewriter {
  // static CVC4_THREADLOCAL(AllRewriteRules*) s_allRules;
  // static CVC4_THREADLOCAL(TimerStat*) d_rewriteTimer; 

#warning "TODO: Double check thread safety and make sure the fix compiles on mac."
  static RewriteFunction d_rewriteTable[kind::LAST_KIND];

  static RewriteResponse IdentityRewrite(TNode node, bool prerewrite = false);
  static RewriteResponse UndefinedRewrite(TNode node, bool prerewrite = false); 

  static void initializeRewrites();
  
 static RewriteResponse RewriteEqual(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUlt(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSlt(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUle(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSle(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUgt(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSgt(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUge(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSge(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteNot(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteConcat(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteAnd(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteOr(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteXnor(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteXor(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteNand(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteNor(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteComp(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteMult(TNode node, bool prerewrite = false);
  static RewriteResponse RewritePlus(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSub(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteNeg(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUdiv(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUrem(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSmod(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSdiv(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSrem(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteShl(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteLshr(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteAshr(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteExtract(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteRepeat(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteZeroExtend(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSignExtend(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteRotateRight(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteRotateLeft(TNode node, bool prerewrite = false);

public:

  static RewriteResponse postRewrite(TNode node);

  static RewriteResponse preRewrite(TNode node);

  static inline Node rewriteEquality(TNode node) {
    Debug("bitvector") << "TheoryBV::rewriteEquality(" << node << ")" << std::endl;
    return postRewrite(node).node;
  }

  static void init();
  static void shutdown();
  
};/* class TheoryBVRewriter */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_REWRITER_H */

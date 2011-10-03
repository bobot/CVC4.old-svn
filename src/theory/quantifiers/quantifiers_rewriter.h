/*********************                                                        */
/*! \file quantifiers_rewriter.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewriter for the theory of inductive quantifiers
 **
 ** Rewriter for the theory of inductive quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H
#define __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantifiersRewriter {

public:

  static RewriteResponse postRewrite(TNode in) {
    Debug("quantifiers-rewrite") << "post-rewriting " << in << std::endl;
    return RewriteResponse(REWRITE_DONE, in);
  }

  static RewriteResponse preRewrite(TNode in) {
    Debug("quantifiers-rewrite") << "pre-rewriting " << in << std::endl;
    if( in.getKind()==kind::EXISTS ){
      std::vector< Node > children;
      for( int i=0; i<(int)in.getNumChildren(); i++ ){
        if( i==(int)in.getNumChildren()-1 ){
          children.push_back( in[i].notNode() );
        }else{
          children.push_back( in[i] );
        }
      }
      Node n = NodeManager::currentNM()->mkNode(kind::FORALL, children );
      return RewriteResponse(REWRITE_DONE, n.notNode() );
    }
    return RewriteResponse(REWRITE_DONE, in);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class QuantifiersRewriter */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */


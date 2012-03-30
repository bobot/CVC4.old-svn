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

// attribute for "contains instantiation constants from"
struct NestedQuantAttributeId {};
typedef expr::Attribute<NestedQuantAttributeId, Node> NestedQuantAttribute;

class QuantifiersRewriter {
public:
  static bool isClause( Node n );
  static bool isLiteral( Node n );
  static bool isCube( Node n );
private:
  static void computeArgs( std::map< Node, bool >& active, Node n );
  static void computeArgs( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n );
  static Node computePrenex( Node body, std::vector< Node >& args, std::vector< Node >& exArgs, bool pol );
  static Node computePrenex( Node body, std::vector< Node >& args );
  static Node mkForAll( std::vector< Node >& args, Node body, Node ipl );
  static bool hasArg( std::vector< Node >& args, Node n );

  static void setNestedQuantifiers( Node n, Node q );
public:

  static RewriteResponse postRewrite(TNode in) {
    Debug("quantifiers-rewrite-debug") << "post-rewriting " << in << std::endl;
    if( in.getKind()==kind::EXISTS || in.getKind()==kind::FORALL ){
      std::vector< Node > args;
      for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
        args.push_back( in[0][i] );
      }
      Node ipl;
      if( in.getNumChildren()==3 ){
        ipl = in[2];
      }
      //if( in.hasAttribute(NestedQuantAttribute()) ){
      //  Debug("quantifiers-rewrite") << "It is a nested quantifier." << std::endl;
      //  if( in.getKind()==kind::EXISTS ){
      //    args.push_back( in[in.getNumChildren()-1].notNode() );
      //    Node n = NodeManager::currentNM()->mkNode(kind::FORALL, args );
      //    Debug("quantifiers-rewrite") << "Rewrite " << in << " to " << n.notNode() << std::endl;
      //    return RewriteResponse(REWRITE_DONE, n.notNode() );
      //  }
      //}else{
        NodeBuilder<> defs(kind::AND);
        Node n = rewriteQuant( args, in[ 1 ], defs, ipl, 
                               in.hasAttribute(NestedQuantAttribute()), in.getKind()==kind::EXISTS );
        if( in!=n ){
          Debug("quantifiers-rewrite") << "rewrite " << in << std::endl;
          Debug("quantifiers-rewrite") << " to " << std::endl;
          Debug("quantifiers-rewrite") << n << std::endl;
        }
        return RewriteResponse(REWRITE_DONE, n );
      //}
    }
    return RewriteResponse(REWRITE_DONE, in);
  }

  static RewriteResponse preRewrite(TNode in) {
    Debug("quantifiers-rewrite-debug") << "pre-rewriting " << in << std::endl;
    if( in.getKind()==kind::EXISTS || in.getKind()==kind::FORALL ){
      if( !in.hasAttribute(NestedQuantAttribute()) ){
        setNestedQuantifiers( in[ 1 ], in );
      }
    }
    return RewriteResponse(REWRITE_DONE, in);
  }

  static Node rewriteEquality(TNode equality) {
    return postRewrite(equality).node;
  }

  static inline void init() {}
  static inline void shutdown() {}

  /** returns a literal, writes new quantifier definitions into nb */
  //static Node mkPredicate( std::vector< Node >& args, Node body, NodeBuilder<>& defs );

  static Node rewriteQuant( std::vector< Node >& args, Node body, NodeBuilder<>& defs, Node ipl, bool isNested = false, 
                            bool isExists = false );
  /** options */
  static bool doMiniscopingNoFreeVar();
  static bool doMiniscopingAnd();
  static bool doMiniscopingAndExt();
  static bool doPrenex();
};/* class QuantifiersRewriter */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */


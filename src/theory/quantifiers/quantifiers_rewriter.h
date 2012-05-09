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
#include "theory/quantifiers_engine.h"

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
  static void addNodeToOrBuilder( Node n, NodeBuilder<>& t );
  static Node mkForAll( std::vector< Node >& args, Node body, Node ipl );
  static void computeArgs( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n );
  static bool hasArg( std::vector< Node >& args, Node n );
  static void setNestedQuantifiers( Node n, Node q );
private:
  static void computeArgs( std::map< Node, bool >& active, Node n );
  static Node computePreSkolem2( Node body, std::vector< Node >& args, bool pol );
  static Node computePrenex2( Node body, std::vector< Node >& args, bool pol );
  static Node computeClause( Node n );
  static Node computeCNF2( Node n, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred );
private:
  static Node computeMiniscoping( std::vector< Node >& args, Node body, Node ipl, bool isNested = false );
  static Node computePreSkolem( Node f );
  static Node computePrenex( Node f );
  static Node computeVarElimination( Node f );
  static Node computeCNF( Node f );
private:
  static Node rewriteQuants( Node n, bool isNested = false );
public:
  static RewriteResponse preRewrite(TNode in);
  static RewriteResponse postRewrite(TNode in);
  static Node rewriteEquality(TNode equality) {
    return postRewrite(equality).node;
  }
  static inline void init() {}
  static inline void shutdown() {}
private:
  /** options */
  static bool doMiniscopingNoFreeVar();
  static bool doMiniscopingAnd();
  static bool doPreSkolem( Node f );
  static bool doPrenex( Node f );
  static bool doVarElimination( Node f );
  static bool doCNF( Node f );
};/* class QuantifiersRewriter */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */


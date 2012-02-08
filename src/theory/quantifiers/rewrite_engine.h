/*********************                                                       */
/*! \file rewrite_engine.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: bobot
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewrite Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__REWRITE_ENGINE_H
#define __CVC4__REWRITE_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

  class RewriteEngine : public QuantifiersModule
{
private:
  TheoryQuantifiers* d_th;
  /** list of all rewrite rules */
  std::vector< Node > d_rules;

  /* Function which extract the different part of a rewrite rule */
  static Node getPattern(QuantifiersEngine* qe, Node r);
  static std::vector<Node> getSubstitutedGuards
    (Node r, std::vector< Node > vars, std::vector< Node > match);
  static Node getSubstitutedBody
    (Node r, std::vector< Node > vars, std::vector< Node > match);
  static Node getSubstitutedLemma
    (Node r, std::vector< Node > vars, std::vector< Node > match);

  /** true for predicate */
  Node d_true;

 public:
  RewriteEngine( TheoryQuantifiers* th );
  ~RewriteEngine(){}

  void check( Theory::Effort e );
  void registerQuantifier( Node n );
  void assertNode( Node n );
};

}
}
}

#endif

/*********************                                                        */
/*! \file theory_bv_rewrite_rules_core.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
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

#pragma once

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

template<>
bool RewriteRule<UgtToUlt>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UGT);
}

template<>
Node RewriteRule<UgtToUlt>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgtToUlt>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_ULT, b, a);
  return result;
}


template<>
bool RewriteRule<UgeToUle>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UGE);
}

template<>
Node RewriteRule<UgeToUle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgeToUle>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_ULE, b, a);
  return result;
}


template<>
bool RewriteRule<SgtToSlt>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SGT);
}

template<>
Node RewriteRule<SgtToSlt>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgtToUlt>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_SLT, b, a);
  return result;
}


template<>
bool RewriteRule<SgeToSle>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SGE);
}

template<>
Node RewriteRule<SgeToSle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SgeToSle>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_SLE, b, a);
  return result;
}


template<>
bool RewriteRule<UleSplit>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULE);
}

template<>
Node RewriteRule<UleSplit>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UleSplit>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node eq = utils::mkNode(kind::EQUAL, a, b);
  Node lt = utils::mkNode(kind::BITVECTOR_ULT, a, b); 
  Node result = utils::mkNode(kind::OR, eq, lt);
  return result;
}

template<>
bool RewriteRule<SleSplit>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SLE);
}

template<>
Node RewriteRule<SleSplit>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SleSplit>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node eq = utils::mkNode(kind::EQUAL, a, b);
  Node lt = utils::mkNode(kind::BITVECTOR_SLT, a, b); 
  Node result = utils::mkNode(kind::OR, eq, lt);
  return result;
}



}
}
}

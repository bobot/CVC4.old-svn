/*********************                                                        */
/*! \file rewriter_tables.h
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
 ** \brief Rewriter tables for various theories
 **
 ** This file contains template code for the rewriter tables that are generated
 ** from the Theory kinds files.
 **/

#include "cvc4_private.h"

#pragma once

#include "theory/rewriter.h"
#include "theory/rewriter_attributes.h"

${rewriter_includes}

namespace CVC4 {
namespace theory {

RewriteResponse Rewriter::callPreRewrite(theory::TheoryId theoryId, TNode node) {
  switch(theoryId) {
${pre_rewrite_calls}
  default:
    Unreachable();
  }
}

RewriteResponse Rewriter::callPostRewrite(theory::TheoryId theoryId, TNode node) {
  switch(theoryId) {
${post_rewrite_calls}
  default:
    Unreachable();
  }
}

Node Rewriter::getPreRewriteCache(theory::TheoryId theoryId, TNode node) {
  switch(theoryId) {
${pre_rewrite_get_cache}
  default:
    Unreachable();
  }
}

Node Rewriter::getPostRewriteCache(theory::TheoryId theoryId, TNode node) {
  switch(theoryId) {
${post_rewrite_get_cache}
    default:
    Unreachable();
  }
}

void Rewriter::setPreRewriteCache(theory::TheoryId theoryId, TNode node, TNode cache) {
  switch(theoryId) {
${pre_rewrite_set_cache}
  default:
    Unreachable();
  }
}

void Rewriter::setPostRewriteCache(theory::TheoryId theoryId, TNode node, TNode cache) {
  switch(theoryId) {
${post_rewrite_set_cache}
  default:
    Unreachable();
  }
}

void Rewriter::init() {
${rewrite_init}
}

void Rewriter::shutdown() {
${rewrite_shutdown}
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

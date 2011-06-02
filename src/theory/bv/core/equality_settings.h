/*********************                                                        */
/*! \file equality_settings.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
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

#pragma once

namespace CVC4 {
namespace theory {
namespace bv {


/**
 * Settings for the equality manager.
 */
struct BVEqualitySettings {

  /** We also backtrack the nodes, as they represent the solved equations */
  static const bool backtrackNodes = true;

  /** Normalization preferences */
  static inline bool descend(TNode node) {
    return node.getKind() == kind::BITVECTOR_CONCAT || node.getKind() == kind::BITVECTOR_EXTRACT;
  }

  /** Returns true if node1 has preference to node2 as a representative, otherwise node2 is used */
  static inline bool mergePreference(TNode node1, unsigned node1size, TNode node2, unsigned node2size) {
    if (node1.getKind() == kind::CONST_BITVECTOR) {
      Assert(node2.getKind() != kind::CONST_BITVECTOR);
      return true;
    }
    if (node2.getKind() == kind::CONST_BITVECTOR) {
      Assert(node1.getKind() != kind::CONST_BITVECTOR);
      return false;
    }
    if (node1.getKind() == kind::BITVECTOR_CONCAT) {
      Assert(node2.getKind() != kind::BITVECTOR_CONCAT);
      return true;
    }
    if (node2.getKind() == kind::BITVECTOR_CONCAT) {
      Assert(node1.getKind() != kind::BITVECTOR_CONCAT);
      return false;
    }
    return node2size < node1size;
  }
};

}
}
}

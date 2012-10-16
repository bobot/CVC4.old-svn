/*********************                                                        */
/*! \file slicer.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "theory/bv/slicer.h"
#include "util/integer.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;



Slicer::Slicer()
  : d_equalities()
{}


void Slicer::processEquality(TNode node) {
  Assert (node.getKind() == kind::EQUALS);
  TNode t1 = node[0];
  TNode t2 = node[1];

  // 1. process concatenations by splitting into individual equalities
  // 2. now all equalities are of the form a = b where a and b are either variables
  // or extracts over variables.
  // 3. for each a[] = b[] slice the base for a and b
  if (t1.getKind() == kind::BITVECTOR_CONCAT) {
    
  }
  
  if (t1.getKind() == kind::BITVECTOR_EXTRACT) {
    t1 = t1[0]; 
  }
  if (t2.getKind() == kind::BITVECTOR_EXTRACT) {
    t2 = t2[0]; 
  }

  addEquality(t1, t2);
  addEquality(t2, t1); 

  d_equalities.push_back(node);
  
}

void Slicer::addEquality(TNode t1, TNode t2) {
  if (d_equalityMap.find(t1) == d_equalityMap.end()) {
    d_equalityMap[t1] = new vector<TNode>();  
  }
  std::vector<TNode>* terms = d_equalityMap[t1];
  terms->push_back(t1);
}

void Slicer::computeCoarsestBase() {
  
}

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
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace std; 


Slicer::Slicer()
  : d_simpleEqualities(),
    d_roots(),
    d_numRoots(0),
    d_nodeRootMap()
{}

RootId Slicer::makeRoot(TNode n)  {
  Assert (n.getKind() != kind::BITVECTOR_EXTRACT && n.getKind() != kind::BITVECTOR_CONCAT);
  if (d_nodeRootMap.find(n) != d_nodeRootMap.end()) {
    return d_nodeRootMap[n];
  }
  d_nodeRootMap[n] = d_numRoots; 
  d_roots[d_numRoots++] = n;
  return d_numRoots - 1; 
}

void Slicer::splitEqualities(TNode node, std::vector<Node>& equalities) {
  Assert (node.getKind() == kind::EQUAL);
  TNode t1 = node[0];
  TNode t2 = node[1];

  uint32_t width = utils::getSize(t1); 
  
  Base base1(width); 
  if (t1.getKind() == kind::BITVECTOR_CONCAT) {
    unsigned size = 0; 
    for (int i = t1.getNumChildren(); i >= 0; --i) {
      size = size + utils::getSize(t1[i]);
      base1.sliceAt(size); 
    }
  }

  Base base2(width); 
  if (t2.getKind() == kind::BITVECTOR_CONCAT) {
    unsigned size = 0; 
    for (int i = t2.getNumChildren(); i >= 0; --i) {
      size = size + utils::getSize(t2[i]);
      base2.sliceAt(size); 
    }
  }

  base1.sliceWith(base2); 
  if (base1 != Base(width)) {
    // we split the equalities according to the base
    int last = 0; 
    for (unsigned i = 1; i < utils::getSize(t1); ++i) {
      if (base1.isCutPoint(i)) {
        Node extract1 = Rewriter::rewrite(utils::mkExtract(t1, last, i - 1));
        Node extract2 = Rewriter::rewrite(utils::mkExtract(t2, last, i - 1));
        last = i;
        Assert (utils::getSize(extract1) == utils::getSize(extract2)); 
        equalities.push_back(utils::mkNode(kind::EQUAL, extract1, extract2)); 
      }
    }
  } else {
    // just return same equality
    equalities.push_back(node);
  }
} 
 
void Slicer::processEquality(TNode node) {
  Assert (node.getKind() == kind::EQUAL);
  Debug("bv-slicer") << "theory::bv::Slicer::processEquality " << node << endl; 
  std::vector<Node> equalities;
  splitEqualities(node, equalities); 
  for (int i = 0; i < equalities.size(); ++i) {
    Debug("bv-slicer") << "    splitEqualities " << node << endl;
    d_simpleEqualities.push_back(equalities[i]);
  }
}


TNode Slicer::addSimpleTerm(TNode t1) {
  Base base1(0); 
  if (t1.getKind() == kind::BITVECTOR_EXTRACT) {
    unsigned low = utils::getExtractLow(t1);
    unsigned high = utils::getExtractHigh(t1);
    base1 = base1.setBit(low);
    base1 = base1.setBit(high);
    t1 = t1[0];
  }
  
  Assert (t1.getKind() != kind::BITVECTOR_EXTRACT &&
          t1.getKind() != kind::BITVECTOR_CONCAT ); 

  if (d_bases.find(t1) == d_bases.end()) {
    d_bases[t1] = Base(0); 
  }
  d_bases[t1] = d_bases[t1].bitwiseOr(base1);
  return t1; 
}

/** 
 * Process an equality of the form a = b where a, and b are 
 * of the form x [i1:j1], or x for some non-concat/extract term x
 * 
 * @param node 
 */
void Slicer::processSimpleEquality(TNode node) {
  Assert(node.getKind() == kind::EQUAL);

  TNode t1 = addSimpleTerm(node[0]);
  TNode t2 = addSimpleTerm(node[1]);
  addEqualityEdge(t1, t2);
  
  // case 1: x [i1:j1] = x [i2:j2]
  if (node[0].getKind() == kind::BITVECTOR_EXTRACT &&
      node[1].getKind() == kind::BITVECTOR_EXTRACT &&
      node[0][0] == node[1][0] ) {
    // at this point the base already contains the slicing from the two extracts
    Base base = getBase(node[0][0]);
    
    uint32_t low1 = utils::getExtractLow(node[0]);
    uint32_t high1 = utils::getExtractHigh(node[0]); 
    uint32_t low2 = utils::getExtractLow(node[1]);
    uint32_t high2 = utils::getExtractHigh(node[1]); 

    Base new_base = base;
    uint32_t width = base.getSize(); 
    do {
      base = new_base; 
      Base base1 = base.extract(high1, low1);
      Base base2 = base.extract(high2, low2);
      
      base1 = base1 | base2; 

      new_base = base | base1.zeroExtend(width - high1 - 1).leftShift(low1)
                      | base2.zeroExtend(width - high2 - 1).leftShift(low2); 
    } while(new_base != base);
    updateBase(t1, new_base); 
  }

  // case 2 : x[i1:j1] = y[i2:j2]
  if (node[0].getKind() == kind::BITVECTOR_EXTRACT &&
      node[1].getKind() == kind::BITVECTOR_EXTRACT) {
    Base base1 = getBase(node[0][0]);
    Base base2 = getBase(node[1][0]);
    
  }
  
}


Base Slicer::getBase(TNode node) {
  Assert (d_bases.find(node) != d_bases.end());
  return d_bases[node]; 
}

void Slicer::updateBase(TNode node, const Base& base) {
  Assert (d_bases.find(node) != d_bases.end());
  d_bases[node] = d_bases[node].bitwiseOr(base); 
}


void Slicer::computeCoarsestBase() {
  Debug("bv-slicer") << "theory::bv::Slicer::computeCoarsestBase " << endl; 
  // queue of atomic terms whose base has changed
  std::vector<TNode> changedQueue;
  EqualityGraphIterator it = d_edgeMap.begin();
  // compute first slicing based on equalities
  for (; it != d_edgeMap.end(); ++it) {
    TNode t1 = (*it).first;
    std::list<TNode>* edges = (*it).second;
    Base resBase = getBase(t1);
    Debug("bv-slicer") << "  Processing node " << t1 << endl;
    Debug("bv-slicer") << "  with base       " << resBase.toString(2) << endl; 
    std::list<TNode>::iterator edge_it = edges->begin(); 
    
    for (; edge_it != edges->end(); ++ edge_it) {
      // compute slicing
      computeSlicing(t1, 
      Base base2 = getBase(*edge_it);
      resBase = resBase.bitwiseOr(base2); 
      Debug("bv-slicer") << "          edge " << *edge_it << endl;
      Debug("bv-slicer") << "     with base " << base2.toString(2) << endl; 

    }
    
    Debug("bv-slicer") << "New base         " << resBase.toString(2) << endl; 
    // update new bases
    for (; edge_it != edges->end(); ++ edge_it) {
      Base base2 = getBase(*edge_it);
      if (resBase != base2) {
        updateBase(*edge_it, resBase);
        changedQueue.push_back(*edge_it);
        Debug("bv-slicer") << "Adding to changedQueue " << *edge_it << endl; 
      } 
    }
    if (getBase(t1) != resBase) {
      updateBase(t1, resBase);
    }
  }
  
  Debug("bv-slicer") << "Propagating slicing " << endl;
  // propagate slicings 
  while(!changedQueue.empty()) {
    TNode node = changedQueue.back();
    changedQueue.pop_back(); 
    std::list<TNode>* edges = d_edgeMap[node];
    Base resBase = getBase(node);

    Debug("bv-slicer") << "  Processing node " << node << endl;
    Debug("bv-slicer") << "  with base       " << resBase.toString(2) << endl; 

    std::list<TNode>::iterator it = edges->begin();
    for (; it != edges->end(); ++it) {
      Base base1 = getBase(*it);
      Assert (base1.bitwiseOr(resBase) == resBase);
      Debug("bv-slicer") << "          edge " << *it << endl;
      Debug("bv-slicer") << "     with base " << base1.toString(2) << endl; 

      if (base1 != resBase) {
        updateBase(*it, base1.bitwiseOr(resBase));
        changedQueue.push_back(*it);
        Debug("bv-slicer") << "Adding to changedQueue " << *it << endl; 
      }
    }
  }
}

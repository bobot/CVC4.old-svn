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
  : d_equalities()
{}


void Slicer::splitEqualities(TNode node, std::vector<Node>& equalities) {
  Assert (node.getKind() == kind::EQUAL);
  TNode t1 = node[0];
  TNode t2 = node[1];

  
  Base base1(0); 
  if (t1.getKind() == kind::BITVECTOR_CONCAT) {
    unsigned size = 0; 
    for (int i = t1.getNumChildren(); i >= 0; --i) {
      size = size + utils::getSize(t1[i]);
      base1 = base1.setBit(size); 
    }
  }

  Base base2(0); 
  if (t2.getKind() == kind::BITVECTOR_CONCAT) {
    unsigned size = 0; 
    for (int i = t2.getNumChildren(); i >= 0; --i) {
      size = size + utils::getSize(t2[i]);
      base2 = base2.setBit(size); 
    }
  }

  Base resBase = base1.bitwiseOr(base2); 
  if (resBase != Base(0)) {
    // we split the equalities accodring to the base
    int last = 0; 
    for (unsigned i = 1; i < utils::getSize(t1); ++i) {
      if (resBase.isBitSet(i)) {
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
    processSimpleEquality(equalities[i]); 
  }
}


TNode Slicer::addSimpleTerm(TNode t1) {
  Base base1(0); 
  if (t1.getKind() == kind::BITVECTOR_EXTRACT) {
    unsigned low = utils::getExtractLow(t1);
    unsigned high = utils::getExtractHigh(t1);
    if (low != 0) {
      base1 = base1.setBit(low);
    }
    base1 = base1.setBit(high+1);
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

void Slicer::processSimpleEquality(TNode node) {
  Assert(node.getKind() == kind::EQUAL);
  d_equalities.push_back(node);

  TNode t1 = addSimpleTerm(node[0]);
  TNode t2 = addSimpleTerm(node[1]);

  addEqualityEdge(t1, t2);

}

void Slicer::addEqualityEdge(TNode t1, TNode t2) {
  Assert ((t1.getKind() | kind::BITVECTOR_CONCAT | kind::BITVECTOR_EXTRACT == 0) &&
          (t2.getKind() | kind::BITVECTOR_CONCAT | kind::BITVECTOR_EXTRACT == 0));
  
  if (d_edgeMap.find(t1) == d_edgeMap.end()) {
    d_edgeMap[t1] = new std::list<TNode>(); 
  }
  d_edgeMap[t1]->push_back(t2);

  if (d_edgeMap.find(t2) == d_edgeMap.end()) {
    d_edgeMap[t2] = new std::list<TNode>(); 
  }
  d_edgeMap[t2]->push_back(t1);
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
    // compute slicing 
    for (; edge_it != edges->end(); ++ edge_it) {
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

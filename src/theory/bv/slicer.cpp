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

/** 
 * Adds a cutPoint at Index i and splits the corresponding Splinter
 * 
 * @param i the index where the cut point will be introduced
 * @param sp the splinter pointer corresponding to the splinter to be sliced
 * @param low_splinter the resulting bottom part of the splinter
 * @param top_splinter the resulting top part of the splinter
 */
void Slice::split(Index i, SplinterPointer& sp, Splinter*& low_splinter, Splinter*& top_splinter) {
  Assert (!d_base.isCutPoint(i));
  d_base.sliceAt(i);
  
  Splinter* s = NULL;
  std::map<Index, Splinter*>::iterator it = d_splinters.begin();
  bool lt, gt; 
  for (; it != d_splinters.end(); ++it) {
    lt = (it->second)->getHigh() >= i;
    gt = (it->second)->getLow() <= i;
    if (gt && lt) {
      s = it->second;
      break; 
    }
  }
  
  Assert (s != NULL);

  sp = s->getPointer();
  Index low = s->getLow();
  Index high = s->getHigh();
  // creating the two splinter fragments 
  low_splinter = new Splinter(i, low);
  top_splinter = new Splinter(high, i+1);
  
  addSplinter(low, low_splinter);
  addSplinter(i+1, top_splinter); 
} 
 
void Slice::addSplinter(Index i, Splinter* sp) {
  Assert (i == sp->getLow() && sp->getHigh() < d_bitwidth);
  // free the memory associated with the previous splinter
  if (d_splinters.find(i) != d_splinters.end()) {
    delete d_splinters[i];
  }
  d_splinters[i] = sp;
}

void SliceBlock::computeBlockBase(std::vector<RootId>& queue)  {
  // at this point d_base has all the cut points in the individual slices
  for (unsigned row = 0; row < d_block.size(); ++row) {
    Slice* slice = d_block[row];
    const Base base = slice->getBase();
    Base new_cut_points = base.diffCutPoints(d_base);
    // use the cut points from the base to split the current slice
    for (unsigned i = 0; i < d_bitwidth; ++i) {
      if (new_cut_points.isCutPoint(i)) {
        // split this slice (this updates the slice's base)
        Splinter* bottom, *top = NULL;
        SplinterPointer sp;
        slice->split(i, sp, bottom, top);
          
        if (sp != Undefined) {
          // if we do need to split something else split it
          if (sp.term == d_rootId) {
            // TODO: special case
            Assert(false); 
          }
          Slice* slice = d_slicer->getSlice(sp);
          Splinter* s = d_slicer->getSplinter(sp);
          Index cutPoint = s->getLow() + i; 
          Splinter* new_bottom = new Splinter(cutPoint, s->getLow());
          Splinter* new_top = new Splinter(s->getHigh(), cutPoint + 1);
          new_bottom->setPointer(SplinterPointer(d_rootId, row, bottom->getLow()));
          new_top->setPointer(SplinterPointer(d_rootId, row, top->getLow()));

          slice->addSplinter(new_bottom->getLow(), new_bottom);
          slice->addSplinter(new_top->getLow(), new_top); 
          
          bottom->setPointer(SplinterPointer(sp.term, sp.row, new_bottom->getLow()));
          top->setPointer(SplinterPointer(sp.term, sp.row, new_top->getLow()));
          // update base for block
          d_slicer->getSliceBlock(sp)->sliceBaseAt(cutPoint);
          // add to queue of blocks that have changed base
          queue.push_back(sp.term); 
        }
      }
    }
  }
}
 
Slicer::Slicer()
  : d_simpleEqualities(),
    d_roots(),
    d_numRoots(0),
    d_nodeRootMap(),
    d_sliceSet()
{}

RootId Slicer::makeRoot(TNode n)  {
  Assert (n.getKind() != kind::BITVECTOR_EXTRACT && n.getKind() != kind::BITVECTOR_CONCAT);
  if (d_nodeRootMap.find(n) != d_nodeRootMap.end()) {
    return d_nodeRootMap[n];
  }
  RootId id = d_numRoots;
  d_numRoots++; 
  d_nodeRootMap[n] = id; 
  d_roots[id] = n;
  // initialize with an empty slice block
  d_rootBlocks[id] = new SliceBlock(id, utils::getSize(n), this); 
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
  for (unsigned i = 0; i < equalities.size(); ++i) {
    Debug("bv-slicer") << "    splitEqualities " << node << endl;
    registerSimpleEquality(equalities[i]); 
    d_simpleEqualities.push_back(equalities[i]);
  }
}

void Slicer::registerSimpleEquality(TNode eq) {
  Assert (eq.getKind() == kind::EQUAL);
  TNode a = eq[0];
  TNode b = eq[1];
 
  RootId id_a = registerTerm(a);
  RootId id_b = registerTerm(b);

  // TODO: special case a[ ] = a [ ]
  unsigned low_a = 0; 
  unsigned low_b = 0; 

  if (a.getKind() == kind::BITVECTOR_EXTRACT) {
    low_a  = utils::getExtractLow(a);
  }
  
  if (b.getKind() == kind::BITVECTOR_EXTRACT) {
    low_b  = utils::getExtractLow(b);
  }

  Slice* slice_a = makeSlice(a);
  Slice* slice_b = makeSlice(b); 

  SliceBlock* block_a = d_rootBlocks[id_a];
  SliceBlock* block_b = d_rootBlocks[id_b];

  uint32_t row_a = block_a->addSlice(slice_a);
  uint32_t row_b = block_b->addSlice(slice_b); 

  SplinterPointer sp_a = SplinterPointer(id_a, row_a, low_a);
  SplinterPointer sp_b = SplinterPointer(id_b, row_b, low_b); 

  slice_a->getSplinter(low_a)->setPointer(sp_b);
  slice_b->getSplinter(low_b)->setPointer(sp_a); 
}

Slice* Slicer::makeSlice(TNode node) {
  Assert (d_sliceSet.find(node) == d_sliceSet.end());
  
  Index bitwidth = utils::getSize(node); 
  Index low = 0;
  Index high = bitwidth -1 ;
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    low  = utils::getExtractLow(node);
    high = utils::getExtractHigh(node); 
  }
  Splinter* splinter = new Splinter(high, low);
  Slice* slice = new Slice(utils::getSize(node));
  slice->addSplinter(low, splinter);
  if (low != 0) {
    Splinter* bottom_splinter = new Splinter(low-1, 0);
    slice->addSplinter(0, bottom_splinter); 
  }
  if (high != bitwidth - 1) {
    Splinter* top_splinter = new Splinter(bitwidth - 1, high + 1);
    slice->addSplinter(high+1, top_splinter); 
  }
  return slice; 
}


RootId Slicer::registerTerm(TNode node) {
  if (node.getKind() == kind::BITVECTOR_EXTRACT ) {
    node = node[0];
    Assert (isRootTerm(node)); 
  }
  // setting up the data-structures for the root term
  RootId id = makeRoot(node);
  return id; 
}

bool Slicer::isRootTerm(TNode node) {
  Kind kind = node.getKind();
  return kind != kind::BITVECTOR_EXTRACT && kind != kind::BITVECTOR_CONCAT;
}

// Base Slicer::getBase(TNode node) {
//   Assert (d_bases.find(node) != d_bases.end());
//   return d_bases[node]; 
// }

// void Slicer::updateBase(TNode node, const Base& base) {
//   Assert (d_bases.find(node) != d_bases.end());
//   d_bases[node] = d_bases[node].bitwiseOr(base); 
// }


void Slicer::computeCoarsestBase() {
  Debug("bv-slicer") << "theory::bv::Slicer::computeCoarsestBase " << endl; 
  std::vector<RootId> queue;
  for (unsigned i = 0; i < d_rootBlocks.size(); ++i) {
    SliceBlock* block = d_rootBlocks[i];
    block->computeBlockBase(queue);
  }
  
  while (!queue.empty()) {
    // process split candidate
    RootId current = queue.back();
    queue.pop_back();
    SliceBlock* block = d_rootBlocks[current];
    block->computeBlockBase(queue); 
  }
  //Assert ( debugCheckBase()); 
}

// bool Slicer::debugCheckBase() {
  
// }




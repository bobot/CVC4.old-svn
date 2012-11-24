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

#include "cvc4_private.h"

#include <vector>
#include <list>
#include <ext/hash_map>
#include "expr/node.h"

#ifndef __CVC4__THEORY__BV__SLICER_BV_H
#define __CVC4__THEORY__BV__SLICER_BV_H


namespace CVC4 {

class Bitvector;

namespace theory {
namespace bv {

typedef uint32_t RootId;
typedef uint32_t SplinterId;
typedef uint32_t Index;

struct SplinterPointer {
  RootId term;
  Index start_index;
  uint32_t row; 
  SplinterPointer(RootId t, uint32_t r,  Index i) :
    term(t),
    row(r),
    start_index(i)
  {}
};

static const SplinterPointer Undefined = SplinterPointer(-1, -1, -1); 

class Splinter {
  // start and end indices in block 
  uint32_t d_low;
  uint32_t d_high;

  // keeps track of 
  SplinterPointer d_pointer; 

  Splinter(uint32_t high, uint32_t low) :
    d_lowlow),
    d_high(high),
    d_pointer(Undefined)
  {}

    
  void setPointer(SplinterPointer pointer) {
    Assert (d_pointer === Undefined);
    d_pointer = pointer; 
  }

  const SplinterPointer& getPointer() const {
    return d_pointer; 
  }
  const uint32_t getLow() { return d_low; }
  const uint32_t getHigh() {return d_high; }
};


class Slice {
  // map from the beginning of a splinter to the actual splinter id
  std::map<Index, Splinter*> d_splinters;
  Base d_base; 
  Slice()
    : d_splinters()
  {}
  void split(Index start, Index length);
  void addSplinter(Index start, Splinter* sp); 
  Splinter* getSplinter(Index start);
  Base getBase(); 
};


typedef CVC4::Bitvector Base; 

class Base {
  CVC4::Bitvector d_repr;
  uint32_t d_size; 
  Base(uint32_t size) :
    d_size(size) {
    Assert (size > 1);
    d_repr = Bitvector(size - 1, 0);
  }

  /** 
   * Marks the base by adding a cut between index and index + 1
   * 
   * @param index 
   */
  void sliceAt(Index index) {
    Assert (index < d_size - 1); 
    d_repr = d_repr.setBit(index); 
  }

  void sliceWith(const Base& other) {
    Assert (d_size == other.d_size); 
    d_repr = d_repr | other.d_repr; 
  }

  void getSlices(TNode root, std::vector<Node>& slices) {
    uint32_t index = 0; 
    for (uint32_t i = 0; i < d_size - 1; ++i) {
      uint32_t low = index;
      uint32_t high = i + 1;
      index = high;
      Node slice = utils::mkExtract(root, low, high);
      d_slices.push_back(slice); 
    }
  }

  bool isCutPoint(Index index) {
    return d_repr.isBitSet(); 
  }
}; 

class SliceBlock {
  std::vector<Slice*> d_block;
  Base d_base;
  uint32_t d_bitwidth; 
  SliceBlock(uint32_t bitwidth) :
    d_bitwidth(bitwidth)
  {}

  void addSlice(Slice* slice) {
    // update the base with the cut-points in the slice
    d_base.sliceWith(slice->getBase()); 
    d_block.push_back(slice); 
  }

  Slice& getSlice(unsigned index) {
    return d_block(index); 
  }

  void computeBlockBase(std::vector<SplinterPointer> queue) {
    // at this point d_base has all the cut points in the individual slices
    for (unsigned i = 0; i < d_block.size(); ++i) {
      Slice* slice = d_block[i];
      Base base = slice->getBase();
      Base new_cut_points = base.xor(d_base);
      // use the cut points from the base to split the current slice
      for (unsigned i = 0; i < d_bitwidth; ++i) {
        if (new_cut_points.isCutPoint(i)) {
          // split this slice
          Splinter* sp = slice->split(i);
          // potentially propagate cut to other root terms
          if (sp->getPointer != Undefied)  {
            queue.push_back(sp->getPointer()); 
          }
          
      }
    }
  }
};

typedef __gnu_cxx::hash_map<TNode, RootId, TNodeHashFunction> NodeRootIdMap;
typedef std::vector<TNode> Roots; 

typedef __gnu_cxx::hash_map<TNode, SplinterId, TNodeHashFunction> NodeSplinterIdMap;
typedef std::vector<Splinter*> Splinters;

typedef std::vector<SliceBlock*> SliceBlocks;

class Slicer {
  std::vector<TNode> d_simpleEqualities;
  Roots d_roots;
  uint32_t d_numRoots; 
  NodeRootIdMap d_nodeRootMap;
  /* Indexed by Root Id */
  SliceBlocks d_rootBlocks; 
  NodeSplinterIdMap d_nodeSplinterMap;
  Splinterd d_splinters;
  uint32_t d_numSplinters; 
  
private:
  

public:
  Slicer();
  void computeCoarsestBase();
  /** 
   * Takes an equality that is of the following form:
   *          a1 a2 ... an = b1 b2 ... bk
   * where ai, and bi are either variables or extracts over variables,
   * and consecutive extracts have been merged. 
   * 
   * @param node 
   */
  void processEquality(TNode node); 
private:
  void processSimpleEquality(TNode node);
  void splitEqualities(TNode node, std::vector<Node>& equalities);
  TNode addSimpleTerm(TNode t);
  TNode getRoot(RootId id) {return d_roots[id]; }
  RootId getRootId(TNode node) {
    Assert (d_nodeRootMap.find(node) != d_nodeRootMap.end());
    return d_nodeRootMap(node); 
  }

  RootId makeRoot(TNode n); 
  
  

}; /* Slicer class */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__SLICER_BV_H */

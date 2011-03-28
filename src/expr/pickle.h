#ifndef __CVC4__PICKLE_H
#define __CVC4__PICKLE_H

#include <sstream>
#include <deque>
#include <stack>

namespace CVC4{

namespace expr {
namespace pickle {

const unsigned NBITS_BLOCK = 32;
const unsigned NBITS_KIND = __CVC4__EXPR__NODE_VALUE__NBITS__KIND;
const unsigned NBITS_NCHILDREN = __CVC4__EXPR__NODE_VALUE__NBITS__NCHILDREN;
const unsigned NBITS_CONSTBLOCKS = 32;



struct BlockHeader {
  unsigned d_kind          : NBITS_KIND;
};

struct BlockHeaderOperator {
  unsigned d_kind          : NBITS_KIND;
  unsigned d_nchildren     : NBITS_NCHILDREN;
  unsigned                 : NBITS_BLOCK - (NBITS_KIND + NBITS_NCHILDREN);
};

struct BlockHeaderConstant {
  unsigned d_kind          : NBITS_KIND;
  unsigned d_constblocks   : NBITS_BLOCK - NBITS_KIND;
};

struct BlockHeaderVariable {
  unsigned d_kind          : NBITS_KIND;
  unsigned                 : NBITS_BLOCK - NBITS_KIND;
};

struct BlockBody  {
  unsigned d_data          : NBITS_BLOCK;
};

union Block {
  BlockHeader d_header;
  BlockHeaderConstant d_headerConstant;
  BlockHeaderOperator d_headerOperator;
  BlockHeaderVariable d_headerVariable;

  BlockBody d_body;
};

typedef std::deque<Block> BlockDeque;

class Pickler {
private:
  typedef std::stack<Node> NodeStack;

public:
  Pickler() {}

  virtual void append(Block b) = 0;
  void operator << (Block b) {
    append(b);
  }

  void pickleNode(TNode n){
    pickleNode(*this, n);
  }

private:

  static void pickleNode(Pickler& p, TNode n);
  static void pickleVariable(Pickler& p, TNode n);
  static void pickleConstant(Pickler& p, TNode n);
  static void pickleString(Pickler& p, Kind k, const std::string& s);

public:
  static Node remakeNode(BlockDeque& blocks);

private:
  static Node handleOperator(Kind k, uint32_t nchildren, BlockDeque& blocks, NodeStack& stack);
  static Node handleConstant(Kind k, uint32_t nblocks, BlockDeque& blocks);
  static std::string handleString(uint32_t nblocks, BlockDeque& blocks);
  static Node handleVariable(Kind k, BlockDeque& blocks);
};


class DequePickler : public Pickler {
private:
  BlockDeque d_blockQueue;
public:
  void append(Block b){
    enqueue(b);
  }
  void enqueue(Block b) {
    d_blockQueue.push_back(b);
  }

  Block dequeue() {
    Block b = d_blockQueue.front();
    d_blockQueue.pop_front();
    return b;
  }

  void swap(BlockDeque& bq){
    d_blockQueue.swap(bq);
  }
};

class StringStreamPickler : public Pickler {
private:
  std::ostringstream *d_s;

public:
  StringStreamPickler(std::ostringstream *s) : d_s(s) {}
  void append(Block b);

  std::ostringstream* getStream() { return d_s; }
}; /* end StringPickler */

std::string pickleTest(TNode n);

} /* namespace pickle */
} /* namespace expr */

} /* namespace CVC4 */

#endif /* __CVC4__PICKLE_H */

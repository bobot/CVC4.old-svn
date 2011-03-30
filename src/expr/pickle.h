#ifndef __CVC4__PICKLE_H
#define __CVC4__PICKLE_H

#include <sstream>
#include <deque>
#include <stack>
#include <map>

#include "expr/expr.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/expr_manager.h"
#include "expr/variable_type_map.h"
#include "expr/kind.h"
#include "expr/metakind.h"

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


class Pickle {
private:
  typedef std::deque<Block> BlockDeque;
  BlockDeque d_blocks;

public:
  Pickle& operator << (Block b) {
    enqueue(b);
    return (*this);
  }

  std::string toString() const;

  void enqueue(Block b) {
    d_blocks.push_back(b);
  }

  Block dequeue() {
    Block b = d_blocks.front();
    d_blocks.pop_front();
    return b;
  }

  bool empty() const { return d_blocks.empty(); }
  uint32_t size() const { return d_blocks.size(); }

  void swap(Pickle& other){
    d_blocks.swap(other.d_blocks);
  }

  void writeToStringStream(std::ostringstream& oss) const;
};

class Pickler {
protected:
  virtual uint64_t variableToMap(uint64_t x) const { return x; }
  virtual uint64_t variableFromMap(uint64_t x) const { return x; }

private:
  typedef std::stack<Node> NodeStack;
  NodeStack d_stack;

  Pickle d_current;

  ExprManager* d_em;
  
  NodeManager* d_nm;

public:
  Pickler(ExprManager* em) :
    d_em(em)
  { d_nm = d_em->getNodeManager(); }

  /**
   * Constructs a new Pickle of the node n.
   * n must be a node allocated in the node manager specified at initialization time.
   * The new pickle has variables mapped using the VariableIDMap provided at
   * initialization.
   * TODO: Fix comment
   */
  void toPickle(Expr e, Pickle& p);

  /**
   * Constructs a node from a Pickle.
   * This destroys the contents of the Pickle.
   * The node is created in the NodeManager getNM();
   * TODO: Fix comment
   */
  Expr fromPickle(Pickle& p);

private:
  bool atDefaultState(){
    return d_stack.empty() && d_current.empty();
  }

  /* Helper functions for toPickle */
  void toCaseNode(TNode n);
  void toCaseVariable(TNode n);
  void toCaseConstant(TNode n);
  void toCaseOperator(TNode n);
  void toCaseString(Kind k, const std::string& s);


  /* Helper functions for toPickle */
  Node fromCaseOperator(Kind k, uint32_t nchildren);
  Node fromCaseConstant(Kind k, uint32_t nblocks);
  std::string fromCaseString(uint32_t nblocks);
  Node fromCaseVariable(Kind k);

public:
  static void debugPickleTest(Expr e);
};

class MapPickler : public Pickler {
public:
  typedef std::map<uint64_t, uint64_t> VarMap;

private:
  const VarMap& d_toMap;
  const VarMap& d_fromMap;

public:
  MapPickler(ExprManager* em, const VarMap& to, const VarMap& from):
    Pickler(em), d_toMap(to), d_fromMap(from)
  { }

protected:
  static uint64_t map(const VarMap& map, uint64_t key){
    VarMap::const_iterator i = map.find(key);
    Assert(i != map.end());
    return i->second;
  }

  virtual uint64_t variableToMap(uint64_t x) const {
    return map(d_toMap, x);
  }
  virtual uint64_t variableFromMap(uint64_t x) const {
    return map(d_fromMap, x);
  }
};

} /* namespace pickle */
} /* namespace expr */

} /* namespace CVC4 */

#endif /* __CVC4__PICKLE_H */

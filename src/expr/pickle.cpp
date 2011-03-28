/*********************                                                        */
/*! \file pickle.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
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

#include <iostream>
#include <sstream>
#include <string>

#include "expr/expr.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/variable_type_map.h"
#include "util/Assert.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "pickle.h"

/* Format
 *
 * Block size = 64 bits.
 *
 * First 8 bits: __CVC4__EXPR__NODE_VALUE__NBITS__KIND = 8
 * 
 * If metakind of kind given by first section is
 * 
 * > Constants
 *   - Remaining bits of the block tell number of data blocks
 *     required. (i.e. 64-8=56 bits)
 *   - Required number of data blocks follow.
 * > Variables
 *   - In this block, nothing more to store really, maybe store
 *     the ID
 *   - Have the address of this node stored in the next block
 * > Operators and Parameterized Operators
 *   - Add child nodes (in which order?)
 *   - __CVC4__EXPR__NODE_VALUE__NBITS__NCHILDREN = 16 bits, 
 *     the number of blocks to follow.
 *   - Remaning 48 bits are empty
 *   - If parameterized a node follows representing the operator
 */


namespace CVC4{

namespace expr {
namespace pickle {

Block mkBlockBody4Chars(char a, char b, char c, char d){
  Block newBody;
  newBody.d_body.d_data = (a << 24) | (b << 16) | (c << 8) | d;
  return newBody;
}

char getCharBlockBody(BlockBody body, int i){
  Assert(0 <= i && i <= 3);

  switch(i){
  case 0: return (body.d_data & 0xff000000) >> 24;
  case 1: return (body.d_data & 0x00ff0000) >> 16;
  case 2: return (body.d_data & 0x0000ff00) >> 8;
  case 3: return (body.d_data & 0x000000ff);
  default:
    Unreachable();
  }
  return '\0';
}

Block mkBlockBody(unsigned data){
  Block newBody;
  newBody.d_body.d_data = data;
  return newBody;
}

Block mkOperatorHeader(Kind k, unsigned numChildren){
  Block newHeader;
  newHeader.d_headerOperator.d_kind = k;
  newHeader.d_headerOperator.d_nchildren = numChildren;
  return newHeader;
}

Block mkVariableHeader(Kind k){
  Block newHeader;
  newHeader.d_header.d_kind = k;
  return newHeader;
}

Block mkConstantHeader(Kind k, unsigned numBlocks){
  Block newHeader;
  newHeader.d_headerConstant.d_kind = k;
  newHeader.d_headerConstant.d_constblocks = numBlocks;
  return newHeader;
}


void Pickler::pickleNode(Pickler &p, TNode n)
{
  Kind k = n.getKind();
  kind::MetaKind m = metaKindOf(k);
  if(m == kind::metakind::CONSTANT) {
    // TODO: set this before appending
    // TODO: test size before appending
    pickleConstant(p, n);
  } else if(m == kind::metakind::VARIABLE) {
    pickleVariable(p, n);
  } else {
    Assert(m == kind::metakind::PARAMETERIZED || m == kind::metakind::OPERATOR);
    if(m == kind::metakind::PARAMETERIZED) {
      pickleNode(p, n.getOperator());
    }
    for(TNode::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
      pickleNode(p, *i);
    }
    p << mkOperatorHeader(k, n.getNumChildren());
  }
}

void Pickler::pickleVariable(Pickler& p, TNode n){
  Kind k = n.getKind();
  Assert(metaKindOf(k) == kind::metakind::VARIABLE);

  const NodeValue* nv = n.d_nv;
  uint64_t asInt = (uint64_t)nv; //TODO: eeeekkkk
  uint32_t firstHalf = asInt >> 32;
  uint32_t secondHalf = asInt;


  // TODO: replace with NodeValue*
  p << mkVariableHeader(k);
  p << mkBlockBody(firstHalf);
  p << mkBlockBody(secondHalf);
}
void Pickler::pickleConstant(Pickler& p, TNode n){
  Kind k = n.getKind();
  Assert(metaKindOf(k) == kind::metakind::CONSTANT);
  switch(k){
  case kind::CONST_BOOLEAN:
    p << mkConstantHeader(k, 1);
    p << mkBlockBody(n.getConst<bool>());
    break;
  case kind::CONST_INTEGER:
  case kind::CONST_RATIONAL:{
    std::string asString;
    if(k == kind::CONST_INTEGER){
      const Integer& i = n.getConst<Integer>();
      asString = i.toString(16);
    }else {
      Assert(k == kind::CONST_RATIONAL);
      const Rational& q = n.getConst<Rational>();
      asString = q.toString(16);
    }
    pickleString(p, k, asString);
    break;
  }
  default:
    Unimplemented();
  }
}

void Pickler::pickleString(Pickler& p, Kind k, const std::string& s){
  p << mkConstantHeader(k, s.size());

  unsigned size = s.size();
  unsigned i;
  for(i = 0; i + 4 <= size; i+= 4){
    p << mkBlockBody4Chars(s[i + 0], s[i + 1],s[i + 2], s[i + 3]);
  }
  switch(size % 4){
  case 0: break;
  case 1: p << mkBlockBody4Chars(s[i + 0], '\0','\0', '\0'); break;
  case 2: p << mkBlockBody4Chars(s[i + 0], s[i + 1], '\0', '\0'); break;
  case 3: p << mkBlockBody4Chars(s[i + 0], s[i + 1],s[i + 2], '\0'); break;
  default:
    Unreachable();
  }

}

void StringStreamPickler::append(Block b){
  Assert(sizeof(b) * 8 == NBITS_BLOCK);
  Debug("pickle") << "<< :" << sizeof(b) << " : " <<  b.d_body.d_data << std::endl;
  d_s->write( (char *) &b, sizeof(b) );
}


std::string pickleTest(TNode n)
{
  DequePickler dp;
  BlockDeque queue;
  dp.pickleNode(n);
  dp.swap(queue);

  Node afterPickle = Pickler::remakeNode(queue);
  Debug("pickle") << "before " << n << std::endl;
  Debug("pickle") << "after " << afterPickle << std::endl;
  Assert(n == afterPickle);

  std::ostringstream s(std::ios_base::binary);
  StringStreamPickler p(&s);
  p.pickleNode(n);
  std::ostringstream* dfjk= p.getStream();
  return dfjk -> str();
}


Node Pickler::remakeNode(BlockDeque& blocks){
  NodeStack stack;

  while(!blocks.empty()){
    Block front = blocks.front();
    blocks.pop_front();

    Kind k = (Kind)front.d_header.d_kind;
    kind::MetaKind m = metaKindOf(k);

    Node result = Node::null();
    switch(m){
    case kind::metakind::VARIABLE:
      result = handleVariable(k, blocks);
      break;
    case kind::metakind::CONSTANT:
      result = handleConstant(k, front.d_headerConstant.d_constblocks, blocks);
      break;
    case kind::metakind::OPERATOR:
    case kind::metakind::PARAMETERIZED:
      result = handleOperator(k, front.d_headerOperator.d_nchildren, blocks, stack);
      break;
    default:
      Unimplemented();
    }
    Assert(result != Node::null());
    stack.push(result);
  }
  Assert(stack.size() == 1);
  Node res = stack.top();
  return res;
}

Node Pickler::handleVariable(Kind k, BlockDeque& blocks){
  Assert(metaKindOf(k) == kind::metakind::VARIABLE);

  Block firstHalf = blocks.front();
  blocks.pop_front();

  Block secondHalf = blocks.front();
  blocks.pop_front();

  uint64_t asInt = firstHalf.d_body.d_data;
  asInt = asInt << 32;
  asInt = asInt | (secondHalf.d_body.d_data);

  NodeValue* nv = (NodeValue*) asInt;
  Node fromNodeValue(nv);

  Assert(fromNodeValue.getKind() == k);

  return fromNodeValue;
}

Node Pickler::handleConstant(Kind k, uint32_t constblocks,  BlockDeque& blocks){
  switch(k){
  case kind::CONST_BOOLEAN:{
    Assert(constblocks == 1);
    Block val = blocks.front();
    blocks.pop_front();

    bool b= val.d_body.d_data;
    return NodeManager::currentNM()->mkConst<bool>(b);
  }
  case kind::CONST_INTEGER:
  case kind::CONST_RATIONAL:{
    std::string s = handleString(constblocks, blocks);
    if( k == kind::CONST_INTEGER ){
      Integer i(s, 16);
      return NodeManager::currentNM()->mkConst<Integer>(i);
    }else{
      Rational q(s, 16);
      return NodeManager::currentNM()->mkConst<Rational>(q);
    }
  }
  default:
    Unimplemented();
    return Node::null();
  }
}

std::string Pickler::handleString(uint32_t size,  BlockDeque& blocks){
  std::stringstream ss;
  unsigned i;
  for(i = 0; i + 4 <= size; i+= 4){
    Block front = blocks.front();
    blocks.pop_front();
    BlockBody body = front.d_body;

    ss << getCharBlockBody(body,0)
       << getCharBlockBody(body,1)
       << getCharBlockBody(body,2)
       << getCharBlockBody(body,3);
  }
  Assert(i == size - (size%4) );
  if(size % 4 != 0){
    Block front = blocks.front();
    blocks.pop_front();
    BlockBody body = front.d_body;
    switch(size % 4){
    case 1:
      ss << getCharBlockBody(body,0);
      break;
    case 2:
      ss << getCharBlockBody(body,0)
         << getCharBlockBody(body,1);
      break;
    case 3:
      ss << getCharBlockBody(body,0)
         << getCharBlockBody(body,1)
         << getCharBlockBody(body,2);
      break;
    default:
      Unreachable();
    }
  }
  return ss.str();
}
Node Pickler::handleOperator(Kind k, uint32_t nchildren, BlockDeque& blocks, NodeStack& stack){
  kind::MetaKind m = metaKindOf(k);
  bool parameterized = (m == kind::metakind::PARAMETERIZED);
  uint32_t npops = nchildren + (parameterized? 1 : 0);

  NodeStack aux;
  while(npops > 0){
    Assert(!stack.empty());
    Node top = stack.top();
    aux.push(top);
    stack.pop();
    --npops;
  }

  NodeBuilder<> nb(k);
  while(!aux.empty()){
    Node top = aux.top();
    nb << top;
    aux.pop();
  }

  return nb;
}


} /* namespace pickle */
} /* namespace expr */

} /* namespace CVC4 */

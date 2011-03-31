/*********************                                                        */
/*! \file pickle.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: taking, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is a "pickler" for expressions
 **
 ** This is a "pickler" for expressions.  It produces a binary
 ** serialization of an expression that can be converted back
 ** into an expression in the same or another ExprManager.
 **/

#include <iostream>
#include <sstream>
#include <string>

#include "expr/expr.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/node_value.h"
#include "expr/expr_manager_scope.h"
#include "expr/variable_type_map.h"
#include "util/Assert.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/pickle.h"

namespace CVC4 {
namespace expr {
namespace pickle {

static Block mkBlockBody4Chars(char a, char b, char c, char d) {
  Block newBody;
  newBody.d_body.d_data = (a << 24) | (b << 16) | (c << 8) | d;
  return newBody;
}

static char getCharBlockBody(BlockBody body, int i) {
  Assert(0 <= i && i <= 3);

  switch(i) {
  case 0: return (body.d_data & 0xff000000) >> 24;
  case 1: return (body.d_data & 0x00ff0000) >> 16;
  case 2: return (body.d_data & 0x0000ff00) >> 8;
  case 3: return (body.d_data & 0x000000ff);
  default:
    Unreachable();
  }
  return '\0';
}

static Block mkBlockBody(unsigned data) {
  Block newBody;
  newBody.d_body.d_data = data;
  return newBody;
}

static Block mkOperatorHeader(Kind k, unsigned numChildren) {
  Block newHeader;
  newHeader.d_headerOperator.d_kind = k;
  newHeader.d_headerOperator.d_nchildren = numChildren;
  return newHeader;
}

static Block mkVariableHeader(Kind k) {
  Block newHeader;
  newHeader.d_header.d_kind = k;
  return newHeader;
}

static Block mkConstantHeader(Kind k, unsigned numBlocks) {
  Block newHeader;
  newHeader.d_headerConstant.d_kind = k;
  newHeader.d_headerConstant.d_constblocks = numBlocks;
  return newHeader;
}

void Pickle::writeToStringStream(std::ostringstream& oss) const {
  BlockDeque::const_iterator i = d_blocks.begin(), end = d_blocks.end();
  for(; i != end; ++i) {
    Block b = *i;
    Assert(sizeof(b) * 8 == NBITS_BLOCK);
    oss << b.d_body.d_data << " ";
  }
}

std::string Pickle::toString() const {
  std::ostringstream oss;
  oss.flags(std::ios::oct | std::ios::showbase);
  writeToStringStream(oss);
  return oss.str();
}

void Pickler::toPickle(Expr e, Pickle& p) throw (PicklingException) {
  Assert(e.getExprManager() == d_em);
  Assert(atDefaultState());

  try{
    d_current.swap(p);
    toCaseNode(e.getTNode());
    d_current.swap(p);
  }catch(PicklingException& p){
    d_current = Pickle();
    Assert(atDefaultState());
    throw p;
  }

  Assert(atDefaultState());
}

void Pickler::toCaseNode(TNode n) {
  Debug("pickler") << "toCaseNode: " << n << std::endl;
  Kind k = n.getKind();
  kind::MetaKind m = metaKindOf(k);
  switch(m) {
  case kind::metakind::CONSTANT:
    toCaseConstant(n);
    break;
  case kind::metakind::VARIABLE:
    toCaseVariable(n);
    break;
  case kind::metakind::OPERATOR:
  case kind::metakind::PARAMETERIZED:
    toCaseOperator(n);
    break;
  default:
    Unimplemented();
  }
}

void Pickler::toCaseOperator(TNode n) throw (PicklingException) {
  Kind k = n.getKind();
  kind::MetaKind m = metaKindOf(k);
  Assert(m == kind::metakind::PARAMETERIZED || m == kind::metakind::OPERATOR);
  if(m == kind::metakind::PARAMETERIZED) {
    toCaseNode(n.getOperator());
  }
  for(TNode::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
    toCaseNode(*i);
  }
  d_current << mkOperatorHeader(k, n.getNumChildren());
}

void Pickler::toCaseVariable(TNode n) throw (PicklingException){
  Kind k = n.getKind();
  Assert(metaKindOf(k) == kind::metakind::VARIABLE);

  const NodeValue* nv = n.d_nv;
  uint64_t asInt = reinterpret_cast<uint64_t>(nv);
  uint64_t mapped = variableToMap(asInt);

  uint32_t firstHalf = mapped >> 32;
  uint32_t secondHalf = mapped & 0xffffffff;

  d_current << mkVariableHeader(k);
  d_current << mkBlockBody(firstHalf);
  d_current << mkBlockBody(secondHalf);
}


void Pickler::toCaseConstant(TNode n) {
  Kind k = n.getKind();
  Assert(metaKindOf(k) == kind::metakind::CONSTANT);
  switch(k) {
  case kind::CONST_BOOLEAN:
    d_current << mkConstantHeader(k, 1);
    d_current << mkBlockBody(n.getConst<bool>());
    break;
  case kind::CONST_INTEGER:
  case kind::CONST_RATIONAL: {
    std::string asString;
    if(k == kind::CONST_INTEGER) {
      const Integer& i = n.getConst<Integer>();
      asString = i.toString(16);
    } else {
      Assert(k == kind::CONST_RATIONAL);
      const Rational& q = n.getConst<Rational>();
      asString = q.toString(16);
    }
    toCaseString(k, asString);
    break;
  }
  default:
    Unimplemented();
  }
}

void Pickler::toCaseString(Kind k, const std::string& s) {
  d_current << mkConstantHeader(k, s.size());

  unsigned size = s.size();
  unsigned i;
  for(i = 0; i + 4 <= size; i += 4) {
    d_current << mkBlockBody4Chars(s[i + 0], s[i + 1],s[i + 2], s[i + 3]);
  }
  switch(size % 4) {
  case 0: break;
  case 1: d_current << mkBlockBody4Chars(s[i + 0], '\0','\0', '\0'); break;
  case 2: d_current << mkBlockBody4Chars(s[i + 0], s[i + 1], '\0', '\0'); break;
  case 3: d_current << mkBlockBody4Chars(s[i + 0], s[i + 1],s[i + 2], '\0'); break;
  default:
    Unreachable();
  }

}

void Pickler::debugPickleTest(Expr e) {

  //ExprManager *em = e.getExprManager();
  //Expr e1 = mkVar("x", makeType());
  //return ;

  Pickler pickler(e.getExprManager());

  Pickle p;
  pickler.toPickle(e, p);

  uint32_t size = p.size();
  std::string str = p.toString();

  Expr from = pickler.fromPickle(p);
  ExprManagerScope ems(e);

  Debug("pickle") << "before: " << e << std::endl;
  Debug("pickle") << "after: " << from.getNode() << std::endl;
  Debug("pickle") << "pickle: (oct) "<< size << " " << str.length() << " " << str << std::endl;

  Assert(p.empty());
  Assert(e == from);
}

Expr Pickler::fromPickle(Pickle& p) {
  Assert(atDefaultState());

  d_current.swap(p);

  while(!d_current.empty()) {
    Block front = d_current.dequeue();

    Kind k = (Kind)front.d_header.d_kind;
    kind::MetaKind m = metaKindOf(k);

    Node result = Node::null();
    switch(m) {
    case kind::metakind::VARIABLE:
      result = fromCaseVariable(k);
      break;
    case kind::metakind::CONSTANT:
      result = fromCaseConstant(k, front.d_headerConstant.d_constblocks);
      break;
    case kind::metakind::OPERATOR:
    case kind::metakind::PARAMETERIZED:
      result = fromCaseOperator(k, front.d_headerOperator.d_nchildren);
      break;
    default:
      Unimplemented();
    }
    Assert(result != Node::null());
    d_stack.push(result);
  }

  Assert(d_current.empty());
  Assert(d_stack.size() == 1);
  Node res = d_stack.top();
  d_stack.pop();

  Assert(atDefaultState());

  return d_nm->toExpr(res);
}

Node Pickler::fromCaseVariable(Kind k) {
  Assert(metaKindOf(k) == kind::metakind::VARIABLE);

  Block firstHalf = d_current.dequeue();
  Block secondHalf = d_current.dequeue();

  uint64_t asInt = firstHalf.d_body.d_data;
  asInt = asInt << 32;
  asInt = asInt | (secondHalf.d_body.d_data);

  uint64_t mapped = variableFromMap(asInt);

  NodeValue* nv = reinterpret_cast<NodeValue*>(mapped);
  Node fromNodeValue(nv);

  Assert(fromNodeValue.getKind() == k);

  return fromNodeValue;
}

Node Pickler::fromCaseConstant(Kind k, uint32_t constblocks) {
  switch(k) {
  case kind::CONST_BOOLEAN: {
    Assert(constblocks == 1);
    Block val = d_current.dequeue();

    bool b= val.d_body.d_data;
    return d_nm->mkConst<bool>(b);
  }
  case kind::CONST_INTEGER:
  case kind::CONST_RATIONAL: {
    std::string s = fromCaseString(constblocks);
    if(k == kind::CONST_INTEGER) {
      Integer i(s, 16);
      return d_nm->mkConst<Integer>(i);
    } else {
      Rational q(s, 16);
      return d_nm->mkConst<Rational>(q);
    }
  }
  default:
    Unimplemented();
    return Node::null();
  }
}

std::string Pickler::fromCaseString(uint32_t size) {
  std::stringstream ss;
  unsigned i;
  for(i = 0; i + 4 <= size; i += 4) {
    Block front = d_current.dequeue();
    BlockBody body = front.d_body;

    ss << getCharBlockBody(body,0)
       << getCharBlockBody(body,1)
       << getCharBlockBody(body,2)
       << getCharBlockBody(body,3);
  }
  Assert(i == size - (size%4) );
  if(size % 4 != 0) {
    Block front = d_current.dequeue();
    BlockBody body = front.d_body;
    switch(size % 4) {
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

Node Pickler::fromCaseOperator(Kind k, uint32_t nchildren) {
  kind::MetaKind m = metaKindOf(k);
  bool parameterized = (m == kind::metakind::PARAMETERIZED);
  uint32_t npops = nchildren + (parameterized? 1 : 0);

  NodeStack aux;
  while(npops > 0) {
    Assert(!d_stack.empty());
    Node top = d_stack.top();
    aux.push(top);
    d_stack.pop();
    --npops;
  }

  NodeBuilder<> nb(d_nm, k);
  while(!aux.empty()) {
    Node top = aux.top();
    nb << top;
    aux.pop();
  }

  return nb;
}


}/* CVC4::expr::pickle namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */

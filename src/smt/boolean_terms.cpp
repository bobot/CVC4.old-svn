/*********************                                                        */
/*! \file boolean_terms.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
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

#include "smt/boolean_terms.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "theory/model.h"
#include "expr/kind.h"
#include <string>
#include <algorithm>

using namespace std;
using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

const Datatype& BooleanTermConverter::booleanTermsConvertDatatype(const Datatype& dt) throw() {
  return dt;
  // boolean terms not supported in datatypes, yet

  Debug("boolean-terms") << "booleanTermsConvertDatatype: considering " << dt.getName() << endl;
  for(Datatype::const_iterator c = dt.begin(); c != dt.end(); ++c) {
    TypeNode t = TypeNode::fromType((*c).getConstructor().getType());
    for(TypeNode::const_iterator a = t.begin(); a != t.end(); ++a) {
      if((*a).isBoolean()) {
        Datatype newDt(dt.getName() + "'");
        Debug("boolean-terms") << "found a Boolean arg in constructor " << (*c).getName() << endl;
        for(c = dt.begin(); c != dt.end(); ++c) {
          DatatypeConstructor ctor((*c).getName() + "'", (*c).getTesterName() + "'");
          t = TypeNode::fromType((*c).getConstructor().getType());
          for(DatatypeConstructor::const_iterator a = (*c).begin(); a != (*c).end(); ++a) {
            if((*a).getType().getRangeType().isBoolean()) {
              ctor.addArg((*a).getName() + "'", NodeManager::currentNM()->mkBitVectorType(1).toType());
            } else {
              Type argType = (*a).getType().getRangeType();
              if(argType.isDatatype() && DatatypeType(argType).getDatatype() == dt) {
                ctor.addArg((*a).getName() + "'", DatatypeSelfType());
              } else {
                ctor.addArg((*a).getName() + "'", argType);
              }
            }
          }
          newDt.addConstructor(ctor);
        }
        DatatypeType newDtt = NodeManager::currentNM()->toExprManager()->mkDatatypeType(newDt);
        const Datatype& newD = newDtt.getDatatype();
        for(c = dt.begin(); c != dt.end(); ++c) {
          Debug("boolean-terms") << "constructor " << (*c).getConstructor() << ":" << (*c).getConstructor().getType() << " made into " << newD[(*c).getName() + "'"].getConstructor() << ":" << newD[(*c).getName() + "'"].getConstructor().getType() << endl;
          d_booleanTermCache[make_pair(Node::fromExpr((*c).getConstructor()), false)] = Node::fromExpr(newD[(*c).getName() + "'"].getConstructor());
          d_booleanTermCache[make_pair(Node::fromExpr((*c).getTester()), false)] = Node::fromExpr(newD[(*c).getName() + "'"].getTester());
          for(DatatypeConstructor::const_iterator a = (*c).begin(); a != (*c).end(); ++a) {
            d_booleanTermCache[make_pair(Node::fromExpr((*a).getSelector()), false)] = Node::fromExpr(newD[(*c).getName() + "'"].getSelector((*a).getName() + "'"));
          }
        }
        return newD;
      }
    }
  }
  return dt;
}/* BooleanTermConverter::booleanTermsConvertDatatype() */

Node BooleanTermConverter::rewriteBooleanTerms(TNode top, bool boolParent) throw() {
  Debug("boolean-terms") << "rewriteBooleanTerms: " << top << " - boolParent=" << boolParent << endl;

  BooleanTermCache::iterator i = d_booleanTermCache.find(make_pair<Node, bool>(top, boolParent));
  if(i != d_booleanTermCache.end()) {
    return (*i).second.isNull() ? Node(top) : (*i).second;
  }

  Kind k = top.getKind();
  kind::MetaKind mk = top.getMetaKind();

  NodeManager* nm = NodeManager::currentNM();

  if(!boolParent && top.getType().isBoolean()) {
    Node one = nm->mkConst(BitVector(1u, 1u));
    Node zero = nm->mkConst(BitVector(1u, 0u));
    // still need to rewrite e.g. function applications over boolean
    Node topRewritten = rewriteBooleanTerms(top, true);
    Node n = nm->mkNode(kind::ITE, topRewritten, one, zero);
    Debug("boolean-terms") << "constructed ITE: " << n << endl;
    return n;
  }

  if(mk == kind::metakind::CONSTANT) {
    Assert(k != kind::STORE_ALL, "array store-all not yet supported by Boolean-term conversion");
    return top;
  } else if(mk == kind::metakind::VARIABLE) {
    TypeNode t = top.getType();
    if(t.isFunction()) {
      for(unsigned i = 0; i < t.getNumChildren() - 1; ++i) {
        if(t[i].isBoolean()) {
          vector<TypeNode> argTypes = t.getArgTypes();
          replace(argTypes.begin(), argTypes.end(), t[i], nm->mkBitVectorType(1));
          TypeNode newType = nm->mkFunctionType(argTypes, t.getRangeType());
          Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()) + "_bt",
                                newType, "a function introduced by Boolean-term conversion",
                                NodeManager::SKOLEM_EXACT_NAME);
          Debug("boolean-terms") << "constructed func: " << n << " of type " << newType << endl;
          top.setAttribute(BooleanTermAttr(), n);
          d_booleanTermCache[make_pair(top, boolParent)] = n;
          return n;
        }
      }
    } else if(t.isArray()) {
      TypeNode indexType = t.getArrayIndexType();
      TypeNode constituentType = t.getArrayConstituentType();
      bool rewrite = false;
      if(indexType.isBoolean()) {
        indexType = nm->mkBitVectorType(1);
        rewrite = true;
      }
      if(constituentType.isBoolean()) {
        constituentType = nm->mkBitVectorType(1);
        rewrite = true;
      }
      if(rewrite) {
        TypeNode newType = nm->mkArrayType(indexType, constituentType);
        Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()),
                              newType, "an array variable introduced by Boolean-term conversion",
                              NodeManager::SKOLEM_EXACT_NAME);
        top.setAttribute(BooleanTermAttr(), n);
        Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
        d_booleanTermCache[make_pair(top, boolParent)] = n;
        return n;
      }
      d_booleanTermCache[make_pair(top, boolParent)] = Node::null();
      return top;
    } else if(t.isDatatype()) {
      const Datatype& dt = t.getConst<Datatype>();
      const Datatype& dt2 = booleanTermsConvertDatatype(dt);
      if(dt != dt2) {
        Assert(d_booleanTermCache.find(make_pair(top, boolParent)) == d_booleanTermCache.end(),
               "Node `%s' already in cache ?!", top.toString().c_str());
        Assert(top.isVar());
        TypeNode newType = TypeNode::fromType(dt2.getDatatypeType());
        Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()),
                              newType, "an array variable introduced by Boolean-term conversion",
                              NodeManager::SKOLEM_EXACT_NAME);
        top.setAttribute(BooleanTermAttr(), n);
        Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
        d_booleanTermCache[make_pair(top, boolParent)] = n;
        return n;
      } else {
        d_booleanTermCache[make_pair(top, boolParent)] = Node::null();
        return top;
      }
    } else if(t.isConstructor()) {
      Assert(!boolParent);
      const Datatype& dt = t[t.getNumChildren() - 1].getConst<Datatype>();
      const Datatype& dt2 = booleanTermsConvertDatatype(dt);
      if(dt != dt2) {
        Assert(d_booleanTermCache.find(make_pair(top, boolParent)) != d_booleanTermCache.end(),
               "constructor `%s' not in cache", top.toString().c_str());
        return d_booleanTermCache[make_pair(top, boolParent)];
      } else {
        d_booleanTermCache[make_pair(top, boolParent)] = Node::null();
        return top;
      }
    } else if(t.isTester() || t.isSelector()) {
      Assert(!boolParent);
      const Datatype& dt = t[0].getConst<Datatype>();
      const Datatype& dt2 = booleanTermsConvertDatatype(dt);
      if(dt != dt2) {
        Assert(d_booleanTermCache.find(make_pair(top, boolParent)) != d_booleanTermCache.end(),
               "tester or selector `%s' not in cache", top.toString().c_str());
        return d_booleanTermCache[make_pair(top, boolParent)];
      } else {
        d_booleanTermCache[make_pair(top, boolParent)] = Node::null();
        return top;
      }
    } else if(t.getNumChildren() > 0) {
      for(TypeNode::iterator i = t.begin(); i != t.end(); ++i) {
        if((*i).isBoolean()) {
          vector<TypeNode> argTypes(t.begin(), t.end());
          replace(argTypes.begin(), argTypes.end(), *i, nm->mkBitVectorType(1));
          TypeNode newType = nm->mkTypeNode(t.getKind(), argTypes);
          Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()),
                                newType, "a variable introduced by Boolean-term conversion",
                                NodeManager::SKOLEM_EXACT_NAME);
          Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
          top.setAttribute(BooleanTermAttr(), n);
          d_booleanTermCache[make_pair(top, boolParent)] = n;
          return n;
        }
      }
    }/* else if(t.isRecord()) {
      Unimplemented();
    }*/
    return top;
  }
  switch(k) {
  case kind::LAMBDA:
  case kind::FORALL:
  case kind::EXISTS:
  case kind::REWRITE_RULE:
  case kind::RR_REWRITE:
  case kind::RR_REDUCTION:
  case kind::RR_DEDUCTION:
    //Assert(false, "not yet supported");
    return top;

  default:
    NodeBuilder<> b(k);
Debug("bt") << "looking at: " << top << std::endl;
    if(mk == kind::metakind::PARAMETERIZED) {
      if(kindToTheoryId(k) != THEORY_BV) {
Debug("bt") << "rewriting: " << top.getOperator() << std::endl;
        b << rewriteBooleanTerms(top.getOperator(), kindToTheoryId(k) == THEORY_BOOL);
Debug("bt") << "got: " << b.getOperator() << std::endl;
      } else {
        b << top.getOperator();
      }
    }
    for(TNode::const_iterator i = top.begin(); i != top.end(); ++i) {
Debug("bt") << "rewriting: " << *i << std::endl;
      b << rewriteBooleanTerms(*i, kindToTheoryId(k) == THEORY_BOOL);
Debug("bt") << "got: " << b[b.getNumChildren() - 1] << std::endl;
    }
    Node n = b;
    Debug("boolean-terms") << "constructed: " << n << endl;
    d_booleanTermCache[make_pair(top, boolParent)] = n;
    return n;
  }
}/* BooleanTermConverter::rewriteBooleanTerms() */

}/* CVC4::smt namespace */
}/* CVC4 namespace */

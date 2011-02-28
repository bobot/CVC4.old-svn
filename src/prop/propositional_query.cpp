/*********************                                                        */
/*! \file prop_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway, dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the propositional engine of CVC4.
 **
 ** Implementation of the propositional engine of CVC4.
 **/

#include "prop/propositional_query.h"
#include <map>
#include <algorithm>

#include <bdd.h>

using namespace std;
using namespace CVC4;
using namespace CVC4::prop;
using namespace CVC4::kind;


namespace CVC4 {
namespace prop {

class BddInstance {
private:
  //Cudd d_mgr;
  //std::map<Node, BDD> d_atomToBddMap;
  typedef std::map<Node, unsigned> AtomToIDMap;
  AtomToIDMap d_atomToBddMap;

  unsigned d_atomId;


  bdd encodeNode(TNode t);
  bdd encodeAtom(TNode t);
  bdd encodeCombinator(TNode t);

  bool isAnAtom(TNode t) {
    switch(t.getKind()){
    case NOT:
    case XOR:
    case IFF:
    case IMPLIES:
    case OR:
    case AND:
      return false;
    case ITE:
      return t.getType().isBoolean();
    default:
      return true;
    }
  }

  void setupAtoms(TNode t);

  void clear(){
    d_atomId = 0;
    d_atomToBddMap.clear();
  }

  Result d_result;

public:
  static const unsigned MAX_VARIABLES = 20;

  BddInstance(TNode t) : d_atomToBddMap(), d_atomId(0) {
    setupAtoms(t);

    Debug("bdd::sat") << t << endl;
    Debug("bdd::sat") << d_atomToBddMap.size() << endl;


    if(d_atomToBddMap.size() > MAX_VARIABLES){
      d_result = Result(Result::SAT_UNKNOWN, Result::TIMEOUT);
    }else{
      bdd_init(1000,100);
      bdd_gbc_hook(NULL);

      //Size must be at least 1
      size_t varsToAlloc = max(d_atomToBddMap.size(), (size_t)1);
      bdd_setvarnum(varsToAlloc);

      bdd res = encodeNode(t);
      bdd falseBdd = !(bdd_true());
      bool isUnsat = (res == falseBdd);

      clear();
      bdd_done();

      if(isUnsat){
        d_result = Result::UNSAT;
      }else{
        d_result = Result::SAT;
      }
    }
  }

  Result getResult() const{ return d_result; }


};/* class BddInstance */
}/* CVC4::prop namespace */
}/* CVC4 namespace */

bdd BddInstance::encodeNode(TNode t){
  if(isAnAtom(t)){
    return encodeAtom(t);
  }else{
    return encodeCombinator(t);
  }
}


bdd BddInstance::encodeCombinator(TNode t){
  switch(t.getKind()){
  case XOR:{
    Assert(t.getNumChildren() == 2);
    bdd left = encodeNode(t[0]);
    bdd right = encodeNode(t[1]);
    bdd res = bdd_xor(left,right);
    return res;
  }
  case IFF:{
    Assert(t.getNumChildren() == 2);
    bdd left = encodeNode(t[0]);
    bdd right = encodeNode(t[1]);
    bdd res = bdd_biimp(left,right);
    return res;
  }
  case IMPLIES:{
    Assert(t.getNumChildren() == 2);
    bdd left = encodeNode(t[0]);
    bdd right = encodeNode(t[1]);
    bdd res = bdd_imp(left,right);
    return res;
  }
  case AND:
  case OR:{
    Assert(t.getNumChildren() >= 2);
    TNode::iterator i = t.begin(), end = t.end();
    bdd tmp = encodeNode(*i);
    ++i;
    for(; i != end; ++i){
      bdd curr = encodeNode(*i);
      if(t.getKind() == AND){
        tmp = bdd_and(tmp, curr);
      }else{
        tmp = bdd_or(tmp,curr);
      }
    }
    return tmp;
  }
  case ITE:{
    Assert(t.getType().isBoolean());
    bdd cnd = encodeNode(t[0]);
    bdd thenBranch = encodeNode(t[1]);
    bdd elseBranch = encodeNode(t[2]);
    return bdd_ite(cnd,thenBranch, elseBranch);
  }
  case NOT:{
    bdd child = encodeNode(t[0]);
    return bdd_not(child);
  }
  default:
    Unhandled(t.getKind());
  }
}

bdd BddInstance::encodeAtom(TNode t){
  if(t.getKind() == kind::CONST_BOOLEAN){
    if(t.getConst<bool>()){
      return bdd_true();
    }else{
      return bdd_not(bdd_true());
    }
  }
  Assert(t.getKind() != kind::CONST_BOOLEAN);

  AtomToIDMap::iterator findT = d_atomToBddMap.find(t);
  Assert(d_atomToBddMap.find(t) != d_atomToBddMap.end());
  unsigned id = findT->second;
  return bdd_ithvar(id);
}

void BddInstance::setupAtoms(TNode t){
  if(t.getKind() == kind::CONST_BOOLEAN){
  }else if(isAnAtom(t)){
    AtomToIDMap::iterator findT = d_atomToBddMap.find(t);
    if(findT == d_atomToBddMap.end()){

      d_atomToBddMap.insert(make_pair(t, d_atomId));
      d_atomId++;
    }
  }else{
    for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
      setupAtoms(*i);
    }
  }
}

Result PropositionalQuery::isSatisfiable(TNode q){
  BddInstance instance(q);

  return instance.getResult();
}

Result PropositionalQuery::isTautology(TNode q){
  Node negQ = NodeBuilder<1>(kind::NOT) << q;
  Result satResult = isSatisfiable(negQ);

  return satResult.asValidityResult();
}

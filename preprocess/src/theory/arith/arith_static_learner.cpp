/*********************                                                        */
/*! \file arith_rewriter.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: dejan
 ** Minor contributors (to current version): mdeters
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

#include "theory/rewriter.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arith_static_learner.h"

#include "util/propositional_query.h"

#include <vector>

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;


ArithStaticLearner::ArithStaticLearner():
  d_miplibTrick(),
  d_statistics()
{}

ArithStaticLearner::Statistics::Statistics():
  d_iteMinMaxApplications("theory::arith::iteMinMaxApplications", 0),
  d_iteConstantApplications("theory::arith::iteConstantApplications", 0),
  d_miplibtrickApplications("theory::arith::miplibtrickApplications", 0),
  d_avgNumMiplibtrickValues("theory::arith::avgNumMiplibtrickValues")
{
  StatisticsRegistry::registerStat(&d_iteMinMaxApplications);
  StatisticsRegistry::registerStat(&d_iteConstantApplications);
  StatisticsRegistry::registerStat(&d_miplibtrickApplications);
  StatisticsRegistry::registerStat(&d_avgNumMiplibtrickValues);
}

ArithStaticLearner::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_iteMinMaxApplications);
  StatisticsRegistry::unregisterStat(&d_iteConstantApplications);
  StatisticsRegistry::unregisterStat(&d_miplibtrickApplications);
  StatisticsRegistry::unregisterStat(&d_avgNumMiplibtrickValues);
}

void ArithStaticLearner::staticLearning(TNode n, TheoryPreprocessor& p){

  vector<TNode> workList;
  workList.push_back(n);
  TNodeSet processed;

  //Contains an underapproximation of nodes that must hold.
  TNodeSet defTrue;

  defTrue.insert(n);

  while(!workList.empty()) {
    n = workList.back();

    bool unprocessedChildren = false;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      if(processed.find(*i) == processed.end()) {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }
    if(n.getKind() == AND && defTrue.find(n) != defTrue.end() ){
      for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
        defTrue.insert(*i);
      }
    }

    if(unprocessedChildren) {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if(processed.find(n) != processed.end()) {
      continue;
    }
    processed.insert(n);

    process(n,p, defTrue);

  }

  postProcess(p);
}

void ArithStaticLearner::clear(){
  d_miplibTrick.clear();
}



bool containsItes(TNode n){
  if(n.getKind() == ITE) return true;

  for(TNode::iterator i=n.begin(), end=n.end(); i != end; ++i){
    if(containsItes(*i)){
      return true;
    }
  }
  return false;
}

void ArithStaticLearner::process(TNode n, TheoryPreprocessor& p, const TNodeSet& defTrue){
  Debug("arith::static") << "===================== looking at" << n << endl;

  switch(n.getKind()){
  case EQUAL:
    if(defTrue.find(n) != defTrue.end()){
      eqConstant(n, p);
    }
    break;
  case ITE:
    if(false && n[0].getKind() != EQUAL &&
       isRelationOperator(n[0].getKind())  ){
      iteMinMax(n, p);
    }

    if(false &&
       (n[1].getKind() == CONST_RATIONAL || n[1].getKind() == CONST_INTEGER) &&
       (n[2].getKind() == CONST_RATIONAL || n[2].getKind() == CONST_INTEGER)) {
      iteConstant(n, p);
    }
    break;
  case IMPLIES:
    // == 3-FINITE VALUE SET : Collect information ==
    if(n[1].getKind() == EQUAL &&
       n[1][0].getMetaKind() == metakind::VARIABLE &&
       defTrue.find(n) != defTrue.end()){
      Node eqTo = n[1][1];
      Node rewriteEqTo = Rewriter::rewrite(eqTo);
      if(rewriteEqTo.getKind() == CONST_RATIONAL){

        TNode var = n[1][0];
        if(d_miplibTrick.find(var)  == d_miplibTrick.end()){
          d_miplibTrick.insert(make_pair(var, set<Node>()));
        }
        d_miplibTrick[var].insert(n);
        Debug("arith::miplib") << "insert " << var  << " const " << n << endl;
      }
    }
    break;
  default: // Do nothing
    break;
  }
}

void ArithStaticLearner::iteMinMax(TNode n, TheoryPreprocessor& p){
  Assert(n.getKind() == kind::ITE);
  Assert(n[0].getKind() != EQUAL);
  Assert(isRelationOperator(n[0].getKind()));

  TNode c = n[0];
  Kind k = simplifiedKind(c);
  TNode t = n[1];
  TNode e = n[2];
  TNode cleft = (c.getKind() == NOT) ? c[0][0] : c[0];
  TNode cright = (c.getKind() == NOT) ? c[0][1] : c[1];

  if((t == cright) && (e == cleft)){
    TNode tmp = t;
    t = e;
    e = tmp;
    k = reverseRelationKind(k);
  }
  if(t == cleft && e == cright){
    // t == cleft && e == cright
    Assert( t == cleft );
    Assert( e == cright );
    Node skolem = p.skolemize(n);

    switch(k){
    case LT:   // (ite (< x y) x y)
    case LEQ: { // (ite (<= x y) x y)
      Node nLeqX = NodeBuilder<2>(LEQ) << skolem << t;
      Node nLeqY = NodeBuilder<2>(LEQ) << skolem << e;
      Debug("arith::static") << n << "is a min =>"  << nLeqX << nLeqY << endl;
      p.learn( nLeqX );
      p.learn( nLeqY );
      ++(d_statistics.d_iteMinMaxApplications);
      break;
    }
    case GT: // (ite (> x y) x y)
    case GEQ: { // (ite (>= x y) x y)
      Node nGeqX = NodeBuilder<2>(GEQ) << skolem << t;
      Node nGeqY = NodeBuilder<2>(GEQ) << skolem << e;
      Debug("arith::static") << n << "is a max =>"  << nGeqX << nGeqY << endl;
      p.learn( nGeqX) ;
      p.learn( nGeqY );
      ++(d_statistics.d_iteMinMaxApplications);
      break;
    }
    default: Unreachable();
    }
  }
}

void ArithStaticLearner::eqConstant(TNode n, TheoryPreprocessor& p) {
  Assert(n.getKind() == EQUAL);

  Node rewrite = p.replaceAndRewrite(n);

  Debug("eqConstant") << n << " -> " << rewrite << endl;

  if(rewrite[0].getMetaKind() == metakind::VARIABLE &&
     rewrite[1].getKind() == CONST_RATIONAL){

    bool success = p.requestReplacement(rewrite[0], rewrite[1]);
    if(!success){
      Debug("eqConstant") << "failed " << n << endl;
    }else{
      Debug("eqConstant") << "success " << n << endl;
    }
  }
}

void ArithStaticLearner::iteConstant(TNode n, TheoryPreprocessor& p){
  Assert(n.getKind() == ITE);
  Assert(n[1].getKind() == CONST_RATIONAL || n[1].getKind() == CONST_INTEGER );
  Assert(n[2].getKind() == CONST_RATIONAL || n[2].getKind() == CONST_INTEGER );

  Node skolem = p.skolemize(n);

  Rational t = coerceToRational(n[1]);
  Rational e = coerceToRational(n[2]);
  TNode min = (t <= e) ? n[1] : n[2];
  TNode max = (t >= e) ? n[1] : n[2];

  Node skolemGeqMin = NodeBuilder<2>(GEQ) << skolem << min;
  Node skolemLeqMax = NodeBuilder<2>(LEQ) << skolem << max;
  Debug("arith::static") << n << " iteConstant"  << skolemGeqMin << skolemLeqMax << endl;
  p.learn( skolemLeqMax );
  p.learn( skolemLeqMax );
  ++(d_statistics.d_iteConstantApplications);
}


void ArithStaticLearner::postProcess(TheoryPreprocessor& p){
  vector<TNode> keys;
  VarToNodeSetMap::iterator mipIter = d_miplibTrick.begin();
  VarToNodeSetMap::iterator endMipLibTrick = d_miplibTrick.end();
  for(; mipIter != endMipLibTrick; ++mipIter){
    keys.push_back(mipIter->first);
  }

  // == 3-FINITE VALUE SET ==
  vector<TNode>::iterator keyIter = keys.begin();
  vector<TNode>::iterator endKeys = keys.end();
  for(; keyIter != endKeys; ++keyIter){
    TNode var = *keyIter;
    const set<Node>& imps = d_miplibTrick[var];

    Assert(!imps.empty());
    vector<Node> conditions;
    set<Rational> values;
    set<Node>::const_iterator j=imps.begin(), impsEnd=imps.end();
    for(; j != impsEnd; ++j){
      TNode imp = *j;
      Assert(imp.getKind() == IMPLIES);
      Assert(imp[1].getKind() == EQUAL);

      Node eqTo = imp[1][1];
      Node rewriteEqTo = Rewriter::rewrite(eqTo);
      Assert(rewriteEqTo.getKind() == CONST_RATIONAL);

      conditions.push_back(imp[0]);
      values.insert(rewriteEqTo.getConst<Rational>());
    }

    Node possibleTaut = Node::null();
    if(conditions.size() == 1){
      possibleTaut = conditions.front();
    }else{
      NodeBuilder<> orBuilder(OR);
      orBuilder.append(conditions);
      possibleTaut = orBuilder;
    }


    Debug("arith::miplib") << "var: " << var << endl;
    Debug("arith::miplib") << "possibleTaut: " << possibleTaut << endl;

    Result isTaut = PropositionalQuery::isTautology(possibleTaut);
    if(isTaut == Result(Result::VALID)){
      miplibTrick(var, values, p);
      d_miplibTrick.erase(var);
    }
  }
}


void ArithStaticLearner::miplibTrick(TNode var, set<Rational>& values, TheoryPreprocessor& p){

  Debug("arith::miplib") << var << " found a tautology!"<< endl;

  const Rational& min = *(values.begin());
  const Rational& max = *(values.rbegin());

  Debug("arith::miplib") << "min: " << min << endl;
  Debug("arith::miplib") << "max: " << max << endl;

  Assert(min <= max);
  ++(d_statistics.d_miplibtrickApplications);
  (d_statistics.d_avgNumMiplibtrickValues).addEntry(values.size());

  Node nGeqMin = NodeBuilder<2>(GEQ) << var << mkRationalNode(min);
  Node nLeqMax = NodeBuilder<2>(LEQ) << var << mkRationalNode(max);
  Debug("arith::miplib") << nGeqMin << nLeqMax << endl;
  p.learn(nGeqMin);
  p.learn(nLeqMax);
  set<Rational>::iterator valuesIter = values.begin();
  set<Rational>::iterator valuesEnd = values.end();
  set<Rational>::iterator valuesPrev = valuesIter;
  ++valuesIter;
  for(; valuesIter != valuesEnd; valuesPrev = valuesIter, ++valuesIter){
    const Rational& prev = *valuesPrev;
    const Rational& curr = *valuesIter;
    Assert(prev < curr);

    //The interval (last,curr) can be excluded:
    //(not (and (> var prev) (< var curr))
    //<=> (or (not (> var prev)) (not (< var curr)))
    //<=> (or (<= var prev) (>= var curr))
    Node leqPrev = NodeBuilder<2>(LEQ) << var << mkRationalNode(prev);
    Node geqCurr = NodeBuilder<2>(GEQ) << var << mkRationalNode(curr);
    Node excludedMiddle =  NodeBuilder<2>(OR) << leqPrev << geqCurr;
    Debug("arith::miplib") << excludedMiddle << endl;
    p.learn( excludedMiddle );
  }
}

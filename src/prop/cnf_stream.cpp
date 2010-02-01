/*********************                                           -*- C++ -*-  */
/** cnf_stream.cpp
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **/

#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "expr/node.h"
#include "util/Assert.h"

using namespace CVC4::prop::minisat;
using namespace std;


namespace CVC4 {
namespace prop {

CnfStream::CnfStream(PropEngine *pe) : d_pl(pe){}


void CnfStream::insertClauseIntoStream(vec<Lit> & c){
  d_pl->assertClause(c);
}

void CnfStream::insertClauseIntoStream(minisat::Lit a){
  vec<Lit> clause(1);
  clause[0] = a;
  insertClauseIntoStream(clause);
}
void CnfStream::insertClauseIntoStream(minisat::Lit a,minisat::Lit b){
  vec<Lit> clause(2);
  clause[0] = a;
  clause[1] = b;
  //  clause.push(a);
  //clause.push(b);
  insertClauseIntoStream(clause);
}
void CnfStream::insertClauseIntoStream(minisat::Lit a,minisat::Lit b, minisat::Lit c){
  vec<Lit> clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  //clause.push(a);
  //clause.push(b);
  //clause.push(c);
  insertClauseIntoStream(clause);
}

//TODO: only NOT, and setupLit use this directly
//Reorganizing this probably makes sense.
Lit CnfStream::registerLit(const Node & n, Lit intermsOf, bool negate){
  Lit l = (negate ? ~intermsOf : intermsOf);
  d_pl->registerMapping(n, l);
  return l;
}
Lit CnfStream::setupLit(const Node & n){
  Lit l = d_pl->requestFreshLit();
  return registerLit(n, l);
}

Lit CnfStream::handleAtom(const Node & n){
  Lit l = setupLit(n);
  switch(n.getKind()){ /* TRUE and FALSE are handled specially. */
  case TRUE:
    insertClauseIntoStream( l );
    break;
  case FALSE:
    insertClauseIntoStream( ~l );
    break;
  default: //Does nothing else
    break;
  }
  return l;
}

Lit CnfStream::handleXor(const Node & n){
  // n: a XOR b
  
  Lit a = naiveRecConvertToCnf(n[0]);
  Lit b = naiveRecConvertToCnf(n[1]);
  
  Lit l = setupLit(n);
  
  insertClauseIntoStream( a,  b, ~l);
  insertClauseIntoStream( a, ~b,  l);
  insertClauseIntoStream(~a,  b,  l);
  insertClauseIntoStream(~a, ~b, ~l);
  
  return l;
}

void  CnfStream::childLiterals(const Node& n, vec<Lit> & target){
  for(Node::iterator subExprIter = n.begin();
      subExprIter != n.end();
      ++subExprIter){
    Lit equivalentLit = naiveRecConvertToCnf(*subExprIter);
    target.push(equivalentLit);
  }
}

Lit CnfStream::handleOr(const Node& n){
  //child_literals
  vec<Lit> lits;
  childLiterals(n, lits);
  
  Lit e = setupLit(n);
  
  /* e <-> (a1 | a2 | a3 | ...)
   *: e -> (a1 | a2 | a3 | ...)
   * : ~e | (
   * : ~e | a1 | a2 | a3 | ...
   * e <- (a1 | a2 | a3 | ...)
   * : e <- (a1 | a2 | a3 |...)
   * : e | ~(a1 | a2 | a3 |...)
   * : 
   * : (e | ~a1) & (e |~a2) & (e & ~a3) & ...
   */

  vec<Lit> c;
  c.push(~e);
  
  for( int index = 0; index < lits.size(); ++index){
    Lit a = lits[index];
    c.push(a);
    insertClauseIntoStream( e, ~a);
  }
  insertClauseIntoStream(c);
  
  return e;
}


/* TODO: this only supports 2-ary <=> nodes atm.
 * Should this be changed?
 */
Lit CnfStream::handleIff(const Node& n){
  Assert(n.getKind() == IFF);
  Assert(n.getNumChildren() == 2);
  // n: a <=> b;

  Lit a = naiveRecConvertToCnf(n[0]);
  Lit b = naiveRecConvertToCnf(n[1]);
    
  Lit l = setupLit(n);
    
  /* l <-> (a<->b)
   * : l -> ((a-> b) & (b->a))
   * : ~l | ((~a | b) & (~b |a))
   * : (~a | b | ~l ) & (~b | a | ~l)
   * 
   * : (a<->b) -> l
   * : ~((a & b) | (~a & ~b)) | l
   * : (~(a & b)) & (~(~a & ~b)) | l
   * : ((~a | ~b) & (a | b)) | l
   * : (~a | ~b | l) & (a | b | l)
   */
    
  insertClauseIntoStream( ~a, b,~l);
  insertClauseIntoStream(  a,~b,~l);
  insertClauseIntoStream( ~a,~b, l);
  insertClauseIntoStream(  a, b, l);
  
  return l;
}

Lit CnfStream::handleAnd(const Node& n){
  //TODO: we know the exact size of the this.
  //Dynamically allocated array would have less overhead no?
  vec<Lit> lits;
  childLiterals(n, lits);
    
  Lit e = setupLit(n);

  /* e <-> (a1 & a2 & a3 & ...)
   * : e -> (a1 & a2 & a3 & ...)
   * : ~e | (a1 & a2 & a3 & ...)
   * : (~e | a1) & (~e | a2) & ...
   * e <- (a1 & a2 & a3 & ...)
   * : e <- (a1 & a2 & a3 & ...)
   * : e | ~(a1 & a2 & a3 & ...)
   * : e | (~a1 | ~a2 | ~a3 | ...)
   * : e | ~a1 | ~a2 | ~a3 | ...
   */

  vec<Lit> c;
  c.push(e);
  for(int index = 0; index < lits.size(); ++index){
    Lit a = lits[index];
    c.push(~a);
    insertClauseIntoStream( ~e, a );
  }
  insertClauseIntoStream(c);
  
  return e;
}

Lit CnfStream::handleImplies(const Node & n){
  Assert(n.getKind() == IMPLIES);
  // n: a => b;

  Lit a = naiveRecConvertToCnf(n[0]);
  Lit b = naiveRecConvertToCnf(n[1]);
  
  Lit l = setupLit(n);
  
  /* l <-> (a->b)
   * (l -> (a->b)) & (l <- (a->b))
   *  : l -> (a -> b)
   *  : ~l | (~ a | b)
   *  : (~l | ~a | b)
   * (~l | ~a | b) & (l<- (a->b))
   *  : (a->b) -> l
   *  : ~(~a | b) | l
   *  : (a & ~b) | l
   *  : (a | l) & (~b | l)
   * (~l | ~a | b) & (a | l) & (~b | l)
   */
    
  insertClauseIntoStream(  a, l);
  insertClauseIntoStream( ~b, l);
  insertClauseIntoStream( ~l, ~a, b);
  
  return l;
}

Lit CnfStream::handleNot(const Node & n){
  Assert(n.getKind() == NOT);
  
  // n : NOT m
  Node m = n[0];
  Lit equivM = naiveRecConvertToCnf(m);
  return registerLit(n, equivM, true);
}

//FIXME: This function is a major hack! Should be changed ASAP
//Assumes binary no else if branchs, and that ITEs 
Lit CnfStream::handleIte(const Node & n){
  Assert(n.getKind() == ITE);
  
  // n : IF c THEN t ELSE f ENDIF;
  Lit c = naiveRecConvertToCnf(n[0]);
  Lit t = naiveRecConvertToCnf(n[1]);
  Lit f = naiveRecConvertToCnf(n[2]);
  
  // d <-> IF c THEN tB ELSE fb
  // : d -> (c & tB) | (~c & fB)
  // : ~d | ( (c & tB) | (~c & fB) )
  // :          x | (y & z) = (x | y) & (x | z)
  // : ~d | ( ((c & t) | ~c ) & ((c & t) | f ) )
  // : ~d | ( (((c | ~c) & (~c | t))) & ((c | f) & (f | t)) )
  // : ~d | ( (~c | t) & (c | f) & (f | t) )
  // : (~d | ~c | t) & (~d | c | f) & (~d | f | t)

  // : ~d | (c & t & f)
  // : (~d | c)  & (~d | t) & (~d | f)
  // ( IF c THEN tB ELSE fb) -> d
  // :~((c & tB) | (~c & fB)) | d
  // : ((~c | ~t)& ( c |~fb)) | d
  // : (~c | ~ t | d) & (c | ~f | d)

  Lit d = setupLit(n);

  insertClauseIntoStream(~d , ~c , t);
  insertClauseIntoStream(~d ,  c , f);
  insertClauseIntoStream(~d ,  f , t);
  insertClauseIntoStream(~c , ~t , d);
  insertClauseIntoStream( c , ~f , d);

  return d;
}

//FIXME: This function is a major hack! Should be changed ASAP
//TODO: Should be moved. Not sure where...
//TODO: Should use positive defintion, i.e. what kinds are atomic.
bool atomic(const Node & n){
  switch(n.getKind()){
  case NOT:
  case XOR:
  case ITE:
  case IFF:
  case OR:
  case AND:
    return false;
  default:
    return true;
  }
}

//TODO: The following code assumes everthing is either
// an atom or is a logical connective. This ignores quantifiers and lambdas.
Lit CnfStream::naiveRecConvertToCnf(const Node & n){
  if(d_pl->isNodeMapped(n)){
    return d_pl->lookupLit(n);
  }
  
  if(atomic(n)){
    return handleAtom(n);
  }else{
    //Assume n is a logical connective
    
    switch(n.getKind()){
    case NOT:
      return handleNot(n);
    case XOR:
      return handleXor(n);
    case ITE:
      return handleIte(n);
    case IFF:
      return handleIff(n);
    case OR:
      return handleOr(n);
    case AND:
      return handleAnd(n);
    default:
      Unreachable();
    }
  }
}
  
void CnfStream::convertAndAssert(const Node & n){
  //n has already been mapped so use the previous result
  if(d_pl->isNodeMapped(n)){
    Lit l = d_pl->lookupLit( n );
    insertClauseIntoStream(l);
    return;
  }
  
  if(n.getKind() == AND){
    for(Node::iterator i = n.begin(); i != n.end(); ++i){
      convertAndAssert(*i);
    }
  }else if(n.getKind() == OR){
    vec<Lit> c;
    for(Node::iterator i = n.begin(); i != n.end(); ++i){
      Lit cl = naiveRecConvertToCnf(*i);
      c.push(cl);
    }
    insertClauseIntoStream(c);
  }else{
    Lit e = naiveRecConvertToCnf(n);
    insertClauseIntoStream( e );
  }
}




}/* CVC4::prop namespace */
}/* CVC4 namespace */

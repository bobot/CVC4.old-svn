/*********************                                                        */
/*! \file theory_uf_candidate generator.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory uf candidate generator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_CANDIDATE_GENERATOR_H
#define __CVC4__THEORY_UF_CANDIDATE_GENERATOR_H

#include "theory/quantifiers_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/rr_inst_match.h"

namespace CVC4 {
namespace theory {
namespace uf {

namespace rrinst{
typedef CVC4::theory::rrinst::CandidateGenerator CandidateGenerator;

//New CandidateGenerator. They have a simpler semantic than the old one

// Just iterate amoung the equivalence classes
// node::Null() must be given to reset
class CandidateGeneratorTheoryUfClasses : public CandidateGenerator{
private:
  //the equality classes iterator
  eq::EqClassesIterator d_eq;
  //einstantiator pointer
  InstantiatorTheoryUf* d_ith;
public:
  CandidateGeneratorTheoryUfClasses( InstantiatorTheoryUf * ith): d_ith( ith ){}
  ~CandidateGeneratorTheoryUfClasses(){}
  void resetInstantiationRound(){};
  void reset( TNode eqc ){
    Assert(eqc.isNull());
    d_eq = eq::EqClassesIterator( ((TheoryUF*)d_ith->getTheory())->getEqualityEngine() );
  }; //* the argument is not used
  TNode getNextCandidate(){
    if( !d_eq.isFinished() ) return (*(d_eq++));
    else return Node::null();
  };
};

// Just iterate amoung the equivalence class of the given node
// node::Null() *can't* be given to reset
class CandidateGeneratorTheoryUfClass : public CandidateGenerator{
private:
  //instantiator pointer
  InstantiatorTheoryUf* d_ith;
  //the equality class iterator
  eq::EqClassIterator d_eqc;
  /* For the case where the given term doesn't exists in uf */
  Node d_retNode;
public:
  CandidateGeneratorTheoryUfClass( InstantiatorTheoryUf* ith): d_ith( ith ){}
  ~CandidateGeneratorTheoryUfClass(){}
  void resetInstantiationRound(){};
  void reset( TNode eqc ){
    Assert(!eqc.isNull());
    if( ((TheoryUF*)d_ith->getTheory())->getEqualityEngine()->hasTerm( eqc ) ){
      /* eqc is in uf  */
      eqc = ((TheoryUF*)d_ith->getTheory())->getEqualityEngine()->getRepresentative( eqc );
      d_eqc = eq::EqClassIterator( eqc, ((TheoryUF*)d_ith->getTheory())->getEqualityEngine() );
      d_retNode = Node::null();
    }else{
      /* If eqc if not a term known by uf, it is the only one in its
         equivalence class. So we will return only it */
      d_retNode = eqc;
      d_eqc = eq::EqClassIterator();
    }
  }; //* the argument is not used
  TNode getNextCandidate(){
    if(d_retNode.isNull()){
      if( !d_eqc.isFinished() ) return (*(d_eqc++));
      else return Node::null();
    }else{
      /* the case where eqc not in uf */
      Node ret = d_retNode;
      d_retNode = Node::null(); /* d_eqc.isFinished() must be true */
      return ret;
    }
  };
};

class CandidateGeneratorTheoryUfOp : public CandidateGenerator{
private:
  Node d_op;
  //instantiator pointer
  InstantiatorTheoryUf* d_ith;
  // Since new term can appears we restrict ourself to the one that
  // exists at resetInstantiationRound
  size_t d_term_iter_limit;
  size_t d_term_iter;
public:
  CandidateGeneratorTheoryUfOp(Node op, InstantiatorTheoryUf* ith): d_op(op), d_ith( ith ){}
  ~CandidateGeneratorTheoryUfOp(){}
  void resetInstantiationRound(){
    d_term_iter_limit = d_ith->getQuantifiersEngine()->getTermDatabase()->d_op_map[d_op].size();
  };
  void reset( TNode eqc ){
    Assert(eqc.isNull());
    d_term_iter = 0;
  }; //* the argument is not used
  TNode getNextCandidate(){
    if( d_term_iter<d_term_iter_limit ){
      TNode n = d_ith->getQuantifiersEngine()->getTermDatabase()->d_op_map[d_op][d_term_iter];
      ++d_term_iter;
      return n;
    } else return Node::null();
  };
};


class CandidateGeneratorTheoryUfType : public CandidateGenerator{
private:
  TypeNode d_type;
  //instantiator pointer
  InstantiatorTheoryUf* d_ith;
  // Since new term can appears we restrict ourself to the one that
  // exists at resetInstantiationRound
  size_t d_term_iter_limit;
  size_t d_term_iter;
public:
  CandidateGeneratorTheoryUfType(TypeNode type, InstantiatorTheoryUf* ith): d_type(type), d_ith( ith ){}
  ~CandidateGeneratorTheoryUfType(){}
  void resetInstantiationRound(){
    d_term_iter_limit = d_ith->getQuantifiersEngine()->getTermDatabase()->d_type_map[d_type].size();
  };
  void reset( TNode eqc ){
    Assert(eqc.isNull());
    d_term_iter = 0;
  }; //* the argument is not used
  TNode getNextCandidate(){
    if( d_term_iter<d_term_iter_limit ){
      TNode n = d_ith->getQuantifiersEngine()->getTermDatabase()->d_type_map[d_type][d_term_iter];
      ++d_term_iter;
      return n;
    } else return Node::null();
  };
};

} /* namespace inst */

namespace inst{
typedef CVC4::theory::inst::CandidateGenerator CandidateGenerator;

//Old CandidateGenerator

class CandidateGeneratorTheoryUfDisequal;

class CandidateGeneratorTheoryUf : public CandidateGenerator
{
  friend class CandidateGeneratorTheoryUfDisequal;
private:
  //operator you are looking for
  Node d_op;
  //instantiator pointer
  InstantiatorTheoryUf* d_ith;
  //the equality class iterator
  eq::EqClassIterator d_eqc;
  int d_term_iter;
  int d_term_iter_limit;
private:
  Node d_retNode;
public:
  CandidateGeneratorTheoryUf( InstantiatorTheoryUf* ith, Node op );
  ~CandidateGeneratorTheoryUf(){}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
};

//class CandidateGeneratorTheoryUfDisequal : public CandidateGenerator
//{
//private:
//  //equivalence class 
//  Node d_eq_class;
//  //equivalence class info
//  EqClassInfo* d_eci;
//  //equivalence class iterator
//  EqClassInfo::BoolMap::const_iterator d_eqci_iter;
//  //instantiator pointer
//  InstantiatorTheoryUf* d_ith;
//public:
//  CandidateGeneratorTheoryUfDisequal( InstantiatorTheoryUf* ith, Node eqc );
//  ~CandidateGeneratorTheoryUfDisequal(){}
//
//  void resetInstantiationRound();
//  void reset( Node eqc );   //should be what you want to be disequal from
//  Node getNextCandidate();
//};

class CandidateGeneratorTheoryUfLitEq : public CandidateGenerator
{
private:
  //the equality classes iterator
  eq::EqClassesIterator d_eq;
  //equality you are trying to match equalities for
  Node d_match_pattern;
  //einstantiator pointer
  InstantiatorTheoryUf* d_ith;
public:
  CandidateGeneratorTheoryUfLitEq( InstantiatorTheoryUf* ith, Node mpat );
  ~CandidateGeneratorTheoryUfLitEq(){}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
};

class CandidateGeneratorTheoryUfLitDeq : public CandidateGenerator
{
private:
  //the equality class iterator for false
  eq::EqClassIterator d_eqc_false;
  //equality you are trying to match disequalities for
  Node d_match_pattern;
  //einstantiator pointer
  InstantiatorTheoryUf* d_ith;
public:
  CandidateGeneratorTheoryUfLitDeq( InstantiatorTheoryUf* ith, Node mpat );
  ~CandidateGeneratorTheoryUfLitDeq(){}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
};


}/* CVC4::theory::uf::inst namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

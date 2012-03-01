/*********************                                                        */
/*! \file theory_uf_candidate_generator.cpp
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
 ** \brief Implementation of theory uf candidate generator class
 **/

#include "theory/uf/theory_uf_candidate_generator.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine_impl.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

void CandidateGeneratorTheoryUf::resetInstantiationRound(){
  d_term_iter_limit = d_ith->getTermDatabase()->d_op_map[d_op].size();
}

void CandidateGeneratorTheoryUf::reset( Node eqc ){
  if( eqc.isNull() ){
    Assert( !d_op.isNull() );
    d_term_iter = 0;
  }else{
    //create an equivalence class iterator in eq class eqc
    d_eqc = EqClassIterator( eqc, ((TheoryUF*)d_ith->getTheory())->getEqualityEngine() );
    d_term_iter = -1;
  }
}

Node CandidateGeneratorTheoryUf::getNextCandidate(){
  if( d_term_iter>=0 ){
    //get next candidate term in the uf term database
    if( d_term_iter<d_term_iter_limit ){
      Node n = d_ith->getTermDatabase()->d_op_map[d_op][d_term_iter];
      d_term_iter++;
      return n;
    }
  }else if( d_term_iter==-1 ){
    //get next candidate term in equivalence class
    while( !d_eqc.isFinished() ){
      Node n = (*d_eqc);
      ++d_eqc;
      if( d_op.isNull() ){
        //done producing matches
        if( !n.hasAttribute(InstConstantAttribute()) ){
          d_term_iter = -2;
          return n;
        }
      }else{
        if( n.getKind()==APPLY_UF && n.getOperator()==d_op ){
          if( !n.hasAttribute(InstConstantAttribute()) ){
            return n;
          }
        }
      }
    }
  }
  return Node::null();
}


CandidateGeneratorTheoryUfDisequal::CandidateGeneratorTheoryUfDisequal( InstantiatorTheoryUf* ith, Node op ) : d_ith( ith ){
  d_cg = new CandidateGeneratorTheoryUf( ith, op );
  d_eci = NULL;
}


void CandidateGeneratorTheoryUfDisequal::resetInstantiationRound(){
  
}

//we will iterate over all terms that are disequal from eqc
void CandidateGeneratorTheoryUfDisequal::reset( Node eqc ){
  //Assert( !eqc.isNull() );
  ////begin iterating over equivalence classes that are disequal from eqc
  //d_eci = d_ith->getEquivalenceClassInfo( eqc );
  //if( d_eci ){
  //  d_eqci_iter = d_eci->d_disequal.begin();
  //}
}

Node CandidateGeneratorTheoryUfDisequal::getNextCandidate(){
  //if( d_eci ){
  //  while( d_eqci_iter != d_eci->d_disequal.end() ){
  //    if( (*d_eqci_iter).second ){
  //      //we have an equivalence class that is disequal from eqc
  //      d_cg->reset( (*d_eqci_iter).first );
  //      Node n = d_cg->getNextCandidate();
  //      //if there is a candidate in this equivalence class, return it
  //      if( !n.isNull() ){
  //        return n;
  //      }
  //    }
  //    ++d_eqci_iter;
  //  }
  //}
  return Node::null();
}

CandidateGeneratorTheoryUfEq::CandidateGeneratorTheoryUfEq( InstantiatorTheoryUf* ith, Node pat, Node mpat ) : 
  d_pattern( pat ), d_match_pattern( mpat ), d_ith( ith ){
  
}

void CandidateGeneratorTheoryUfEq::resetInstantiationRound(){
  
}

void CandidateGeneratorTheoryUfEq::reset( Node eqc ){
  //bool pol = d_pattern.getKind()!=NOT;
  //Node eq = d_pattern.getKind()==NOT ? d_pattern[0] : d_pattern;
  //Assert( eq.getKind()==IFF || eq.getKind()==EQUAL );

}

Node CandidateGeneratorTheoryUfEq::getNextCandidate(){
  return Node::null();
}

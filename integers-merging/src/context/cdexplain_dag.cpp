/*********************                                                        */
/*! \file cdexplain_dag.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Datastructure for keeping track of proofs in a context dependent fashion.
 **
 ** Implementation of a lazy datastructure for keeping track of proofs in a context dependent fashion.
 **/

#include "context/cdexplain_dag.h"

#include <stack>
#include <limits>

namespace CVC4 {
namespace context {

CDExplainDAG::CDExplainDAG(Context* c):
  ContextNotifyObj(c),
  SENTINEL(std::numeric_limits<ProofIndex>::max()),
  d_writtenSinceLastPop(false),
  d_lastActiveFact(c, 0),
  d_lastActiveProof(c,0)
{}

void CDExplainDAG::enqueueLeaves(CDExplainDAG::ProofIndex start, NodeBuilder<>& nb) const{
  std::stack<ProofIndex> pis;
    pis.push(start);
    while(!pis.empty()){
      ProofIndex ci = pis.top();
      pis.pop();

      if(ci == this->SENTINEL){
        continue;
      }

      const ProofNode& curr = d_pv[ci];
      switch(curr.getType()){
      case LEAF:
        nb << d_fv[curr.getFactIndex()];
        break;
      case CONS:
        pis.push(curr.getCar());
        pis.push(curr.getCdr());
        break;
      default:
        Unhandled(curr.getType());
      }
    }
  }



}/* context namespace */

}/* CVC4 namespace */

/*********************                                                        */
/*! \file relevant_domain.h
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
 ** \brief relevant domain class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__RELEVANT_DOMAIN_H
#define __CVC4__RELEVANT_DOMAIN_H

#include "theory/quantifiers_engine.h"
#include "theory/extended_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class RelevantDomain
{
private:
  QuantifiersEngine* d_quantEngine;

  //the domain of the arguments
  std::map< Node, std::map< int, RepDomain > > d_active_domain;
  //for computing relevant instantiation domain, return true if changed
  bool computeRelevantInstantiationDomain( Node n, Node parent, int arg, std::vector< RepDomain >& rd );
  //for computing extended
  bool extendFunctionDomains( Node n, RepDomain& range );
public:
  RelevantDomain( QuantifiersEngine* qe );
  virtual ~RelevantDomain(){}
  //compute the relevant domain
  void compute();
  //relevant instantiation domain for each quantifier
  std::map< Node, std::vector< RepDomain > > d_quant_inst_domain;
};

}
}
}

#endif

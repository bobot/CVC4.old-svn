/*********************                                                        */
/*! \file theory_uf_instantiator.cpp
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
 ** \brief Implementation of theory uf instantiator class
 **/

#include "theory/uf/morgan/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/uf/morgan/theory_uf_morgan.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::uf::morgan;

TheoryUfInstantiatior::TheoryUfInstantiatior(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th) :
TheoryInstantiatior( c, ie ),
d_th(th),
d_nodes(c){
  
  
}

Theory* TheoryUfInstantiatior::getTheory() { 
  return d_th; 
}

void TheoryUfInstantiatior::check( Node assertion )
{
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  Debug("quant-uf") << "TheoryUfInstantiatior::check: " << assertion << std::endl;
  switch(assertion.getKind()) {
  case kind::EQUAL:
  case kind::IFF:
    assertEqual(assertion[0], assertion[1]);
    break;
  case kind::APPLY_UF:
    { // assert it's a predicate
      Assert(assertion.getOperator().getType().getRangeType().isBoolean());
      assertEqual(assertion, t->d_trueNode);
    }
    break;
  case kind::NOT:
    if(assertion[0].getKind() == kind::EQUAL ||
       assertion[0].getKind() == kind::IFF) {
      assertDisequal(assertion[0][0], assertion[0][1]);
    } else {
      // negation of a predicate
      Assert(assertion[0].getKind() == kind::APPLY_UF);
      // assert it's a predicate
      Assert(assertion[0].getOperator().getType().getRangeType().isBoolean());
      assertEqual(assertion[0], t->d_falseNode);
    }
    break;
  default:
    Unhandled(assertion.getKind());
  }
}

void TheoryUfInstantiatior::assertEqual( Node a, Node b )
{
  if( b.getKind()==INST_CONSTANT){
    Node t = a;
    a = b;
    b = t;
  }
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  registerTerm( a );
  registerTerm( b );
}

void TheoryUfInstantiatior::assertDisequal( Node a, Node b )
{
  if( b.getKind()==INST_CONSTANT){
    Node t = a;
    a = b;
    b = t;
  }
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  registerTerm( a );
  registerTerm( b );
}

void TheoryUfInstantiatior::registerTerm( Node n )
{
  d_nodes[n] = true;
}

bool TheoryUfInstantiatior::prepareInstantiation()
{
  Debug("quant-uf") << "Search for instantiation for UF:" << std::endl;

  //find all instantiation constants that are solved


  //we're done if some node is instantiation-ready


  //otherwise, add possible splitting lemma


  return false;
}

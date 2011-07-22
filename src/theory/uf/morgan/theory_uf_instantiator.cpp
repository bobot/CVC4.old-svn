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
d_th( th ){
  
}

bool TheoryUfInstantiatior::doInstantiation( OutputChannel* out )
{
  Debug("quant-uf") << "Get instantiation for UF:" << std::endl;
  
  TheoryUFMorgan* t = (TheoryUFMorgan*)d_th;
  UnionFind<TNode, TNodeHashFunction>* u = &t->d_unionFind;


  return false;
}

/*********************                                                        */
/*! \file instantiation_engine.h
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
 ** \brief Theory instantiator, Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATION_ENGINE_H
#define __CVC4__INSTANTIATION_ENGINE_H

#include "theory/theory.h"
#include "util/hash.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {

class TheoryEngine;
class SmtEngine;

namespace theory {

class InstantiationEngine;

class TheoryInstantiatior{
protected:
  /** reference to the instantiation engine */
  InstantiationEngine* d_ie;
public:
  TheoryInstantiatior(context::Context* c, InstantiationEngine* ie);
  TheoryInstantiatior(){}
  ~TheoryInstantiatior();

  virtual bool doInstantiation( OutputChannel* out ){ return false; }
  virtual Theory* getTheory() = 0;
};/* class TheoryInstantiatior */

class InstantiationEngine
{
  friend class ::CVC4::TheoryEngine;
private:
  /** theory instantiator objects for each theory */
  theory::TheoryInstantiatior* d_instTable[theory::THEORY_LAST];
  /** reference to theory engine object */
  TheoryEngine* d_te;
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_vars;
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** instantiation constants to universal quantifiers */
  std::map< Node, Node > d_inst_constants_map;
  /** map from universal quantifiers to list of instantiations per theory */
  std::map< Node, std::map< Theory*, std::map< Node, Node > > > d_inst_map;
public:
  InstantiationEngine(context::Context* c, TheoryEngine* te);
  ~InstantiationEngine();
  
  theory::TheoryInstantiatior* getTheoryMatcher( Theory* t ) { return d_instTable[t->getId()]; }

  void getInstantiationConstantsFor( Node f, std::vector< Node >& vars, std::vector< Node >& ics );
  bool getInstantiationFor( Node f, std::vector< Node >& vars, std::vector< Node >& terms );
  bool doInstantiation( OutputChannel* out );
};/* class InstantiationEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

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
 ** \brief Theory matcher, Instantiation Engine classes
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

namespace theory {

class InstantiationEngine;

class TheoryMatcher{
protected:
  /** reference to the instantiation engine */
  InstantiationEngine* d_ie;
public:
  TheoryMatcher(context::Context* c, InstantiationEngine* ie);
  ~TheoryMatcher();

  virtual bool getInstantiation( std::map< Node, Node >& inst ){ return false; }
  virtual Theory* getTheory() = 0;
};/* class TheoryMatcher */

class InstantiationEngine
{
private:
  /** theory matcher objects for each theory */
  theory::TheoryMatcher* d_matcherTable[theory::THEORY_LAST];
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
  
  theory::TheoryMatcher* getTheoryMatcher( Theory* t );

  void getInstantiationConstantsFor( Node f, std::vector< Node >& vars, std::vector< Node >& ics );
  bool getInstantiationFor( Node f, std::vector< Node >& vars, std::vector< Node >& terms );
};/* class InstantiationEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

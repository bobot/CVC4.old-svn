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

// attribute for "contains instantiation constants from"
struct InstantitionConstantAttributeId {};
typedef expr::Attribute<InstantitionConstantAttributeId, Node> InstantitionConstantAttribute;

namespace theory {

class InstantiationEngine;

class Instantiatior{
  friend class InstantiationEngine;
protected:
  /** reference to the instantiation engine */
  InstantiationEngine* d_instEngine;
  /** map from quantified formulas to list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** solutions for instantiation constants */
  std::map< Node, Node > d_solved_ic;
  /** list of lemmas */
  std::vector< Node > d_lemmas;
public:
  Instantiatior(context::Context* c, InstantiationEngine* ie);
  ~Instantiatior();

  /** get corresponding theory for this instantiator */
  virtual Theory* getTheory() = 0;
  /** check function, assertion is asserted to theory */
  virtual void check( Node assertion ){}

  /** prepare instantiation method
    * post condition: set d_solved_ic and d_lemmas fields */
  virtual bool prepareInstantiation(){ return false; }
  /** node n is instantiation-ready */
  bool isInstantiationReady( Node n );

  /** helper functions for lemmas */
  unsigned int getNumLemmas() { return d_lemmas.size(); }
  Node getLemma( int i ) { return d_lemmas[i]; }
  void clearLemmas() { d_lemmas.clear(); }
};/* class Instantiatior */

class InstantiationEngine
{
  friend class ::CVC4::TheoryEngine;
private:
  typedef context::CDMap< Node, bool, NodeHashFunction > BoolMap;

  /** theory instantiator objects for each theory */
  theory::Instantiatior* d_instTable[theory::THEORY_LAST];
  /** reference to theory engine object */
  TheoryEngine* d_te;
  /** map from universal quantifiers to the list of variables */
  std::map< Node, std::vector< Node > > d_vars;
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** map from universal quantifiers to the list of skolem constants */
  std::map< Node, std::vector< Node > > d_skolem_constants;
  /** instantiation constants to universal quantifiers */
  std::map< Node, Node > d_inst_constants_map;
  /** map from universal quantifiers to their counterexample literals */
  std::map< Node, Node > d_counterexamples;
  /** map from universal quantifiers to their counterexample body */
  std::map< Node, Node > d_counterexample_body;
  /** map from quantifiers to their counterexample equivalents */
  std::map< Node, Node > d_quant_to_ceq;
  /** stores whether a quantifier is a subquantifier of another */
  std::map< Node, std::vector< Node > > d_subquant;   //DO_THIS
  /** map from quantifiers to whether they are active */
  BoolMap d_active;

  void associateNestedQuantifiers( Node n, Node cen );
public:
  InstantiationEngine(context::Context* c, TheoryEngine* te);
  ~InstantiationEngine();
  
  theory::Instantiatior* getInstantiator( Theory* t ) { return d_instTable[t->getId()]; }

  void instantiate( Node f, std::vector< Node >& terms, OutputChannel* out );

  void getInstantiationConstantsFor( Node f, std::vector< Node >& ics, Node& cebody );
  void getSkolemConstantsFor( Node f, std::vector< Node >& scs );
  void getVariablesFor( Node f, std::vector< Node >& vars );
  bool doInstantiation( OutputChannel* out );

  /** get the corresponding counterexample literal for quantified formula node n */
  Node getCounterexampleLiteralFor( Node n );
  /** get the corresponding countexample equivalent for quantified formula, 
      where n is a nested quantifier */
  Node getCounterexampleQuantifier( Node n ) { return d_quant_to_ceq[n]; }
  /** mark literals as dependent */
  void registerLiterals( Node n, Node f, OutputChannel* out );
  /** set active */
  void setActive( Node n, bool val ) { d_active[n] = val; }
  /** get active */
  bool getActive( Node n ) { return d_active[n]; }
  /** is subquantifier */
  bool isSubQuantifier( Node sub, Node f );
};/* class InstantiationEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

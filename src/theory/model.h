/*********************                                                        */
/*! \file model.h
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
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_H
#define __CVC4__MODEL_H

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

/** this class stores a representative set */
class RepSet {
public:
  RepSet(){}
  ~RepSet(){}
  std::map< TypeNode, std::vector< Node > > d_type_reps;
  std::map< Node, int > d_tmap;
  /** clear the set */
  void clear();
  /** has type */
  bool hasType( TypeNode tn ) { return d_type_reps.find( tn )!=d_type_reps.end(); }
  /** add representative for type */
  void add( Node n );
  /** set the representatives for type */
  void set( TypeNode t, std::vector< Node >& reps );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) { return d_tmap.find( n )!=d_tmap.end() ? d_tmap[n] : -1; }
  /** debug print */
  void debugPrint( const char* c );
};

//representative domain
typedef std::vector< int > RepDomain;

/** Model class
 *    For Model m, should call m.initialize() before using
 */
class Model
{
protected:
  /** pointer to theory engine */
  TheoryEngine* d_te;
  /** process initialize */
  virtual void processInitialize() {}
  /** add term */
  virtual void addTerm() {}
public:
  /** equality engine containing all known equalities/disequalities */
  eq::EqualityEngine d_equalityEngine;
  /** use constants for representatives */
  bool d_useConstantReps;
  /** map of representatives of equality engine to used representatives */
  std::map< Node, Node > d_reps;
  /** representative alphabet */
  RepSet d_ra;
  //true/false nodes
  Node d_true;
  Node d_false;
public:
  Model( TheoryEngine* te, std::string name );
  virtual ~Model(){}
  /** initialize */
  void initialize();
  /** get value */
  Node getValue( TNode n );
  /** get value */
  virtual Node getInterpretedValue( TNode n ) = 0;
  /** get arbitrary value */
  Node getArbitraryValue( TypeNode tn, std::vector< Node >& exclude );
public:
  /** assert equality */
  void assertEquality( Node a, Node b, bool polarity );
  /** assert predicate */
  void assertPredicate( Node a, bool polarity );
  /** assert equality engine */
  void assertEqualityEngine( eq::EqualityEngine* ee );
public:
  //queries about equality
  bool hasTerm( Node a );
  Node getRepresentative( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
public:
  /** print representative function */
  void printRepresentative( const char* c, Node r );
};

//default model class: extends model arbitrarily
class DefaultModel : public Model
{
public:
  DefaultModel( TheoryEngine* te, std::string name );
  virtual ~DefaultModel(){}
public:
  Node getInterpretedValue( TNode n );
};

//incomplete model class: does not extend model
class IncompleteModel : public Model
{
public:
  IncompleteModel( TheoryEngine* te, std::string name ) : Model( te, name ){}
  virtual ~IncompleteModel(){}
public:
  Node getInterpretedValue( TNode n ) { return Node::null(); }
};

}
}

#endif
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
  /** set the representatives for type */
  void set( TypeNode t, std::vector< Node >& reps );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) { return d_tmap.find( n )!=d_tmap.end() ? d_tmap[n] : -1; }
  /** debug print */
  void debugPrint( const char* c, QuantifiersEngine* qe );
};

//representative domain
typedef std::vector< int > RepDomain;

class Model
{
public:
  /** equality engine containing all known equalities/disequalities */
  eq::EqualityEngine d_equalityEngine;
  /** list of all terms for each operator */
  std::map< Node, std::vector< Node > > d_terms;
  /** representative alphabet */
  RepSet d_ra;
public:
  Model( context::Context* c );
  virtual ~Model(){}
  /** get value */
  virtual Node getValue( TNode n ) = 0;
public:
  /** assert equality */
  void assertEquality( Node a, Node b, bool polarity );
  /** assert predicate */
  void assertPredicate( Node a, bool polarity );
  /** assert equality engine */
  void assertEqualityEngine( eq::EqualityEngine* ee );
public:
  /** print representative function */
  static void printRepresentative( const char* c, QuantifiersEngine* qe, Node r );
};

class ModelBuilder
{
public:
  ModelBuilder(){}
  virtual ~ModelBuilder(){}
  virtual void buildModel( Model& m ) = 0;
};

}
}

#endif
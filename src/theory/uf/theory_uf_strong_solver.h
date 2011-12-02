/*********************                                                        */
/*! \file theory_uf_instantiator.h
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
 ** \brief Theory uf instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_STRONG_SOLVER_H
#define __CVC4__THEORY_UF_STRONG_SOLVER_H

#include "theory/theory.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdlist.h"
#include "context/cdlist_context_memory.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUF;

class StrongSolverTheoryUf{
protected:
  /** theory uf pointer */
  TheoryUF* d_th;

  /** information for incremental conflict/clique finding */
  class ConflictFind {
  private:
    /** theory uf pointer */
    TheoryUF* d_th;
    /** region class */
    class Region {
    public:
      //constructor
      Region( Node n ){
        d_reps[n] = true;
        d_reps_size = 1;
        d_total_disequalities_size[0] = 0;
        d_total_disequalities_size[1] = 0;
      }
      ~Region(){}
      //number of representatives in this region
      int d_reps_size;
      //disequalities size
      std::map< Node, int > d_disequalities_size[2];
      //total disequality size (internal and external)
      int d_total_disequalities_size[2];
      //representatives 
      std::map< Node, bool > d_reps;
      //disequalities (internal and external)
      std::map< Node, std::map< Node, bool > > d_disequalities[2];
      // has representative
      bool hasRep( Node n ) { return d_reps.find( n )!=d_reps.end() && d_reps[n]; }
      //merge with other region
      void merge( Region& r );
      //take node from region
      void takeNode( Region& r, Node n );
      /** merge */
      void setEqual( Node a, Node b );
      //set n1 != n2 to value 'valid', type is whether it is internal/external
      void setDisequal( Node n1, Node n2, int type, bool valid );
      // is disequal
      bool isDisequal( Node n1, Node n2, int type );
    };
    /** vector of regions */
    std::vector< Region > d_regions;
    /** whether the region is valid */
    std::vector< bool > d_valid;
    /** map from Nodes to index of d_regions they exist in, -1 means invalid */
    std::map< Node, int > d_regions_map;
    /** merge regions */
    void mergeRegions( int ai, int bi );
  public:
    ConflictFind(){}
    ConflictFind( TheoryUF* th ) : d_th( th ){}
    ~ConflictFind(){}
    /** cardinality operating with */
    int d_cardinality;
    /** new node */
    void newEqClass( Node n );
    /** merge */
    void merge( Node a, Node b );
    /** unmerge */
    void undoMerge( Node a, Node b );
    /** assert terms are disequal */
    void assertDisequal( Node a, Node b );
    /** check */
    void check( Theory::Effort level );
  };
  /** conflict find structure, one for each type */
  std::map< TypeNode, ConflictFind > d_conf_find;
public:
  StrongSolverTheoryUf(context::Context* c, TheoryUF* th);
  ~StrongSolverTheoryUf() {}
  /** new node */
  void newEqClass( Node n );
  /** merge */
  void merge( Node a, Node b );
  /** unmerge */
  void undoMerge( Node a, Node b );
  /** assert terms are disequal */
  void assertDisequal( Node a, Node b );
  /** check */
  void check( Theory::Effort level );
public:
  /** identify */
  std::string identify() const { return std::string("StrongSolverTheoryUf"); }
  /** debug print */
  void debugPrint( const char* c );
public:
  /** set cardinality for sort */
  void setCardinality( TypeNode t, int c );
  /** get cardinality for sort */
  int getCardinality( TypeNode t );
};/* class StrongSolverTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

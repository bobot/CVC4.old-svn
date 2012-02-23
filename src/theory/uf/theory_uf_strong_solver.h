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
#include "theory/quantifiers_engine.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdlist.h"
#include "context/cdlist_context_memory.h"

#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUF;

class StrongSolverTheoryUf{
protected:
  typedef context::CDMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
  typedef context::CDList<bool> BoolList;
public:
  /** information for incremental conflict/clique finding for a particular sort */
  class ConflictFind {
  public:
    /** a partition of the current equality graph for which cliques can occur internally */
    class Region {
    public:
      /** conflict find pointer */
      ConflictFind* d_cf;
      /** information stored about each node in region */ 
      class RegionNodeInfo {
      public:
        /** disequality list for node */
        class DiseqList {
        public:
          DiseqList( context::Context* c ) : d_size( c, 0 ), d_disequalities( c ){}
          ~DiseqList(){}
          context::CDO< unsigned > d_size;
          NodeBoolMap d_disequalities; 
          void setDisequal( Node n, bool valid ){
            Assert( d_disequalities.find( n )==d_disequalities.end() || d_disequalities[n]!=valid );
            d_disequalities[ n ] = valid;
            d_size = d_size + ( valid ? 1 : -1 );
          }
        };
      private:
        DiseqList d_internal;
        DiseqList d_external;
      public:
        /** constructor */
        RegionNodeInfo( context::Context* c ) : d_internal( c ), d_external( c ), d_valid( c, true ){
          d_disequalities[0] = &d_internal;
          d_disequalities[1] = &d_external;
        }
        ~RegionNodeInfo(){}
        context::CDO< bool > d_valid;
        DiseqList* d_disequalities[2];

        int getNumDisequalities() { return d_disequalities[0]->d_size + d_disequalities[1]->d_size; }
        int getNumExternalDisequalities() { return d_disequalities[0]->d_size; }
        int getNumInternalDisequalities() { return d_disequalities[1]->d_size; }
      };
      ///** end class RegionNodeInfo */
    private:
      //a postulated clique
      NodeBoolMap d_testClique;
      context::CDO< unsigned > d_testCliqueSize;
      //disequalities needed for this clique to happen
      NodeBoolMap d_splits;
      context::CDO< unsigned > d_splitsSize;
    private:
      //number of valid representatives in this region
      context::CDO< unsigned > d_reps_size;
      //total disequality size (external)
      context::CDO< unsigned > d_total_diseq_external;
      //total disequality size (internal)
      context::CDO< unsigned > d_total_diseq_internal;
    public:
      //constructor
      Region( ConflictFind* cf, context::Context* c ) : d_cf( cf ), d_testClique( c ), d_testCliqueSize( c, 0 ),
        d_splits( c ), d_splitsSize( c, 0 ), d_reps_size( c, 0 ), d_total_diseq_external( c, 0 ),
        d_total_diseq_internal( c, 0 ), d_valid( c, true ) { 
      }
      ~Region(){}
      //region node infomation
      std::map< Node, RegionNodeInfo* > d_nodes;
      //whether region is valid
      context::CDO< bool > d_valid;
    public:
      //get num reps
      int getNumReps() { return d_reps_size; }
      // has representative
      bool hasRep( Node n ) { return d_nodes.find( n )!=d_nodes.end() && d_nodes[n]->d_valid; }
      //take node from region
      void takeNode( Region* r, Node n );
      //merge with other region
      void combine( Region* r );
      /** set rep */
      void setRep( Node n, bool valid );
      /** merge */
      void setEqual( Node a, Node b );
      //set n1 != n2 to value 'valid', type is whether it is internal/external
      void setDisequal( Node n1, Node n2, int type, bool valid );
      // is disequal
      bool isDisequal( Node n1, Node n2, int type );
    public:
      /** get must merge */
      bool getMustCombine( int cardinality );
      /** check for cliques */
      bool check( Theory::Effort level, unsigned cardinality, std::vector< Node >& clique );
      /** has splits */
      bool hasSplits() { return d_splitsSize>0; }
      /** get split */
      Node getBestSplit();
      /** get representatives */
      void getRepresentatives( std::vector< Node >& reps );
      //print debug
      void debugPrint( const char* c, bool incClique = false );
    };
  private:
    /** theory uf pointer */
    TheoryUF* d_th;
    /** regions used to d_region_index */
    context::CDO< unsigned > d_regions_index;
    /** vector of regions */
    std::vector< Region* > d_regions;
    /** map from Nodes to index of d_regions they exist in, -1 means invalid */
    NodeIntMap d_regions_map;
    /** regions used to d_region_index */
    context::CDO< unsigned > d_disequalities_index;
    /** list of all disequalities */
    std::vector< Node > d_disequalities;
    /** number of representatives in all regions */
    context::CDO< unsigned > d_reps;
    /** whether two terms are ambiguous (indexed by equalities) */
    NodeBoolMap d_term_amb;
  private:
    /** merge regions */
    void combineRegions( int ai, int bi );
    /** move node n to region ri */
    void moveNode( Node n, int ri );
    /** get number of disequalities from node n to region ri */
    int getNumDisequalitiesToRegion( Node n, int ri );
    /** get number of disequalities from Region r to other regions */
    void getDisequalitiesToRegions( int ri, std::map< int, int >& regions_diseq );
    /** check if we need to combine region ri */
    bool checkRegion( int ri, bool rec = true );
    /** explain clique */
    void explainClique( std::vector< Node >& clique, OutputChannel* out );
    /** is valid */
    bool isValid( int ri ) { return ri>=0 && ri<(int)d_regions_index && d_regions[ ri ]->d_valid; }
    /** check ambiguous terms */
    bool disambiguateTerms( OutputChannel* out );
    /** cardinality operating with */
    int d_cardinality;
    /** type */
    TypeNode d_type;
  public:
    ConflictFind( TypeNode tn, context::Context* c, TheoryUF* th ) : 
        d_th( th ), d_regions_index( c, 0 ), d_regions_map( c ), d_disequalities_index( c, 0 ), 
        d_reps( c, 0 ), d_term_amb( c ), d_cardinality( 0 ), d_type( tn ){}
    ~ConflictFind(){}
    /** new node */
    void newEqClass( Node n );
    /** merge */
    void merge( Node a, Node b );
    /** unmerge */
    void undoMerge( Node a, Node b );
    /** assert terms are disequal */
    void assertDisequal( Node a, Node b, Node reason );
    /** check */
    void check( Theory::Effort level, OutputChannel* out );
    //print debug
    void debugPrint( const char* c );
    /** set cardinality */
    void setCardinality( int c );
    /** get cardinality */
    int getCardinality() { return d_cardinality; }
    /** get representatives */
    void getRepresentatives( std::vector< Node >& reps );
    /** get cardinality lemma */
    Node getCardinalityLemma();
  public:
    /** is cardinality strict */
    bool d_isCardinalityStrict;
    /** cardinality lemma term */ 
    Node d_cardinality_lemma_term;
  public:
    /** get number of regions (for debugging) */
    int getNumRegions();
  }; /** class ConflictFind */
private:
  /** The output channel for the strong solver. */
  OutputChannel* d_out;
  /** theory uf pointer */
  TheoryUF* d_th;
  /** conflict find structure, one for each type */
  std::map< TypeNode, ConflictFind* > d_conf_find;
public:
  StrongSolverTheoryUf(context::Context* c, context::UserContext* u, OutputChannel& out, TheoryUF* th);
  ~StrongSolverTheoryUf() {}
  /** new node */
  void newEqClass( Node n );
  /** merge */
  void merge( Node a, Node b );
  /** unmerge */
  void undoMerge( Node a, Node b );
  /** assert terms are disequal */
  void assertDisequal( Node a, Node b, Node reason );
  /** assert cardinality */
  void assertCardinality( Node c );
public:
  /** check */
  void check( Theory::Effort level );
  /** preregister a term */
  void preRegisterTerm( TNode n );
public:
  /** identify */
  std::string identify() const { return std::string("StrongSolverTheoryUf"); }
  //print debug
  void debugPrint( const char* c );
public:
  /** set cardinality for sort */
  void setCardinality( TypeNode t, int c, bool isStrict = false );
  /** get cardinality for sort */
  int getCardinality( TypeNode t );
  /** get representatives */
  void getRepresentatives( TypeNode t, std::vector< Node >& reps );

  class Statistics {
  public:
    IntStat d_clique_lemmas;
    IntStat d_split_lemmas;
    IntStat d_disamb_term_lemmas;
    Statistics();
    ~Statistics();
  };
  /** statistics class */
  Statistics d_statistics;

  /** is relavant type */
  static bool isRelevantType( TypeNode t );
  /** are types related? */
  bool areTypesRelated( TypeNode t1, TypeNode t2 ) { 
    return d_type_relate[t1].find( t2 )!=d_type_relate[t1].end() && d_type_relate[t1][t2]; 
  }
private:
  /** Types whose cardinality constraints are related to one another:
      A type T1 is related to a type T2 if there exists a term whose top symbol is a
      function of type ( ... x T1 x ... ) -> T2, or vice versa.
  */
  std::map< TypeNode, std::map< TypeNode, bool > > d_type_relate;
};/* class StrongSolverTheoryUf */





//instantiation strategies

class InstStrategyFinteModelFind : public InstStrategy{
private:
  /** representative alphabet */
  class RepAlphabet {
  public:
    std::map< TypeNode, std::vector< Node > > d_type_reps;
    std::map< Node, int > d_indicies;
    void set( TypeNode t, std::vector< Node >& reps );
  };
  /** partial instantiation set */
  class PartialInstSet {
  public:
    PartialInstSet( RepAlphabet* ra, Node f ) : d_ra( ra ), d_f( f ){
      for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
        d_index.push_back( 0 );
      }
    }
    ~PartialInstSet(){}
    RepAlphabet* d_ra;
    Node d_f;
    std::vector< int > d_index;
    bool didCurrentInstantiation( PartialInstSet* pi );
    void increment();
    bool isFinished();
    void getMatch( QuantifiersEngine* ie, InstMatch& m );
    Node getTerm( int i );
  };
  /** was the current instantiation of this already done? */
  bool didCurrentInstantiation( PartialInstSet* pi );
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** map from types to sets of representatives */
  RepAlphabet* d_curr_ra;
  /** finding model */
  context::CDO< bool > d_finding_model;
  /** map of current used instantiations */
  std::map< Node, std::vector< PartialInstSet* > > d_inst_group;
public:
  InstStrategyFinteModelFind( context::Context* c, InstantiatorTheoryUf* th, QuantifiersEngine* ie );
  ~InstStrategyFinteModelFind(){}
  void resetInstantiationRound();
  int process( Node f, int effort );
  /** identify */
  std::string identify() const { return std::string("FinteModelFind"); }
};


}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

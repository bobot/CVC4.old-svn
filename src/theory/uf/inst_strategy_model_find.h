/*********************                                                        */
/*! \file inst_strategy_model_find.h
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
 ** \brief inst strategy model find
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_STRATEGY_MODEL_FIND_H
#define __CVC4__INST_STRATEGY_MODEL_FIND_H

#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace uf {

class RepAlphabetIterator;

/** this class stores a representative alphabet */
class RepAlphabet {
public:
  RepAlphabet(){}
  RepAlphabet( RepAlphabet& ra, QuantifiersEngine* ie );
  ~RepAlphabet(){}
  std::map< TypeNode, std::vector< Node > > d_type_reps;
  std::map< Node, int > d_tmap;
  void set( TypeNode t, std::vector< Node >& reps );
  /** returns true if we did this instantiation */
  bool didInstantiation( RepAlphabetIterator& riter );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) { return d_tmap.find( n )!=d_tmap.end() ? d_tmap[n] : -1; }
  /** debug print */
  void debugPrint( const char* c );
};

class RepAlphabetIterator;

/** this class determines which subset of instantiations should be tried by a RepAlphabetIterator */
class RAIFilter
{
private:
  /** restriction trie class stores a set of restricted instantiation values */
  class RestrictionTrie
  {
  public:
    typedef std::pair< int, int > InstValue;
  public:
    bool d_active;
    std::map< int, std::map< int, RestrictionTrie > > d_data;
  private:
    void addRestriction2( std::vector< InstValue >& restriction, int index );
    int accept2( std::vector< int >& index, int checkIndex );
  public:
    RestrictionTrie() : d_active( false ){}
    ~RestrictionTrie(){}
    void addRestriction( std::vector< InstValue >& restriction ){ addRestriction2( restriction, 0 ); }
    int accept( std::vector< int >& index ) { return accept2( index, (int)index.size()-1 ); }
  };
  //the restriction trie
  RestrictionTrie d_rt;
private:
  //collect predicate restrictions
  void collectPredicateRestrictions( QuantifiersEngine* qe, Node n, Node pol, RepAlphabet* ra, TermArgTrie* tat, int index,
                                     std::map< int, int >& restriction );
public:
  RAIFilter(){}
  ~RAIFilter(){}
  //initialize with this quantifier
  void initialize( QuantifiersEngine* qe, Node f, RepAlphabet* ra );
  //if the current value of rai->d_index is disallowed, this function will 
  // return the highest variable number that should be incremented.
  // Otherwise, it will return -1.
  int acceptCurrent( RepAlphabetIterator* rai );
};

/** this class iterates over a RepAlphabet */
class RepAlphabetIterator {
private:
  //filte, used as oracle to determine if instantiations need not be tried
  RAIFilter d_raif;
public:
  RepAlphabetIterator( QuantifiersEngine* qe, Node f, RepAlphabet* ra );
  ~RepAlphabetIterator(){}
  Node d_f;
  RepAlphabet* d_ra;
  std::vector< int > d_index;
  void increment( QuantifiersEngine* qe );
  bool isFinished();
  void getMatch( QuantifiersEngine* qe, InstMatch& m );
  Node getTerm( int i );
  int getNumTerms() { return d_f[0].getNumChildren(); }
};

//instantiation strategies
class InstStrategyFinteModelFind : public InstStrategy{
private:
  /** was the current instantiation of this already done? */
  bool didInstantiation( Node f, RepAlphabetIterator& riter );
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_ith;
  /** strong solver class */
  StrongSolverTheoryUf* d_ss;
  /** map of current used instantiations */
  std::vector< RepAlphabet > d_inst_group;
  std::vector< RepAlphabet > d_inst_group_temp;
  std::vector< std::vector< Node > > d_inst_nodes;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e, int limitInst );
public:
  InstStrategyFinteModelFind( context::Context* c, InstantiatorTheoryUf* ith, StrongSolverTheoryUf* ss, QuantifiersEngine* ie );
  ~InstStrategyFinteModelFind(){}
  /** identify */
  std::string identify() const { return std::string("FinteModelFind"); }
};

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

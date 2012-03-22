/*********************                                                        */
/*! \file inst_match.h
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
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_MATCH_H
#define __CVC4__INST_MATCH_H

#include "theory/theory.h"
#include "util/hash.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

//#define USE_EFFICIENT_E_MATCHING

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
namespace uf{
  class InstantiatorTheoryUf;
  class TheoryUF;
}

class CandidateGenerator
{
public:
  CandidateGenerator(){}
  ~CandidateGenerator(){}

  /** Get candidates functions.  These set up a context to get all match candidates.
      cg->reset( eqc );
      do{
        Node cand = cg->getNextCandidate();
        //.......
      }while( !cand.isNull() );
      
      eqc is the equivalence class you are searching in
  */
  virtual void addCandidate( Node n ) {}
  virtual void resetInstantiationRound() = 0;
  virtual void reset( Node eqc ) = 0;
  virtual Node getNextCandidate() = 0;
};

class CandidateGeneratorQueue : public CandidateGenerator
{
private:
  std::vector< Node > d_candidates;
public:
  CandidateGeneratorQueue(){}
  ~CandidateGeneratorQueue(){}

  void addCandidate( Node n ) { d_candidates.push_back( n ); }

  void resetInstantiationRound(){}
  void reset( Node eqc );
  Node getNextCandidate();
};

class EqualityQuery
{
public:
  EqualityQuery(){}
  ~EqualityQuery(){}
  /** general queries about equality */
  virtual Node getRepresentative( Node a ) = 0;
  virtual bool areEqual( Node a, Node b ) = 0;
  virtual bool areDisequal( Node a, Node b ) = 0;
  /** internal representative
      Returns a term in the equivalence class of "a" that does 
      not contain instantiation constants, if such a term exists. 
      Otherwise, return "a" itself.
   */
  virtual Node getInternalRepresentative( Node a ) = 0;
};

class InstMatch
{
public:
  static int d_im_count;
public:
  InstMatch();
  InstMatch( InstMatch* m );

  /** set the match of v to m */
  bool setMatch( EqualityQuery* q, Node v, Node m );
  /** fill all unfilled values with m */
  bool add( InstMatch& m );
  /** if compatible, fill all unfilled values with m and return true 
      return false otherwise */
  bool merge( EqualityQuery* q, InstMatch& m );
  /** debug print method */
  void debugPrint( const char* c );
  /** make internal: ensure that no term in d_map contains instantiation constants */
  void makeInternal( EqualityQuery* q );
  /** make representative */
  void makeRepresentative( EqualityQuery* q );
  /** compute d_match */
  void computeTermVec( QuantifiersEngine* ie, const std::vector< Node >& vars, std::vector< Node >& match );
  /** compute d_match */
  void computeTermVec( const std::vector< Node >& vars, std::vector< Node >& match );
  /** clear */
  void clear(){ d_map.clear(); }
  /** is_empty */
  bool empty(){ return d_map.empty(); }
  /* map from variable to ground terms */
  std::map< Node, Node > d_map;
};

class InstMatchTrie
{
private:
  /** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
  void addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index );
  /** exists match */
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, int index );
  /** the data */
  std::map< Node, InstMatchTrie > d_data;
public:
  InstMatchTrie(){}
  ~InstMatchTrie(){}
public:
  /** add match m for quantifier f, take into account equalities, return true if successful */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false );
};


class InstMatchGenerator
{
private:
  /** candidate generator */
  CandidateGenerator* d_cg;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  std::vector< int > d_children_index;
  /** partial vector */
  std::vector< InstMatch > d_partial;
  /** eq class */
  Node d_eq_class;
  /** initialize pattern */
  void initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe );
  void initializePattern( Node pat, QuantifiersEngine* qe );
  /** for arithmetic */
  bool initializePatternArithmetic( Node n );
  bool getMatchArithmetic( Node t, InstMatch& m, QuantifiersEngine* qe );
public:
  enum {
    MATCH_GEN_DEFAULT = 0,     
    MATCH_GEN_EFFICIENT_E_MATCH,   //generate matches via Efficient E-matching for SMT solvers
    MATCH_GEN_LIT_MATCH,           //generate matches via literal-level matching
  };
private:
  /** for arithmetic matching */
  std::map< Node, Node > d_arith_coeffs;
private:
  /** get the next match.  must call d_cg->reset( ... ) before using. 
      only valid for use where !d_match_pattern.isNull().
  */
  bool getNextMatch2( InstMatch& m, QuantifiersEngine* qe );
public:
  /** get the match against ground term or formula t.
      d_match_mattern and t should have the same shape.
      only valid for use where !d_match_pattern.isNull().
  */
  bool getMatch( Node t, InstMatch& m, QuantifiersEngine* qe );

  /** constructors */
  InstMatchGenerator( Node pat, QuantifiersEngine* qe, int matchOption = 0 );
  InstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption = 0 );
  /** destructor */
  ~InstMatchGenerator(){}
  /** The pattern we are producing matches for.
      If null, this is a multi trigger that is merging matches from d_children.
  */
  Node d_pattern;
  /** match pattern */
  Node d_match_pattern;
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  void reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. */
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe );
  /** return true if whatever Node is subsituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars);
};


//a collect of nodes representing a trigger
class Trigger {
public:
  static int trCount;
private:
  /** computation of variable contains */
  static std::map< Node, std::vector< Node > > d_var_contains;
  static void computeVarContains( Node n ) { computeVarContains2( n, n ); }
  static void computeVarContains2( Node n, Node parent );
private:
  /** the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** the quantifier this trigger is for */
  Node d_f;
  /** match generators */
  InstMatchGenerator* d_mg;
private:
  /** a trie of triggers */
  class TrTrie
  {
  private:
    Trigger* getTrigger2( std::vector< Node >& nodes );
    void addTrigger2( std::vector< Node >& nodes, Trigger* t );
  public:
    TrTrie() : d_tr( NULL ){}
    Trigger* d_tr;
    std::map< Node, TrTrie* > d_children;
    Trigger* getTrigger( std::vector< Node >& nodes ){
      std::vector< Node > temp;
      temp.insert( temp.begin(), nodes.begin(), nodes.end() );
      std::sort( temp.begin(), temp.end() );
      return getTrigger2( temp );
    }
    void addTrigger( std::vector< Node >& nodes, Trigger* t ){
      std::vector< Node > temp;
      temp.insert( temp.begin(), nodes.begin(), nodes.end() );
      std::sort( temp.begin(), temp.end() );
      return addTrigger2( temp, t );
    }
  };
  /** all triggers will be stored in this trie */
  static TrTrie d_tr_trie;
private:
  /** trigger constructor */
  Trigger( QuantifiersEngine* ie, Node f, std::vector< Node >& nodes, int matchOption = 0 );
public:
  ~Trigger(){}
public:
  std::vector< Node > d_nodes;
public:
  void debugPrint( const char* c );
  InstMatchGenerator* getGenerator() { return d_mg; }
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound();
  /** reset, eqc is the equivalence class to search in (search in any if eqc=null) */
  void reset( Node eqc );
  /** get next match.  must call reset( eqc ) once before this function. */
  bool getNextMatch( InstMatch& m );
  /** get the match against ground term or formula t.
      the trigger and t should have the same shape.
      Currently the trigger should not be a multi-trigger.
  */
  bool getMatch( Node t, InstMatch& m);
  /** return true if whatever Node is subsituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars){
    return d_mg->nonunifiable(t,vars);
  };
public:
  /** add all available instantiations exhaustively, in any equivalence class 
      if limitInst>0, limitInst is the max # of instantiations to try */
  int addInstantiations( InstMatch& baseMatch, int instLimit = 0, bool addSplits = false );
  /** mkTrigger method
     ie     : quantifier engine;
     f      : forall something ....
     nodes  : (multi-)trigger
     matchOption : which policy to use for creating matches (one of InstMatchGenerator::MATCH_GEN_* )
     keepAll: don't remove unneeded patterns;
     trOption : policy for dealing with triggers that already existed (see below)
  */
  enum{
    TR_MAKE_NEW,    //make new trigger even if it already may exist
    TR_GET_OLD,     //return a previous trigger if it had already been created
    TR_RETURN_NULL  //return null if a duplicate is found
  };
  static Trigger* mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, 
                             int matchOption = 0, bool keepAll = true, int trOption = TR_MAKE_NEW ); 
private:  
  static bool isUsable( Node n, Node f );
public:
  /** is usable trigger */
  static bool isUsableTrigger( std::vector< Node >& nodes, Node f );
  static bool isUsableTrigger( Node n, Node f );
  /** filter all nodes that have instances */
  static void filterInstances( std::vector< Node >& nodes );
  /** -1: n1 is an instance of n2, 1: n1 is an instance of n2 */
  static int isInstanceOf( Node n1, Node n2 );
  /** variables subsume, return true if n1 contains all free variables in n2 */
  static bool isVariableSubsume( Node n1, Node n2 );

  inline void toStream(std::ostream& out) const {
    if (d_mg->d_match_pattern.isNull()) out << "MultiTrigger (TODO)";
    else out << "[" << d_mg->d_match_pattern << "]";
  }
};

inline std::ostream& operator<<(std::ostream& out, const Trigger & tr) {
  tr.toStream(out);
  return out;
}


}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

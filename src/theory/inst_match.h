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
  /** make complete */
  void makeComplete( Node f, QuantifiersEngine* qe );
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
public:
  class ImtIndexOrder{
  public:
    std::vector< int > d_order;
  };
private:
  /** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
  void addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index, ImtIndexOrder* imtio );
  /** exists match */
  bool existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, int index, ImtIndexOrder* imtio );
  /** the data */
  std::map< Node, InstMatchTrie > d_data;
public:
  InstMatchTrie(){}
  ~InstMatchTrie(){}
public:
  /** add match m for quantifier f, take into account equalities if modEq = true, 
      if imtio is non-null, this is the order to add to trie
      return true if successful 
  */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false, ImtIndexOrder* imtio = NULL );
};

class InstMatchTrieOrdered
{
private:
  InstMatchTrie::ImtIndexOrder* d_imtio;
  InstMatchTrie d_imt;
public:
  InstMatchTrieOrdered( InstMatchTrie::ImtIndexOrder* imtio ) : d_imtio( imtio ){}
  ~InstMatchTrieOrdered(){}
public:
  /** add match m, return true if successful */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false ){
    return d_imt.addInstMatch( qe, f, m, modEq, d_imtio );
  }
};

class IMGenerator
{
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  virtual void reset( Node eqc, QuantifiersEngine* qe ) = 0;
  /** get the next match.  must call reset( eqc ) before this function. */
  virtual bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** return true if whatever Node is subsituted for the variables the
      given Node can't match the pattern */
  virtual bool nonunifiable( TNode t, const std::vector<Node> & vars) = 0;
};


class InstMatchGenerator : public IMGenerator
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

class InstMatchGeneratorMulti : public IMGenerator
{
private:
  /** quantifier to use */
  Node d_f;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  /** inst match tries for each child */
  std::vector< InstMatchTrie > d_children_trie;
  /** whether need to calculate matches */
  bool d_calculate_matches;
  /** current matches calculated */
  std::vector< InstMatch > d_curr_matches;
  /** calculate matches */
  void calculateMatches( QuantifiersEngine* qe );
public:
  /** constructors */
  InstMatchGeneratorMulti( Node f, std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption = 0 );
  /** destructor */
  ~InstMatchGeneratorMulti(){}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  void reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. */
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe );
  /** return true if whatever Node is subsituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars) { return true; }
};


}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__INST_MATCH_H */

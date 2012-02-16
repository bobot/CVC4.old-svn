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
  virtual void reset( Node eqc ) = 0;
  virtual Node getNextCandidate() = 0;
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
  //virtual void requestCandidates( Node t, Node s, int op ) = 0;
  //virtual Node getNextCandidate( Node t, Node s, int op ) = 0;
  //virtual void finishCandidates( Node t, Node s, int op ) = 0;
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
  /** compute d_match */
  void computeTermVec( QuantifiersEngine* ie, std::vector< Node >& vars, std::vector< Node >& match );
  /** clear */
  void clear(){ d_map.clear(); }
  /* map from variable to ground terms */
  std::map< Node, Node > d_map;
};

class InstMatchGenerator
{
private:
  /** candidate generator */
  CandidateGenerator* d_cg;
  /** is literal matching */
  int d_isLitMatch;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  std::vector< int > d_children_index;
  /** partial vector */
  std::vector< InstMatch > d_partial;
  /** initialize pattern */
  void initializePattern( Node pat, QuantifiersEngine* qe );
  void initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe );
private:
  /** get the next match.  must call d_cg->reset( ... ) before using. 
      only valid for use where !d_match_pattern.isNull().
  */
  bool getNextMatch2( InstMatch& m, QuantifiersEngine* qe );
  /** get the match against ground term or formula t.
      d_match_mattern and t should have the same shape.
      only valid for use where !d_match_pattern.isNull().
  */
  bool getMatch( Node t, InstMatch& m, QuantifiersEngine* qe );
public:
  /** constructors */
  InstMatchGenerator( Node pat, QuantifiersEngine* qe, bool isLitMatch = false );
  InstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe, bool isLitMatch = false );
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
  /** is duplicate */
  Trigger* isDuplicate( std::vector< Node >& nodes );
  /** trigger constructor */
  Trigger( QuantifiersEngine* ie, Node f, std::vector< Node >& nodes, bool isLitMatch = false );
public:
  ~Trigger(){}
public:
  std::vector< Node > d_nodes;
  std::vector< Node > d_candidates;
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
public:
  /** add all available instantiations exhaustively, in any equivalence class */
  int addInstantiations( InstMatch& baseMatch, bool addSplits = false );
  /** mkTrigger method
     ie     : quantifier engine;
     f      : forall something ....
     nodes  : (multi-)trigger
     isLitMatch : use literal matching heuristics
     keepAll: don't remove unneeded patterns;
     checkDup : don't generate a trigger that has already been created
  */
  static Trigger* mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, 
                             bool isLitMatch = false, bool keepAll = true, bool checkDup = false ); 
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__INSTANTIATION_ENGINE_H */

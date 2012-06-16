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

#ifndef __CVC4__RR_INST_MATCH_H
#define __CVC4__RR_INST_MATCH_H

#include "theory/theory.h"
#include "util/hash.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "context/cdlist.h"

#include "theory/inst_match.h"

//#define USE_EFFICIENT_E_MATCHING

namespace CVC4 {
namespace theory {

namespace rrinst{

inline std::ostream& operator<<(std::ostream& out, const InstMatch& m) {
  m.toStream(out);
  return out;
}

/** trie for InstMatch objects */
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
public:
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
  /** get ordering */
  InstMatchTrie::ImtIndexOrder* getOrdering() { return d_imtio; }
  /** get trie */
  InstMatchTrie* getTrie() { return &d_imt; }
public:
  /** add match m, return true if successful */
  bool addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq = false ){
    return d_imt.addInstMatch( qe, f, m, modEq, d_imtio );
  }
};

template<bool modEq = false>
class InstMatchTrie2
{
private:

  class Tree {
  public:
    typedef std::hash_map< Node, Tree *, NodeHashFunction > MLevel;
    MLevel e;
    const size_t level; //context level of creation
    Tree() CVC4_UNDEFINED;
    const Tree & operator =(const Tree & t) CVC4_UNDEFINED;
    Tree(size_t l): level(l) {};
    ~Tree(){
      for(typename MLevel::iterator i = e.begin(); i!=e.end(); ++i)
        delete(i->second);
    };
  };


  typedef std::pair<Tree *, TNode> Mod;

  class CleanUp{
  public:
    inline void operator()(Mod * m){
      typename Tree::MLevel::iterator i = m->first->e.find(m->second);
      Assert (i != m->first->e.end()); //should not have been already removed
      m->first->e.erase(i);
    };
  };

  EqualityQuery* d_eQ;
  eq::EqualityEngine * d_eE;

  /* before for the order of destruction */
  Tree d_data;

  context::Context* d_context;
  context::CDList<Mod, CleanUp, std::allocator<Mod> > d_mods;


  typedef std::map<Node, Node>::const_iterator mapIter;

  /** add the substitution given by the iterator*/
  void addSubTree( Tree * root, mapIter current, mapIter end, size_t currLevel);
  /** test if it exists match, modulo uf-equations if modEq is true if
   *  return false the deepest point of divergence is put in [e] and
   *  [diverge].
   */
  bool existsInstMatch( Tree * root,
                        mapIter & current, mapIter & end,
                        Tree * & e, mapIter & diverge) const;

public:
  InstMatchTrie2(context::Context* c,  QuantifiersEngine* q);
  InstMatchTrie2(const InstMatchTrie2 &) CVC4_UNDEFINED;
  const InstMatchTrie2 & operator =(const InstMatchTrie2 & e) CVC4_UNDEFINED;
  /** add match m in the trie,
      modEq specify to take into account equalities,
      return true if it was never seen */
  bool addInstMatch( InstMatch& m);
};/* class InstMatchTrie2 */

/** base class for producing InstMatch objects */
class IMGenerator
{
public:
  /** reset instantiation round (call this at beginning of instantiation round) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  virtual void reset( Node eqc, QuantifiersEngine* qe ) = 0;
  /** get the next match.  must call reset( eqc ) before this function. */
  virtual bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** return true if whatever Node is subsituted for the variables the
      given Node can't match the pattern */
  virtual bool nonunifiable( TNode t, const std::vector<Node> & vars) = 0;
  /** add instantiations directly */
  virtual int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false ) = 0;
};


class InstMatchGenerator : public IMGenerator
{
public:
  static std::map< Node, std::map< Node, std::vector< InstMatchGenerator* > > > d_match_fails;
  /** set match fail */
  void setMatchFail( QuantifiersEngine* qe, Node n1, Node n2 );
private:
  /** candidate generator */
  inst::CandidateGenerator* d_cg;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  std::vector< int > d_children_index;
  /** partial vector */
  std::vector< InstMatch > d_partial;
  /** eq class */
  Node d_eq_class;
  /** for arithmetic matching */
  std::map< Node, Node > d_arith_coeffs;
  /** initialize pattern */
  void initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe );
  void initializePattern( Node pat, QuantifiersEngine* qe );
public:
  enum {
    //options for producing matches
    MATCH_GEN_DEFAULT = 0,     
    MATCH_GEN_EFFICIENT_E_MATCH,   //generate matches via Efficient E-matching for SMT solvers
    //others (internally used)
    MATCH_GEN_INTERNAL_ARITHMETIC,
    MATCH_GEN_INTERNAL_ERROR,
  };
private:
  /** get the next match.  must call d_cg->reset( ... ) before using. 
      only valid for use where !d_match_pattern.isNull().
  */
  bool getNextMatch2( InstMatch& m, QuantifiersEngine* qe, bool saveMatched = false );
  /** for arithmetic */
  bool getMatchArithmetic( Node t, InstMatch& m, QuantifiersEngine* qe );
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
  /** add instantiations */
  int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false );
};

/** smart multi-trigger implementation */
class InstMatchGeneratorMulti : public IMGenerator
{
private:
  /** indexed trie */
  typedef std::pair< std::pair< int, int >, InstMatchTrie* > IndexedTrie;
  /** collect instantiations */
  void collectInstantiations( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas, InstMatchTrie* tr, 
                              std::vector< IndexedTrie >& unique_var_tries,
                              int trieIndex, int childIndex, int endChildIndex, bool modEq );
  /** collect instantiations 2 */
  void collectInstantiations2( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas,
                               std::vector< IndexedTrie >& unique_var_tries,
                               int uvtIndex, InstMatchTrie* tr = NULL, int trieIndex = 0 );
private:
  /** var contains (variable indicies) for each pattern node */
  std::map< Node, std::vector< int > > d_var_contains;
  /** variable indicies contained to pattern nodes */
  std::map< int, std::vector< Node > > d_var_to_node;
  /** quantifier to use */
  Node d_f;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  /** inst match tries for each child */
  std::vector< InstMatchTrieOrdered > d_children_trie;
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
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) { return false; } 
  /** return true if whatever Node is subsituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars) { return true; }
  /** add instantiations */
  int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false );
};

/** smart (single)-trigger implementation */
class InstMatchGeneratorSimple : public IMGenerator
{
private:
  /** quantifier for match term */
  Node d_f;
  /** match term */
  Node d_match_pattern;
  /** add instantiations */
  void addInstantiations( InstMatch& m, QuantifiersEngine* qe, int& addedLemmas, 
                          int argIndex, TermArgTrie* tat, int instLimit, bool addSplits );
public:
  /** constructors */
  InstMatchGeneratorSimple( Node f, Node pat ) : d_f( f ), d_match_pattern( pat ){}
  /** destructor */
  ~InstMatchGeneratorSimple(){}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe ) {}
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  void reset( Node eqc, QuantifiersEngine* qe ) {}
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) { return false; } 
  /** return true if whatever Node is subsituted for the variables the
      given Node can't match the pattern */
  bool nonunifiable( TNode t, const std::vector<Node> & vars) { return true; }
  /** add instantiations */
  int addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false );
};

}/* CVC4::theory rrinst */

}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__RR_INST_MATCH_H */

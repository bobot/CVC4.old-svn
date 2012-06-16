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
#include "expr/node_manager.h"
#include "expr/node_builder.h"

//#define USE_EFFICIENT_E_MATCHING

namespace CVC4 {
namespace theory {

namespace rrinst{

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
  virtual void reset( TNode eqc ) = 0;
  virtual TNode getNextCandidate() = 0;
  /** add candidate to list of nodes returned by this generator */
  virtual void addCandidate( Node n ) {}
  /** call this at the beginning of each instantiation round */
  virtual void resetInstantiationRound() = 0;
public:
  /** legal candidate */
  static inline bool isLegalCandidate( TNode n ){
    return !n.getAttribute(NoMatchAttribute()) &&
      ( !Options::current()->cbqi || !n.hasAttribute(InstConstantAttribute())) &&
      ( !Options::current()->efficientEMatching || n.hasAttribute(AvailableInTermDb()) );
}

};

// /** candidate generator queue (for manual candidate generation) */
// class CandidateGeneratorQueue : public CandidateGenerator
// {
// private:
//   std::vector< Node > d_candidates;
//   int d_candidate_index;
// public:
//   CandidateGeneratorQueue() : d_candidate_index( 0 ){}
//   ~CandidateGeneratorQueue(){}

//   void addCandidate( Node n );

//   void resetInstantiationRound(){}
//   void reset( TNode eqc );
//   TNode getNextCandidate();
// };


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

template<bool modEq = false> class InstMatchTrie2;
template<bool modEq = false> class InstMatchTrie2Pairs;

template<bool modEq = false>
class InstMatchTrie2Gen
{
  friend class InstMatchTrie2<modEq>;
  friend class InstMatchTrie2Pairs<modEq>;

private:

  class Tree {
  public:
    typedef std::hash_map< Node, Tree *, NodeHashFunction > MLevel;
    MLevel e;
    const size_t level; //context level of creation
    Tree() CVC4_UNDEFINED;
    const Tree & operator =(const Tree & t){
      Assert(t.e.empty()); Assert(e.empty());
      Assert(t.level == level);
      return t;
    }
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

  /** add match m in the trie root
      return true if it was never seen */
  bool addInstMatch( InstMatch& m, Tree * root);

public:
  InstMatchTrie2Gen(context::Context* c,  QuantifiersEngine* q);
  InstMatchTrie2Gen(const InstMatchTrie2Gen &) CVC4_UNDEFINED;
  const InstMatchTrie2Gen & operator =(const InstMatchTrie2Gen & e) CVC4_UNDEFINED;
};

template<bool modEq>
class InstMatchTrie2
{
  typename InstMatchTrie2Gen<modEq>::Tree d_data;
  InstMatchTrie2Gen<modEq> d_backtrack;
public:
  InstMatchTrie2(context::Context* c,  QuantifiersEngine* q): d_data(0),
                                                              d_backtrack(c,q) {};
  InstMatchTrie2(const InstMatchTrie2 &) CVC4_UNDEFINED;
  const InstMatchTrie2 & operator =(const InstMatchTrie2 & e) CVC4_UNDEFINED;
  /** add match m in the trie,
      return true if it was never seen */
  inline bool addInstMatch( InstMatch& m){
    return d_backtrack.addInstMatch(m,&d_data);
  };

};/* class InstMatchTrie2 */

class Matcher
{
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset the term to match, return false if there is no such term */
  virtual bool reset( TNode n, InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** get the next match. If it return false once you shouldn't call
      getNextMatch again before doing a reset */
  virtual bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** If reset, or getNextMatch return false they remove from the
      InstMatch the binding that they have previously created */
};


class ApplyMatcher: public Matcher{
private:
  /** What to check first: constant and variable */
  std::vector< std::pair<TNode,size_t> > d_constants;
  std::vector< std::pair<TNode,size_t> > d_variables;
  /** children generators, only the sub-pattern which are
      neither a variable neither a constant appears */
  std::vector< std::pair<Matcher*,size_t> > d_childrens;
  /** the variable that have been set by this matcher (during its own reset) */
  std::vector< TNode > d_binded; /* TNode because the variable are already in d_pattern */
  /** the representant of the argument of the term given by the last reset */
  std::vector< Node > d_reps;
public:
  /** The pattern we are producing matches for */
  Node d_pattern;
public:
  /** constructors */
  ApplyMatcher( Node pat, QuantifiersEngine* qe);
  /** destructor */
  ~ApplyMatcher(){}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset the term to match */
  bool reset( TNode n, InstMatch& m, QuantifiersEngine* qe );
  /** get the next match. */
  bool getNextMatch(InstMatch& m, QuantifiersEngine* qe);
private:
  bool getNextMatch(InstMatch& m, QuantifiersEngine* qe, bool reset);
};


/* Match literal so you don't choose the equivalence class( */
class PatMatcher
{
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset the matcher, return false if there is no such term */
  virtual bool reset( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** get the next match. If it return false once you shouldn't call
      getNextMatch again before doing a reset */
  virtual bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** If reset, or getNextMatch return false they remove from the
      InstMatch the binding that they have previously created */
};

Matcher* mkMatcher( Node pat, QuantifiersEngine* qe );
PatMatcher* mkPattern( Node pat, QuantifiersEngine* qe );

/* Match literal so you don't choose the equivalence class( */
class PatsMatcher
{
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset the matcher, return false if there is no such term */
  virtual bool getNextMatch( QuantifiersEngine* qe ) = 0;
  virtual const InstMatch& getInstMatch() = 0;
  /** Add directly the instantiation to quantifiers engine */
  virtual int addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe, int instLimit, bool addSplits ) = 0;
};

PatsMatcher* mkPatterns( std::vector< Node > pat, QuantifiersEngine* qe );
PatsMatcher* mkPatternsEfficient( std::vector< Node > pat, QuantifiersEngine* qe );

/** return true if whatever Node is subsituted for the variables the
    given Node can't match the pattern */
bool nonunifiable( TNode t, TNode pat, const std::vector<Node> & vars);

class InstMatchGenerator;

// /* Base Generator: generate term for sub-term of pattern */
// class InstMatchGenerator
// {

// public:
//   static std::map< Node, std::map< Node, std::vector< InstMatchGenerator* > > > d_match_fails;
//   /** set match fail */
//   void setMatchFail( QuantifiersEngine* qe, Node n1, Node n2 );
// private:
//   /** candidate generator */
//   CandidateGenerator* d_cg;
//   /** policy to use for matching */
//   int d_matchPolicy;
//   /** children generators */
//   std::vector< InstMatchGenerator* > d_children;
//   std::vector< int > d_children_index;
//   /** partial vector */
//   std::vector< InstMatch > d_partial;
//   /** eq class */
//   Node d_eq_class;
//   /** for arithmetic matching */
//   std::map< Node, Node > d_arith_coeffs;
//   /** initialize pattern */
//   void initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe );
//   void initializePattern( Node pat, QuantifiersEngine* qe );
// private:
//   /** get the next match.  must call d_cg->reset( ... ) before using. 
//       only valid for use where !d_match_pattern.isNull().
//   */
//   bool getNextMatch2( InstMatch& m, QuantifiersEngine* qe, bool saveMatched = false );
//   /** for arithmetic */
//   bool getMatchArithmetic( Node t, InstMatch& m, QuantifiersEngine* qe );
// public:
//   /** get the match against ground term or formula t.
//       d_match_mattern and t should have the same shape.
//       only valid for use where !d_match_pattern.isNull().
//   */
//   bool getMatch( Node t, InstMatch& m, QuantifiersEngine* qe );

//   /** constructors */
//   InstMatchGenerator( Node pat, QuantifiersEngine* qe, int matchOption = 0 );
//   //  InstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption = 0 );
//   /** destructor */
//   ~InstMatchGenerator(){}
//   /** The pattern we are producing matches for.
//       If null, this is a multi trigger that is merging matches from d_children.
//   */
//   Node d_pattern;
//   /** match pattern */
//   Node d_match_pattern;
// public:
//   /** reset instantiation round (call this whenever equivalence classes have changed) */
//   void resetInstantiationRound( QuantifiersEngine* qe );
//   /** reset, eqc is the equivalence class to search in (any if eqc=null) */
//   void reset( Node eqc, QuantifiersEngine* qe );
//   /** get the next match.  must call reset( eqc ) before this function. */
//   bool getNextMatch( InstMatch& m, QuantifiersEngine* qe );
//   /** add instantiations */
//   int addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false );
// };

// /** base class for producing InstMatch objects.
//     They match at the level of the patterns */
// class IMGenerator
// {
// public:
//   /** reset instantiation round (call this at beginning of instantiation round) */
//   virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
//   /** get the next match.  must call reset( eqc ) before this function. */
//   virtual bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) = 0;
//   /** return true if whatever Node is subsituted for the variables the
//       given Node can't match the pattern */
//   virtual bool nonunifiable( TNode t, const std::vector<Node> & vars) = 0;
//   /** add instantiations directly */
//   virtual int addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false ) = 0;
// };

// class InstMatchGeneratorMonoSimple: public IMGenerator
// {
//   InstMatchGenerator img;
//   InstMatchGeneratorMonoSimple(TNode t, QuantifiersEngine* qe):
//     img(t[0],qe) {
//     Assert(t.getKind() == kind::INST_PATTERN);
//     Assert(t.getNumChildren() == 1);
//   };

//   void resetInstantiationRound( QuantifiersEngine* qe ){
//     img.resetInstantiationRound(qe);
//   };

//   /** get the next match.  must call reset( eqc ) before this function. */
//   bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
//     img.getNextMatch(m,qe);
//   };

//   /** return true if whatever Node is subsituted for the variables the
//       given Node can't match the pattern */
//   bool nonunifiable( TNode t, const std::vector<Node> & vars){
//     img.nonunifiable(t,vars);
//   };

//   /** add instantiations directly */
//   virtual int addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false ){
//     img.addInstantiations(baseMatch,qe,instLimit,addSplits);
//   };

// };

// class InstMatchGeneratorMonoEfficient: public InstMatchGeneratorMono{

//   CandidateGeneratorQueue d_eem;

//   InstMatchGeneratorMonoEfficient(TNode t, QuantifiersEngine* qe):
//     InstMatchGeneratorMono(t,qe) {
//     Assert(t[0].getKind()!=EQUAL || t[0].getKind()!=IFF);
//     //register the candidate generator to the efficient e-matching framework
//     Theory* th_uf = qe->getTheoryEngine()->getTheory( theory::THEORY_UF );
//     uf::InstantiatorTheoryUf* ith = (uf::InstantiatorTheoryUf*)th_uf->getInstantiator();
//     ith->registerCandidateGenerator( &d_eem, t[0] );

//   };

//   void resetInstantiationRound( QuantifiersEngine* qe ){
//     InstMatchGeneratorMono::resetInstantiationRound(qe);
//     d_eem.reset(Node::Null());
//   };

//   /** get the next match.  must call resetInstantiationRound
//       before this function. */
//   bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
//     Node t;
//     do{
//       //get the next candidate term t from efficient e-matching
//       t = d_eem.getNextCandidate();
//     }while( !t.isNull() && !getMatch( t, m, qe ) );
//     m.d_matched = t;
//     return !t.isNull();
//   };

//   /** add instantiations directly */
//   int addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit, bool addSplits ){
//     Assert(false);
//     return 0;
//   };

// };

// class InstMatchGeneratorMultiSimple: public IMGenerator
// {
// private:
//   /** children generators */
//   std::vector< InstMatchGenerator > d_children;
//   /** partial vector */
//   std::vector< InstMatch > d_partial;
//   /** constructors */
//   InstMatchGeneratorMultiSimple( std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption = 0 );
//   /** destructor */
//   ~InstMatchGenerator(){}
// public:
//   /** reset instantiation round (call this whenever equivalence classes have changed) */
//   void resetInstantiationRound( QuantifiersEngine* qe );
//   /** get the next match.  must call reset( eqc ) before this function. */
//   bool getNextMatch( InstMatch& m, QuantifiersEngine* qe );
//   /** return true if whatever Node is subsituted for the variables the
//       given Node can't match the pattern */
//   bool nonunifiable( TNode t, const std::vector<Node> & vars);
//   /** add instantiations */
//   int addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false );
// };


// class InstMatchGeneratorMultiEfficient{
// private:
//   /** children generators */
//   std::vector< InstMatchGenerator > d_children;
//   /** partial vector */
//   std::vector< InstMatch > d_partial;
//   /** Used by multi-pattern with efficient e-matching */
//   std::vector< InstMatchGenerator* > d_children_multi_efficient;
//   size_t d_children_multi_efficient_index;
// private:
//   /** get the next match.  must call d_cg->reset( ... ) before using. 
//       only valid for use where !d_match_pattern.isNull().
//   */
//   bool getNextMatch2( InstMatch& m, QuantifiersEngine* qe, bool saveMatched = false );
//   /** for arithmetic */
//   bool getMatchArithmetic( Node t, InstMatch& m, QuantifiersEngine* qe );
// public:
//   /** get the match against ground term or formula t.
//       d_match_mattern and t should have the same shape.
//       only valid for use where !d_match_pattern.isNull().
//   */
//   bool getMatch( Node t, InstMatch& m, QuantifiersEngine* qe );

//   /** constructors */
//   InstMatchGeneratorMultiSimple( std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption = 0 );
//   /** destructor */
//   ~InstMatchGenerator(){}
// public:
//   /** reset instantiation round (call this whenever equivalence classes have changed) */
//   void resetInstantiationRound( QuantifiersEngine* qe );
//   /** get the next match.  must call reset( eqc ) before this function. */
//   bool getNextMatch( InstMatch& m, QuantifiersEngine* qe );
//   /** return true if whatever Node is subsituted for the variables the
//       given Node can't match the pattern */
//   bool nonunifiable( TNode t, const std::vector<Node> & vars);
//   /** add instantiations */
//   int addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false );
// };


// /** smart multi-trigger implementation */
// class InstMatchGeneratorMulti : public IMGenerator
// {
// private:
//   /** indexed trie */
//   typedef std::pair< std::pair< int, int >, InstMatchTrie* > IndexedTrie;
//   /** collect instantiations */
//   void collectInstantiations( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas, InstMatchTrie* tr, 
//                               std::vector< IndexedTrie >& unique_var_tries,
//                               int trieIndex, int childIndex, int endChildIndex, bool modEq );
//   /** collect instantiations 2 */
//   void collectInstantiations2( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas,
//                                std::vector< IndexedTrie >& unique_var_tries,
//                                int uvtIndex, InstMatchTrie* tr = NULL, int trieIndex = 0 );
// private:
//   /** var contains (variable indicies) for each pattern node */
//   std::map< Node, std::vector< int > > d_var_contains;
//   /** variable indicies contained to pattern nodes */
//   std::map< int, std::vector< Node > > d_var_to_node;
//   /** quantifier to use */
//   Node d_f;
//   /** policy to use for matching */
//   int d_matchPolicy;
//   /** children generators */
//   std::vector< InstMatchGenerator* > d_children;
//   /** inst match tries for each child */
//   std::vector< InstMatchTrieOrdered > d_children_trie;
//   /** calculate matches */
//   void calculateMatches( QuantifiersEngine* qe );
// public:
//   /** constructors */
//   InstMatchGeneratorMulti( Node f, std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption = 0 );
//   /** destructor */
//   ~InstMatchGeneratorMulti(){}
//   /** reset instantiation round (call this whenever equivalence classes have changed) */
//   void resetInstantiationRound( QuantifiersEngine* qe );
//   /** reset, eqc is the equivalence class to search in (any if eqc=null) */
//   void reset( Node eqc, QuantifiersEngine* qe );
//   /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
//   bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) { return false; } 
//   /** return true if whatever Node is subsituted for the variables the
//       given Node can't match the pattern */
//   bool nonunifiable( TNode t, const std::vector<Node> & vars) { return true; }
//   /** add instantiations */
//   int addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false );
// };

class TermArgTrie;

// /** smart (single)-trigger implementation */
// class InstMatchGeneratorSimple : public IMGenerator
// {
// private:
//   /** quantifier for match term */
//   Node d_f;
//   /** match term */
//   Node d_match_pattern;
//   /** add instantiations */
//   void addInstantiations( InstMatch& m, QuantifiersEngine* qe, int& addedLemmas, 
//                           int argIndex, TermArgTrie* tat, int instLimit, bool addSplits );
// public:
//   /** constructors */
//   InstMatchGeneratorSimple( Node f, Node pat ) : d_f( f ), d_match_pattern( pat ){}
//   /** destructor */
//   ~InstMatchGeneratorSimple(){}
//   /** reset instantiation round (call this whenever equivalence classes have changed) */
//   void resetInstantiationRound( QuantifiersEngine* qe ) {}
//   /** reset, eqc is the equivalence class to search in (any if eqc=null) */
//   void reset( Node eqc, QuantifiersEngine* qe ) {}
//   /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
//   bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) { return false; } 
//   /** return true if whatever Node is subsituted for the variables the
//       given Node can't match the pattern */
//   bool nonunifiable( TNode t, const std::vector<Node> & vars) { return true; }
//   /** add instantiations */
//   int addInstantiations( InstMatch& baseMatch, QuantifiersEngine* qe, int instLimit = 0, bool addSplits = false );
// };

}/* CVC4::theory rrinst */

}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__RR_INST_MATCH_H */

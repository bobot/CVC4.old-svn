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

#ifndef __CVC4__THEORY_UF_INSTANTIATOR_H
#define __CVC4__THEORY_UF_INSTANTIATOR_H

#include "theory/quantifiers_engine.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdlist.h"
#include "context/cdlist_context_memory.h"

#include "util/stats.h"
#include "theory/uf/theory_uf.h"

namespace CVC4 {
namespace theory {
namespace uf {

class InstantiatorTheoryUf;

//instantiation strategies

class InstStrategyCheckCESolved : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** is solved? */
  std::map< Node, bool > d_solved;
  /** calc if f is solved */
  void calcSolved( Node f );
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e, int instLimit );
public:
  InstStrategyCheckCESolved( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyCheckCESolved(){}
  /** identify */
  std::string identify() const { return std::string("CheckCESolved"); }
};

class InstStrategyLitMatch : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** triggers for literal matching */
  std::map< Node, Trigger* > d_lit_match_triggers;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e, int instLimit );
public:
  InstStrategyLitMatch( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyLitMatch(){}
  /** identify */
  std::string identify() const { return std::string("LitMatch"); }
};

class InstStrategyUserPatterns : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** explicitly provided patterns */
  std::map< Node, std::vector< Trigger* > > d_user_gen;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e, int instLimit );
public:
  InstStrategyUserPatterns( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyUserPatterns(){}
public:
  /** add pattern */
  void addUserPattern( Node f, Node pat );
  /** get num patterns */
  int getNumUserGenerators( Node f ) { return (int)d_user_gen[f].size(); }
  /** get user pattern */
  Trigger* getUserGenerator( Node f, int i ) { return d_user_gen[f][ i ]; }
  /** identify */
  std::string identify() const { return std::string("UserPatterns"); }
};

class InstStrategyAutoGenTriggers : public InstStrategy{
private:
  /** collect all APPLY_UF pattern terms for f in n */
  static bool collectPatTerms2( Node f, Node n, std::map< Node, bool >& patMap, int tstrt );
public:
  //different strategies for choosing triggers
  enum {
    TS_MAX_TRIGGER = 0,
    TS_MIN_TRIGGER,
    TS_ALL,
  };
  static bool collectPatTerms( Node f, Node n, std::vector< Node >& patTerms, int tstrt, bool filterInst = false );
public:
  enum {
    RELEVANCE_NONE,
    RELEVANCE_DEFAULT,
  };
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** trigger generation strategy */
  int d_tr_strategy;
  /** relevance strategy */
  int d_rlv_strategy;
  /** triggers for each quantifier */
  std::map< Node, Trigger* > d_auto_gen_trigger;
private:
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e, int instLimit );
public:
  InstStrategyAutoGenTriggers( InstantiatorTheoryUf* th, QuantifiersEngine* ie, int tstrt, int rstrt ) : 
      InstStrategy( ie ), d_th( th ), d_tr_strategy( tstrt ), d_rlv_strategy( rstrt ){}
  ~InstStrategyAutoGenTriggers(){}
public:
  /** get auto-generated trigger */
  Trigger* getAutoGenTrigger( Node f );
  /** identify */
  std::string identify() const { return std::string("AutoGenTriggers"); }
};

class InstStrategyFreeVariable : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** guessed instantiations */
  std::map< Node, bool > d_guessed;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e, int instLimit );
public:
  InstStrategyFreeVariable( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyFreeVariable(){}
  /** identify */
  std::string identify() const { return std::string("FreeVariable"); }
};

//equivalence class info
class EqClassInfo
{
public:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
private:
  //a list of operators that occur as top symbols in that equivalence class
  //  Efficient E-Matching for SMT Solvers: "funs" 
  NodeList d_funs;
  //a list of operators f for which a term of the form f( ... t ... ) exists
  //  Efficient E-Matching for SMT Solvers: "pfuns" 
  NodeList d_pfuns;
  //a list of equivalence classes that are disequal
  BoolMap d_disequal;
public:
  EqClassInfo( context::Context* c );
  ~EqClassInfo(){}
  //set member
  void setMember( Node n );
  //has function, Efficient E-Matching for SMT Solvers: "funs" 
  bool hasFunction( Node op );
  //merge with another eq class info
  void merge( EqClassInfo* eci );
};

class UfTermDb : public TermDb
{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_ith;
public:
  UfTermDb( InstantiatorTheoryUf* ith ) : d_ith( ith ){}
  ~UfTermDb(){}
  /** parent structure: 
      n -> op -> index -> L
      map from node "n" to a list of nodes "L", where each node n' in L 
        has operator "op", and n'["index"] = n.
      for example, d_parents[n][f][1] = { f( t1, n ), f( t2, n ), ... }
  */
  std::map< Node, std::map< Node, std::map< int, std::vector< Node > > > > d_parents;
  /** register this term */
  void add( Node n, std::vector< Node >& added, bool withinQuant = false );
};

class InstantiatorTheoryUf : public Instantiator{
  friend class ::CVC4::theory::InstMatchGenerator;
  friend class UfTermDb;
protected:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
  typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeLists;
  /** term database */
  UfTermDb* d_db;
  /** map to representatives used */
  std::map< Node, Node > d_ground_reps;
protected:
  /** instantiation strategies */
  InstStrategyUserPatterns* d_isup;
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::QuantifiersEngine* ie, Theory* th);
  ~InstantiatorTheoryUf() {}
  /** assertNode method */
  void assertNode( Node assertion );
  /** Pre-register a term.  Done one time for a Node, ever. */
  void preRegisterTerm( Node t );
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryUf"); }
  /** debug print */
  void debugPrint( const char* c );
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
private:
  /** reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** calculate matches for quantifier f at effort */
  int process( Node f, Theory::Effort effort, int e, int instLimit );
public:
  /** get uf term database */
  UfTermDb* getTermDatabase() { return d_db; }
  /** statistics class */
  class Statistics {
  public:
    //IntStat d_instantiations;
    IntStat d_instantiations_ce_solved;
    IntStat d_instantiations_e_induced;
    IntStat d_instantiations_user_pattern;
    IntStat d_instantiations_guess;
    IntStat d_instantiations_auto_gen;
    IntStat d_instantiations_auto_gen_min;
    IntStat d_instantiations_auto_gen_relevant;
    IntStat d_splits;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
public:
  /** the base match */
  std::map< Node, InstMatch > d_baseMatch;
private:
  //for each equivalence class
  std::map< Node, EqClassInfo* > d_eqc_ops;
public:
  /** general queries about equality */
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  Node getInternalRepresentative( Node a );
  /** new node */
  void newEqClass( TNode n );
  /** merge */
  void merge( TNode a, TNode b );
  /** assert terms are disequal */
  void assertDisequal( TNode a, TNode b, TNode reason );
  /** get equivalence class info */
  EqClassInfo* getEquivalenceClassInfo( Node n );
private:
  class InvertedPathString{
  public:
    std::vector< std::pair< Node, int > > d_string;
  };
  class IpsCgVec {
  public:
    std::vector< std::pair< InvertedPathString, CandidateGenerator* > > d_vec;
  };
  std::map< Node, std::map< Node, IpsCgVec > > d_pp_pairs;
  std::map< Node, std::map< Node, IpsCgVec > > d_pc_pairs;
  std::map< Node, std::vector< CandidateGenerator* > > d_cand_gens;
  /** helper functions */
  void registerPatternElementPairs2( CandidateGenerator* cg, Node pat, InvertedPathString& ips, 
                                     std::map< Node, std::vector< std::pair< Node, InvertedPathString > > >& ips_map );
  void registerPatternElementPairs( CandidateGenerator* cg, Node pat );
public:
  /** Register candidate generator cg for pattern pat.  
      This request will ensure that calls will be made to cg->addCandidate( n ) for all
      ground terms n that are relevant for matching with pat.
  */
  void registerCandidateGenerator( CandidateGenerator* cg, Node pat );
};/* class InstantiatorTheoryUf */

/** equality query object using instantiator theory uf */
class EqualityQueryInstantiatorTheoryUf : public EqualityQuery
{
private:
  /** pointer to instantiator uf class */
  InstantiatorTheoryUf* d_ith;
public:
  EqualityQueryInstantiatorTheoryUf( InstantiatorTheoryUf* ith ) : d_ith( ith ){}
  ~EqualityQueryInstantiatorTheoryUf(){}
  /** general queries about equality */
  Node getRepresentative( Node a ) { return d_ith->getRepresentative( a ); }
  bool areEqual( Node a, Node b ) { return d_ith->areEqual( a, b ); }
  bool areDisequal( Node a, Node b ) { return d_ith->areDisequal( a, b ); }
  Node getInternalRepresentative( Node a ) { return d_ith->getInternalRepresentative( a ); }
}; /* EqualityQueryInstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

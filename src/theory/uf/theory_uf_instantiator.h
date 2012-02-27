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
public:
  InstStrategyCheckCESolved( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyCheckCESolved(){}
  void resetInstantiationRound();
  int process( Node f, int effort, int instLimit );
  /** identify */
  std::string identify() const { return std::string("CheckCESolved"); }
};

class InstStrategyLitMatch : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** triggers for literal matching */
  std::map< Node, Trigger* > d_lit_match_triggers;
public:
  InstStrategyLitMatch( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyLitMatch(){}
  void resetInstantiationRound();
  int process( Node f, int effort, int instLimit );
  /** identify */
  std::string identify() const { return std::string("LitMatch"); }
};

class InstStrategyUserPatterns : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** explicitly provided patterns */
  std::map< Node, std::vector< Trigger* > > d_user_gen;
public:
  InstStrategyUserPatterns( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyUserPatterns(){}
  void resetInstantiationRound();
  int process( Node f, int effort, int instLimit );
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
public:
  //different strategies for choosing triggers
  enum {
    MAX_TRIGGER = 0,
    MIN_TRIGGER,
  };
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** trigger generation strategy */
  int d_tr_strategy;
  /** current trigger */
  std::map< Node, Trigger* > d_auto_gen_trigger;
private:
  /** collect all top level APPLY_UF pattern terms for f in n */
  void collectPatTerms( Node f, Node n, std::vector< Node >& patTerms, int tstrt );
public:
  InstStrategyAutoGenTriggers( InstantiatorTheoryUf* th, QuantifiersEngine* ie, int tstrt ) : 
      InstStrategy( ie ), d_th( th ), d_tr_strategy( tstrt ){}
  ~InstStrategyAutoGenTriggers(){}
  void resetInstantiationRound();
  int process( Node f, int effort, int instLimit );
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
public:
  InstStrategyFreeVariable( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyFreeVariable(){}
  void resetInstantiationRound();
  int process( Node f, int effort, int instLimit );
  /** identify */
  std::string identify() const { return std::string("FreeVariable"); }
};

//equivalence class info
class EqClassInfo
{
public:
  typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
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

class UfTermDb
{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_ith;
public:
  UfTermDb( InstantiatorTheoryUf* ith ) : d_ith( ith ){}
  ~UfTermDb(){}
  /** map from APPLY_UF operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** last index considered */
  std::map< Node, int > d_op_index;
  /** parent */
  std::map< Node, std::map< Node, std::vector< Node > > > d_parents;
  /** register this term */
  void add( Node n );
  /** finish instantiation round */
  void finishInstantiationRound();
};

class InstantiatorTheoryUf : public Instantiator{
  friend class ::CVC4::theory::InstMatchGenerator;
protected:
  typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
  typedef context::CDMap<Node, NodeList*, NodeHashFunction> NodeLists;
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
  /** reset instantiation */
  void resetInstantiationRound();
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryUf"); }
  /** debug print */
  void debugPrint( const char* c );
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
private:
  /** calculate matches for quantifier f at effort */
  int process( Node f, int effort, int instLimit );
public:
  /** get uf term database */
  UfTermDb* getTermDatabase() { return d_db; }
  /** statistics class */
  class Statistics {
  public:
    IntStat d_instantiations;
    IntStat d_instantiations_ce_solved;
    IntStat d_instantiations_e_induced;
    IntStat d_instantiations_user_pattern;
    IntStat d_instantiations_guess;
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
};/* class InstantiatorTheoryUf */

/** equality query object using instantiator theory uf */
class EqualityQueryInstantiatorTheoryUf : public EqualityQuery
{
private:
  InstantiatorTheoryUf* d_ith;
public:
  EqualityQueryInstantiatorTheoryUf( InstantiatorTheoryUf* ith ) : d_ith( ith ){}
  ~EqualityQueryInstantiatorTheoryUf(){}
  /** general queries about equality */
  Node getRepresentative( Node a ) { return d_ith->getRepresentative( a ); }
  bool areEqual( Node a, Node b ) { return d_ith->areEqual( a, b ); }
  bool areDisequal( Node a, Node b ) { return d_ith->areDisequal( a, b ); }
  Node getInternalRepresentative( Node a ) { return d_ith->getInternalRepresentative( a ); }
};

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

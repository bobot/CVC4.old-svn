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

#include "theory/instantiation_engine.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdlist.h"
#include "context/cdlist_context_memory.h"

#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace uf {

class InstantiatorTheoryUf;

class InstStrategyCheckCESolved : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
public:
  InstStrategyCheckCESolved( InstantiatorTheoryUf* th, InstantiationEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyCheckCESolved(){}
  void resetInstantiationRound();
  int process( Node f, int effort );
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
  InstStrategyLitMatch( InstantiatorTheoryUf* th, InstantiationEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyLitMatch(){}
  void resetInstantiationRound();
  int process( Node f, int effort );
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
  InstStrategyUserPatterns( InstantiatorTheoryUf* th, InstantiationEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyUserPatterns(){}
  void resetInstantiationRound();
  int process( Node f, int effort );
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
  /** trigger generation strategy */
  int d_tr_strategy;
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** current trigger */
  std::map< Node, Trigger* > d_auto_gen_trigger;
private:
  /** collect all top level APPLY_UF pattern terms for f in n */
  void collectPatTerms( Node f, Node n, std::vector< Node >& patTerms, int tstrt );
public:
  InstStrategyAutoGenTriggers( InstantiatorTheoryUf* th, InstantiationEngine* ie, int tstrt ) : 
      InstStrategy( ie ), d_th( th ), d_tr_strategy( tstrt ){}
  ~InstStrategyAutoGenTriggers(){}
  void resetInstantiationRound();
  int process( Node f, int effort );
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
  InstStrategyFreeVariable( InstantiatorTheoryUf* th, InstantiationEngine* ie ) : 
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyFreeVariable(){}
  void resetInstantiationRound();
  int process( Node f, int effort );
  /** identify */
  std::string identify() const { return std::string("FreeVariable"); }
};

class UfTermDb
{
public:
  UfTermDb(){}
  ~UfTermDb(){}
  /** map from APPLY_UF operators to ground, pattern terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map[2];
  /** register this term */
  void registerTerm( Node n );
};

class InstantiatorTheoryUf : public Instantiator{
  friend class ::CVC4::theory::InstMatchGenerator;
protected:
  typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
  typedef context::CDMap<Node, NodeList*, NodeHashFunction> NodeLists;

  /** whether obligatiosn have changed for each quantifier */
  BoolMap d_ob_changed;
  /** list of currently asserted literals for each quantifier */
  NodeLists d_obligations;
  /** term database */
  UfTermDb d_db;
  /** all terms in the current context */
  //BoolMap d_terms_full;
  /** map from (representative) nodes to list of representative nodes they are disequal from */
  NodeList d_disequality;
  /** map to representatives used */
  std::map< Node, Node > d_reps;
  /** disequality list */
  std::map< Node, std::vector< Node > > d_dmap;
  /** has instantiation constant */
  void addObligationToList( Node ob, Node f );
  /** add obligations */
  void addObligations( Node n, Node ob );
protected:
  /** instantiation strategies */
  InstStrategyUserPatterns* d_isup;
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::InstantiationEngine* ie, Theory* th);
  ~InstantiatorTheoryUf() {}
  /** check method */
  void check( Node assertion );
  /** reset instantiation */
  void resetInstantiationRound();
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryUf"); }
  /** debug print */
  void debugPrint( const char* c );
  /** register terms */
  void registerTerm( Node n );
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
private:
  /** calculate matches for quantifier f at effort */
  int process( Node f, int effort );
  /** calculate sets possible matches to induce t ~ s */
  std::map< Node, std::map< Node, std::vector< Node > > > d_litMatchCandidates[2];
  void calculateEIndLitCandidates( Node t, Node s, Node f, bool isEq );
public:
  /** are obligations changed? */
  bool getObligationsChanged( Node f ) { return d_ob_changed[f]; }
  /** get obligations for quantifier f */
  void getObligations( Node f, std::vector< Node >& obs );
  /** general queries about equality */
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  Node getInternalRepresentative( Node a );
  /** get uf term database */
  UfTermDb* getTermDatabase() { return &d_db; }
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
  /** the base match */
  InstMatch d_baseMatch;
};/* class InstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

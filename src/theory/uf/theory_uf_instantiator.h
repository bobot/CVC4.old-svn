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
  InstStrategyCheckCESolved( InstantiatorTheoryUf* th, Node f, InstantiationEngine* ie ) : 
      InstStrategy( f, ie ), d_th( th ){}
  ~InstStrategyCheckCESolved(){}
  void resetInstantiationRound();
  bool process( int effort );
};

class InstStrategyLitMatch : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
public:
  InstStrategyLitMatch( InstantiatorTheoryUf* th, Node f, InstantiationEngine* ie ) : 
      InstStrategy( f, ie ), d_th( th ){}
  ~InstStrategyLitMatch(){}
  void resetInstantiationRound();
  bool process( int effort );
};

class InstStrategyUserPatterns : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
public:
  InstStrategyUserPatterns( InstantiatorTheoryUf* th, Node f, InstantiationEngine* ie ) : 
      InstStrategy( f, ie ), d_th( th ){}
  ~InstStrategyUserPatterns(){}
  void resetInstantiationRound();
  bool process( int effort );
};

class InstStrategyAutoGenTriggers : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
public:
  InstStrategyAutoGenTriggers( InstantiatorTheoryUf* th, Node f, InstantiationEngine* ie ) : 
      InstStrategy( f, ie ), d_th( th ){}
  ~InstStrategyAutoGenTriggers(){}
  void resetInstantiationRound();
  bool process( int effort );
};

class InstantiatorTheoryUf : public Instantiator{
  friend class ::CVC4::theory::InstMatchGenerator;
protected:
  typedef context::CDMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDList<Node, context::ContextMemoryAllocator<Node> > NodeList;
  typedef context::CDMap<Node, NodeList*, NodeHashFunction> NodeLists;
  //typedef context::CDMap<Node, SubTermNode*, NodeHashFunction > SubTermMap;

  /** list of currently asserted literals for each quantifier */
  NodeLists d_obligations;
  /** all terms in the current context */
  BoolMap d_terms_full;
  /** terms in the current context that have an equality or disequality with another term */
  BoolMap d_terms;
  /** map from (representative) nodes to list of representative nodes they are disequal from */
  NodeList d_disequality;
  /** disequality list */
  std::map< Node, std::vector< Node > > d_dmap;
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  /** has instantiation constant */
  void addObligationToList( Node ob, Node f );
  void addObligations( Node n, Node ob );
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
  void registerTerm( Node n, bool isTop = true );
private:
  /** assert terms are equal */
  void assertEqual( Node a, Node b );

  /** calculate matches for quantifier f at effort */
  void process( Node f, int effort );

  /** find best match to any term */
  std::map< Node, std::vector< Node > > d_matches;
  std::map< Node, std::vector< Node > > d_anyMatches;
  void calculateMatches( Node f, Node t );
  /** calculate sets possible matches to induce t ~ s */
  std::map< Node, std::map< Node, std::vector< Node > > > d_litMatchCandidates[2];
  void calculateEIndLitCandidates( Node t, Node s, Node f, bool isEq );
  /** calculate whether two terms are equality-dependent */
  std::map< Node, std::map< Node, bool > > d_eq_dep;
  void calculateEqDep( Node i, Node c, Node f );

  /** list of concrete representatives */
  std::map< Node, Node > d_concrete_reps;
public:
  /** get concrete term in eq class */
  Node getConcreteRep( Node n );
  /** get obligations for quantifier f */
  void getObligations( Node f, std::vector< Node >& obs );
  /** statistics class */
  class Statistics {
  public:
    IntStat d_instantiations;
    IntStat d_instantiations_ce_solved;
    IntStat d_instantiations_e_induced;
    IntStat d_instantiations_user_pattern;
    IntStat d_splits;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};/* class InstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */

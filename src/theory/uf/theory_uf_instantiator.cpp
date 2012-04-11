/*********************                                                        */
/*! \file theory_uf_instantiator.cpp
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
 ** \brief Implementation of theory uf instantiator class
 **/

#include "theory/uf/theory_uf_instantiator.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine_impl.h"
#include "theory/uf/inst_strategy_model_find.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

EqClassInfo::EqClassInfo( context::Context* c ) : d_funs( c ), d_pfuns( c ), d_disequal( c ){

}

//set member
void EqClassInfo::setMember( Node n, UfTermDb* db ){
  if( n.getKind()==APPLY_UF ){
    d_funs[n.getOperator()] = true;
  }
  //add parent functions
  for( std::map< Node, std::map< int, std::vector< Node > > >::iterator it = db->d_parents[n].begin();
    it != db->d_parents[n].end(); ++it ){
    d_pfuns[ it->first ] = true;
  }
}

//get has function 
bool EqClassInfo::hasFunction( Node op ){
  return d_funs.find( op )!=d_funs.end();
}

bool EqClassInfo::hasParent( Node op ){
  return d_pfuns.find( op )!=d_pfuns.end();
}

//merge with another eq class info
void EqClassInfo::merge( EqClassInfo* eci ){
  for( BoolMap::iterator it = eci->d_funs.begin(); it != eci->d_funs.end(); it++ ) {
    d_funs[ (*it).first ] = true;
  }
  for( BoolMap::iterator it = eci->d_pfuns.begin(); it != eci->d_pfuns.end(); it++ ) {
    d_pfuns[ (*it).first ] = true;
  }
}

void UfTermTrie::addTerm2( QuantifiersEngine* qe, Node n, int argIndex, bool modEq ){
  if( argIndex<(int)n.getNumChildren() ){
    d_data[ n[argIndex ] ].addTerm2( qe, n, argIndex+1, modEq );
  }
}

bool UfTermTrie::existsTerm( QuantifiersEngine* qe, Node n, int argIndex, bool modEq ){
  if( argIndex==(int)n.getNumChildren() ){
    return true;
  }else{
    std::map< Node, UfTermTrie >::iterator it = d_data.find( n[ argIndex ] );
    if( it!=d_data.end() ){
      if( it->second.existsTerm( qe, n, argIndex+1, modEq ) ){
        return true;
      }
    }
    if( modEq ){
      //check modulo equality if any other term exists
      if( ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine()->hasTerm( n[ argIndex ] ) ){
        uf::EqClassIterator eqc = uf::EqClassIterator( qe->getEqualityQuery()->getRepresentative( n[ argIndex ] ), 
                                ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en!=n ){
            std::map< Node, UfTermTrie >::iterator itc = d_data.find( en );
            if( itc!=d_data.end() ){
              if( itc->second.existsTerm( qe, n, argIndex+1, modEq ) ){
                return true;
              }
            }
          }
          ++eqc;
        }
      }
    }
    return false;
  }
}

bool UfTermTrie::addTerm( QuantifiersEngine* qe, Node n, bool modEq ){
  if( !existsTerm( qe, n, 0, modEq ) ){
    addTerm2( qe, n, 0, modEq );
    return true;
  }else{
    return false;
  }
}

void UfTermDb::add( Node n, std::vector< Node >& added, bool withinQuant ){
#if 1
  //don't add terms in quantifier bodies
  if( withinQuant ){
    return;
  }
#endif
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( !n.hasAttribute(InstConstantAttribute()) ){
      if( std::find( d_op_map[op].begin(), d_op_map[op].end(), n )==d_op_map[op].end() ){
        Debug("uf-term-db") << "register term " << n << std::endl;

        d_op_map[op].push_back( n );
        d_type_map[ n.getType() ].push_back( n );
        added.push_back( n );
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          add( n[i], added, withinQuant );
          if( Options::current()->efficientEMatching ){
            if( d_parents[n[i]][op].empty() ){
              //must add parent to equivalence class info
              Node nir = d_ith->getRepresentative( n[i] );
              EqClassInfo* eci_nir = d_ith->getEquivalenceClassInfo( nir );
              if( eci_nir ){
                eci_nir->d_pfuns[ op ] = true;
              }
            }
            //add to parent structure
            if( std::find( d_parents[n[i]][op][i].begin(), d_parents[n[i]][op][i].end(), n )==d_parents[n[i]][op][i].end() ){
              d_parents[n[i]][op][i].push_back( n );
            }
          }
        }
        if( Options::current()->efficientEMatching ){
          //check if congruent to preexisting node
          //for( int i=0; i<(int)d_op_map[op].size(); i++ ){
          //  Node np = d_op_map[op][i];
          //  bool ncong = false;
          //  for( int a=0; a<(int)np.getNumChildren(); a++ ){
          //    if( !d_ith->areEqual( n[a], np[a] ) ){
          //      ncong = true;
          //      break;
          //    }
          //  }
          //  if( !ncong ){
          //    congruent = true;
          //    break;
          //  }
          //}
          //std::cout << "Add candidate (NEW) " << n << std::endl;
          //new term, add n to candidate generators
          for( int i=0; i<(int)d_ith->d_cand_gens[op].size(); i++ ){
            d_ith->d_cand_gens[op][i]->addCandidate( n );
          }
        }
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        add( n[i], added, withinQuant );
      }
    }
  }
}

void UfTermDb::resetInstantiationRound( Theory::Effort effort ){
  d_calcedNoMatchTerms = false;
}

void UfTermDb::resetMatching(){
  if( !d_calcedNoMatchTerms ){
    int nonCongruentCount = 0;
    int congruentCount = 0;
    int alreadyCongruentCount = 0;
    //calculate all congruent terms
    for( std::map< Node, std::vector< Node > >::iterator it = d_op_map.begin(); it != d_op_map.end(); ++it ){
      UfTermTrie uftt;
      for( int i=0; i<(int)it->second.size(); i++ ){
        Node n = it->second[i];
        if( !n.getAttribute(NoMatchAttribute()) ){
          if( !uftt.addTerm( d_ith->getQuantifiersEngine(), n, true ) ){
            NoMatchAttribute nma;
            n.setAttribute(nma,true);
            congruentCount++;
          }else{
            nonCongruentCount++;
          }
        }else{
          congruentCount++;
          alreadyCongruentCount++;
        }
      }
    }
    //std::cout << "Congruent/Non-Congruent = ";
    //std::cout << congruentCount << "(" << alreadyCongruentCount << ") / " << nonCongruentCount << std::endl;
    d_calcedNoMatchTerms = true;
  }
}

InstantiatorTheoryUf::InstantiatorTheoryUf(context::Context* c, CVC4::theory::QuantifiersEngine* ie, Theory* th) :
Instantiator( c, ie, th )
//d_ob_changed( c ),
//d_obligations( c ),
//d_disequality( c )
{
  d_db = new UfTermDb( this );
  ie->setTermDatabase( d_db );

  if(Options::current()->finiteModelFind ){
    if( Options::current()->cbqi ){
      addInstStrategy( new InstStrategyCheckCESolved( this, ie ) );
    }
    addInstStrategy( new InstStrategyFinteModelFind( c, this, ((TheoryUF*)th)->getStrongSolver(), ie ) );
  }else{
    if( Options::current()->cbqi ){
      addInstStrategy( new InstStrategyCheckCESolved( this, ie ) );
    }
    d_isup = new InstStrategyUserPatterns( this, ie );
    addInstStrategy( d_isup );
    InstStrategyAutoGenTriggers* i_ag = new InstStrategyAutoGenTriggers( this, ie, Trigger::TS_ALL, 
                                                                         InstStrategyAutoGenTriggers::RELEVANCE_DEFAULT, 3 );
    i_ag->setGenerateAdditional( true );
    addInstStrategy( i_ag );
    //addInstStrategy( new InstStrategyAddFailSplits( this, ie ) );
    addInstStrategy( new InstStrategyFreeVariable( this, ie ) );
    //d_isup->setPriorityOver( i_ag );
    //d_isup->setPriorityOver( i_agm );
    //i_ag->setPriorityOver( i_agm );
  }
}

//void InstantiatorTheoryUf::addObligationToList( Node o, Node f ){
//  NodeList* ob;
//  NodeLists::iterator ob_i = d_obligations.find( f );
//  if( ob_i==d_obligations.end() ){
//    ob = new(d_th->getContext()->getCMM()) NodeList(true, d_th->getContext(), false,
//                                                    ContextMemoryAllocator<Node>(d_th->getContext()->getCMM()));
//    d_obligations.insertDataFromContextMemory( f, ob );
//  }else{
//    ob = (*ob_i).second;
//  }
//  for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
//    if( *it==o ){
//      return;
//    }
//  }
//  d_ob_changed[f] = true;
//  ob->push_back( o );
//}
//
//void InstantiatorTheoryUf::addObligations( Node n, Node ob ){
//  if( n.hasAttribute(InstConstantAttribute()) ){
//    addObligationToList( ob, n.getAttribute(InstConstantAttribute()) );
//  }else{
//    for( int i=0; i<(int)n.getNumChildren(); i++ ){
//      addObligations( n[i], ob );
//    }
//  }
//}

void InstantiatorTheoryUf::preRegisterTerm( Node t ){
  switch(t.getKind()) {
  case kind::EQUAL:
    d_quantEngine->addTermToDatabase( t[0] );
    d_quantEngine->addTermToDatabase( t[1] );
    break;
  case kind::NOT:
    if( t[0].getKind()==EQUAL || t[0].getKind()==IFF ){
      d_quantEngine->addTermToDatabase( t[0][0] );
      d_quantEngine->addTermToDatabase( t[0][1] );
    }else if( t[0].getKind()==APPLY_UF ){
      d_quantEngine->addTermToDatabase( t[0] );
    }
    break;
  case kind::CARDINALITY_CONSTRAINT:
    break;
  default:
    d_quantEngine->addTermToDatabase( t );
    break;
  }
  if( t.hasAttribute(InstConstantAttribute()) ){
    setHasConstraintsFrom( t.getAttribute(InstConstantAttribute()) );
  }else if( t.getKind()==NOT && t[0].hasAttribute(InstConstantAttribute()) ){
    setHasConstraintsFrom( t[0].getAttribute(InstConstantAttribute()) );
  }
}

void InstantiatorTheoryUf::assertNode( Node assertion )
{
  Debug("quant-uf-assert") << "InstantiatorTheoryUf::check: " << assertion << std::endl;
  preRegisterTerm( assertion );
  ////addObligations( assertion, assertion );
}

void InstantiatorTheoryUf::addUserPattern( Node f, Node pat ){
  if( d_isup ){
    d_isup->addUserPattern( f, pat );
  }
  setHasConstraintsFrom( f );
}


void InstantiatorTheoryUf::processResetInstantiationRound( Theory::Effort effort ){
  d_ground_reps.clear();
}

int InstantiatorTheoryUf::process( Node f, Theory::Effort effort, int e, int instLimit ){
  Debug("quant-uf") << "UF: Try to solve (" << e << ") for " << f << "... " << std::endl;
  return InstStrategy::STATUS_SAT;
}

void InstantiatorTheoryUf::debugPrint( const char* c )
{

}

bool InstantiatorTheoryUf::areEqual( Node a, Node b ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) &&
      ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( b ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.areEqual( a, b );
  }else{
    return a==b;
  }
}

bool InstantiatorTheoryUf::areDisequal( Node a, Node b ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) &&
      ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( b ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.areDisequal( a, b );
  }else{
    return false;
  }
}

Node InstantiatorTheoryUf::getRepresentative( Node a ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) ){
    return ((TheoryUF*)d_th)->d_equalityEngine.getRepresentative( a );
  }else{
    return a;
  }
}

Node InstantiatorTheoryUf::getInternalRepresentative( Node a ){
  if( d_ground_reps.find( a )==d_ground_reps.end() ){
    if( !((TheoryUF*)d_th)->d_equalityEngine.hasTerm( a ) ){
      return a;
    }else{
      Node rep = getRepresentative( a );
      if( !rep.hasAttribute(InstConstantAttribute()) ){
        //return the representative of a
        d_ground_reps[a] = rep;
        return rep;
      }else{
        //otherwise, must search eq class
        EqClassIterator eqc_iter( rep, &((TheoryUF*)d_th)->d_equalityEngine );
        rep = Node::null();
        while( !eqc_iter.isFinished() ){
          if( !(*eqc_iter).hasAttribute(InstConstantAttribute()) ){
            d_ground_reps[ a ] = *eqc_iter;
            return *eqc_iter;
          }
          eqc_iter++;
        }
        d_ground_reps[ a ] = a;
      }
    }
  }
  return d_ground_reps[a];
}

//void InstantiatorTheoryUf::getObligations( Node f, std::vector< Node >& obs ){
//  NodeLists::iterator ob_i = d_obligations.find( f );
//  if( ob_i!=d_obligations.end() ){
//    NodeList* ob = (*ob_i).second;
//    //std::cout  << "Generate trigger for literal matching..." << std::endl;
//    //this is matching at the literal level : use obligations of f as pattern terms
//    for( NodeList::const_iterator it = ob->begin(); it != ob->end(); ++it ){
//      obs.push_back( *it );
//    }
//    d_ob_changed[f] = false;
//  }
//}

InstantiatorTheoryUf::Statistics::Statistics():
  //d_instantiations("InstantiatorTheoryUf::Total_Instantiations", 0),
  d_instantiations_ce_solved("InstantiatorTheoryUf::Instantiations_CE-Solved", 0),
  d_instantiations_e_induced("InstantiatorTheoryUf::Instantiations_E-Induced", 0),
  d_instantiations_user_pattern("InstantiatorTheoryUf::Instantiations_User_Pattern", 0),
  d_instantiations_guess("InstantiatorTheoryUf::Instantiations_Free_Var", 0),
  d_instantiations_auto_gen("InstantiatorTheoryUf::Instantiations_Auto_Gen", 0),
  d_instantiations_auto_gen_min("InstantiatorTheoryUf::Instantiations_Auto_Gen_Min", 0),
  d_splits("InstantiatorTheoryUf::Total_Splits", 0)
{
  //StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_instantiations_ce_solved);
  StatisticsRegistry::registerStat(&d_instantiations_e_induced);
  StatisticsRegistry::registerStat(&d_instantiations_user_pattern );
  StatisticsRegistry::registerStat(&d_instantiations_guess );
  StatisticsRegistry::registerStat(&d_instantiations_auto_gen );
  StatisticsRegistry::registerStat(&d_instantiations_auto_gen_min );
  StatisticsRegistry::registerStat(&d_splits);
}

InstantiatorTheoryUf::Statistics::~Statistics(){
  //StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_instantiations_ce_solved);
  StatisticsRegistry::unregisterStat(&d_instantiations_e_induced);
  StatisticsRegistry::unregisterStat(&d_instantiations_user_pattern );
  StatisticsRegistry::unregisterStat(&d_instantiations_guess );
  StatisticsRegistry::unregisterStat(&d_instantiations_auto_gen );
  StatisticsRegistry::unregisterStat(&d_instantiations_auto_gen_min );
  StatisticsRegistry::unregisterStat(&d_splits);
}

/** new node */
void InstantiatorTheoryUf::newEqClass( TNode n ){

}

/** merge */
void InstantiatorTheoryUf::merge( TNode a, TNode b ){
  if( Options::current()->efficientEMatching ){
    if( a.getKind()!=IFF && a.getKind()!=EQUAL && b.getKind()!=IFF && b.getKind()!=EQUAL ){
      Debug("efficient-e-match") << "Merging " << a << " with " << b << std::endl;

      //determine new candidates for instantiation
      computeCandidatesPcPairs( a, b );
      computeCandidatesPcPairs( b, a );
      computeCandidatesPpPairs( a, b );
      computeCandidatesPpPairs( b, a );
    }
    //merge eqc_ops of b into a
    EqClassInfo* eci_a = getOrCreateEquivalenceClassInfo( a );
    EqClassInfo* eci_b = getOrCreateEquivalenceClassInfo( b );
    eci_a->merge( eci_b );
  }
}

/** assert terms are disequal */
void InstantiatorTheoryUf::assertDisequal( TNode a, TNode b, TNode reason ){
  
}

EqClassInfo* InstantiatorTheoryUf::getEquivalenceClassInfo( Node n ) { 
  return d_eqc_ops.find( n )==d_eqc_ops.end() ? NULL : d_eqc_ops[n]; 
}
EqClassInfo* InstantiatorTheoryUf::getOrCreateEquivalenceClassInfo( Node n ){
  Assert( n==getRepresentative( n ) );
  if( d_eqc_ops.find( n )==d_eqc_ops.end() ){
    EqClassInfo* eci = new EqClassInfo( d_th->getContext() );
    eci->setMember( n, d_db );
    d_eqc_ops[n] = eci;
  }
  return d_eqc_ops[n]; 
}

void InstantiatorTheoryUf::computeCandidatesPcPairs( Node a, Node b ){
  Debug("efficient-e-match") << "Compute candidates for pc pairs..." << std::endl;
  Debug("efficient-e-match") << "  Eq class = [";
  outputEqClass( "efficient-e-match", a);
  Debug("efficient-e-match") << "]" << std::endl;
  EqClassInfo* eci_a = getOrCreateEquivalenceClassInfo( a );
  EqClassInfo* eci_b = getOrCreateEquivalenceClassInfo( a );
  for( BoolMap::iterator it = eci_a->d_funs.begin(); it != eci_a->d_funs.end(); it++ ) {
    //the child function:  a member of eq_class( a ) has top symbol g, in other words g is in funs( a )
    Node g = (*it).first;
    Debug("efficient-e-match") << "  Checking application " << g << std::endl;
    //look at all parent/child pairs
    for( std::map< Node, std::map< Node, std::vector< InvertedPathString > > >::iterator itf = d_pc_pairs[g].begin(); 
         itf != d_pc_pairs[g].end(); ++itf ){
      //f/g is a parent/child pair
      Node f = itf->first;
      if( eci_b->hasParent( f ) || true ){
        //DO_THIS: determine if f in pfuns( b ), only do the follow if so
        Debug("efficient-e-match") << "    Checking parent application " << f << std::endl;
        //scan through the list of inverted path strings/candidate generators
        for( std::map< Node, std::vector< InvertedPathString > >::iterator cit = itf->second.begin(); 
            cit != itf->second.end(); ++cit ){
          Node pat = cit->first;
          Debug("efficient-e-match") << "      Checking pattern " << pat << std::endl;
          for( int c=0; c<(int)cit->second.size(); c++ ){
            Debug("efficient-e-match") << "        Check inverted path string for pattern ";
            outputInvertedPathString( "efficient-e-match", cit->second[c] );
            Debug("efficient-e-match") << std::endl;

            //collect all new relevant terms
            std::vector< Node > terms;
            terms.push_back( b );
            collectTermsIps( cit->second[c], terms );
            if( !terms.empty() ){
              Debug("efficient-e-match") << "        -> Added terms (" << (int)terms.size() << "): ";
              //add them as candidates to the candidate generator
              for( int t=0; t<(int)terms.size(); t++ ){
                Debug("efficient-e-match") << terms[t] << " ";
                //std::cout << "Add candidate (PC) " << terms[t] << std::endl;
                for( int cg=0; cg<(int)d_pat_cand_gens[pat].size(); cg++ ){
                  d_pat_cand_gens[pat][cg]->addCandidate( terms[t] );
                }
              }
              Debug("efficient-e-match") << std::endl;
            }
          }
        }
      }
    }
  }
}

void InstantiatorTheoryUf::computeCandidatesPpPairs( Node a, Node b ){
  Debug("efficient-e-match") << "Compute candidates for pp pairs..." << std::endl;
  EqClassInfo* eci_a = getOrCreateEquivalenceClassInfo( a );
  EqClassInfo* eci_b = getOrCreateEquivalenceClassInfo( a );
  for( std::map< Node, std::map< Node, std::map< Node, std::vector< IpsPair > > > >::iterator it = d_pp_pairs.begin();
       it != d_pp_pairs.end(); ++it ){
    Node f = it->first;
    if( eci_a->hasParent( f ) ){
      Debug("efficient-e-match") << "  Checking parent application " << f << std::endl;
      for( std::map< Node, std::map< Node, std::vector< IpsPair > > >::iterator it2 = it->second.begin();
           it2 != it->second.end(); ++it2 ){
        Node g = it2->first;
        if( eci_b->hasParent( g ) ){
          Debug("efficient-e-match") << "    Checking parent application " << g << std::endl;
          //if f in pfuns( a ) and g is in pfuns( b ), only do the follow if so
          for( std::map< Node, std::vector< IpsPair > >::iterator cit = it2->second.begin(); 
               cit != it2->second.end(); ++cit ){
            Node pat = cit->first;
            for( int c=0; c<(int)cit->second.size(); c++ ){
              std::vector< Node > a_terms;
              a_terms.push_back( a );
              if( !a_terms.empty() ){
                collectTermsIps( cit->second[c].first, a_terms );
                std::vector< Node > b_terms;
                b_terms.push_back( b );
                collectTermsIps( cit->second[c].first, b_terms );
                //take intersection
                for( int t=0; t<(int)a_terms.size(); t++ ){
                  if( std::find( b_terms.begin(), b_terms.end(), a_terms[t] )!=b_terms.end() ){
                                //std::cout << "Add candidate (PP) " << a_terms[t] << std::endl;
                    Debug("efficient-e-match") << "      -> Add term " << a_terms[t] << std::endl;
                    //add to all candidate generators having this term
                    for( int cg=0; cg<(int)d_pat_cand_gens[pat].size(); cg++ ){
                      d_pat_cand_gens[pat][cg]->addCandidate( a_terms[t] );
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  } 
}

void InstantiatorTheoryUf::collectTermsIps( InvertedPathString& ips, std::vector< Node >& terms, int index ){
  if( index<(int)ips.size() && !terms.empty() ){
    Debug("efficient-e-match-debug") << "> Process " << index << std::endl;
    Node f = ips[index].first;
    int arg = ips[index].second;

    //for each term in terms, determine if any term (modulo equality) has parent "f" from position "arg"
    bool addRep = ( index!=(int)ips.size()-1 );
    std::vector< Node > newTerms;
    for( int t=0; t<(int)terms.size(); t++ ){
      collectParentsTermsIps( terms[t], f, arg, newTerms, addRep );
    }
    terms.clear();
    terms.insert( terms.begin(), newTerms.begin(), newTerms.end() );

    Debug("efficient-e-match-debug") << "> Terms are now: ";
    for( int t=0; t<(int)terms.size(); t++ ){
      Debug("efficient-e-match-debug") << terms[t] << " ";
    }
    Debug("efficient-e-match-debug") << std::endl;

    collectTermsIps( ips, terms, index+1 );
  }
}

bool InstantiatorTheoryUf::collectParentsTermsIps( Node n, Node f, int arg, std::vector< Node >& terms, bool addRep, bool modEq ){
  bool addedTerm = false;
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) && modEq ){
    Assert( getRepresentative( n )==n );
    //collect modulo equality
    //DO_THIS: this should (if necessary) compute a current set of (f, arg) parents for n and cache it
    EqClassIterator eqc_iter( getRepresentative( n ), &((TheoryUF*)d_th)->d_equalityEngine );
    while( !eqc_iter.isFinished() ){
      if( collectParentsTermsIps( (*eqc_iter), f, arg, terms, addRep, false ) ){
        //if only one argument, we know we can stop (since all others added will be congruent)
        if( f.getType().getNumChildren()==2 ){
          return true;
        }
        addedTerm = true;
      }
      eqc_iter++;
    }
  }else{
    //see if parent f exists from argument arg
    if( d_db->d_parents.find( n )!=d_db->d_parents.end() ){
      if( d_db->d_parents[n].find( f )!=d_db->d_parents[n].end() ){
        if( d_db->d_parents[n][f].find( arg )!=d_db->d_parents[n][f].end() ){
          for( int i=0; i<(int)d_db->d_parents[n][f][arg].size(); i++ ){
            Node t = d_db->d_parents[n][f][arg][i];
            if( addRep ){
              t = getRepresentative( t );
            }
            if( std::find( terms.begin(), terms.end(), t )==terms.end() ){
              terms.push_back( t );
            }
            addedTerm = true;
          }
        }
      }
    }
  }
  return addedTerm;
}

void InstantiatorTheoryUf::registerPatternElementPairs2( Node opat, Node pat, InvertedPathString& ips, 
                                                       std::map< Node, std::vector< std::pair< Node, InvertedPathString > > >& ips_map  ){
  Assert( pat.getKind()==APPLY_UF );
  //add information for possible pp-pair
  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    if( pat[i].getKind()==INST_CONSTANT ){
      ips_map[ pat[i] ].push_back( std::pair< Node, InvertedPathString >( pat.getOperator(), InvertedPathString( ips ) ) );
    }
  }
  ips.push_back( std::pair< Node, int >( pat.getOperator(), 0 ) );
  for( int i=0; i<(int)pat.getNumChildren(); i++ ){
    if( pat[i].getKind()==APPLY_UF ){
      ips.back().second = i;
      registerPatternElementPairs2( opat, pat[i], ips, ips_map );
      Debug("pattern-element-opt") << "Found pc-pair ( " << pat.getOperator() << ", " << pat[i].getOperator() << " )" << std::endl;
      Debug("pattern-element-opt") << "   Path = ";
      outputInvertedPathString( "pattern-element-opt", ips );
      Debug("pattern-element-opt") << std::endl;
      //pat.getOperator() and pat[i].getOperator() are a pc-pair
      d_pc_pairs[ pat[i].getOperator() ][ pat.getOperator() ][opat].push_back( InvertedPathString( ips ) );
    }
  }
  ips.pop_back();
}

void InstantiatorTheoryUf::registerPatternElementPairs( Node pat ){
  InvertedPathString ips;
  std::map< Node, std::vector< std::pair< Node, InvertedPathString > > > ips_map;
  registerPatternElementPairs2( pat, pat, ips, ips_map );
  for( std::map< Node, std::vector< std::pair< Node, InvertedPathString > > >::iterator it = ips_map.begin(); it != ips_map.end(); ++it ){
    for( int j=0; j<(int)it->second.size(); j++ ){
      for( int k=j+1; k<(int)it->second.size(); k++ ){
        //found a pp-pair
        Debug("pattern-element-opt") << "Found pp-pair ( " << it->second[j].first << ", " << it->second[k].first << " )" << std::endl;
        Debug("pattern-element-opt") << "   Paths = ";
        outputInvertedPathString( "pattern-element-opt", it->second[j].second );
        Debug("pattern-element-opt") << " and ";
        outputInvertedPathString( "pattern-element-opt", it->second[k].second );
        Debug("pattern-element-opt") << std::endl;
        d_pp_pairs[ it->second[j].first ][ it->second[k].first ][pat].push_back( IpsPair( it->second[j].second, it->second[k].second ) );
      }
    }
  }
}

void InstantiatorTheoryUf::registerCandidateGenerator( CandidateGenerator* cg, Node pat ){
  Debug("efficient-e-match") << "Register candidate generator..." << pat << std::endl;
  if( d_pat_cand_gens.find( pat )==d_pat_cand_gens.end() ){
    registerPatternElementPairs( pat );
  }
  d_pat_cand_gens[pat].push_back( cg );
  
  //take all terms from the uf term db and add to candidate generator
  Node op = pat.getOperator();
  for( int i=0; i<(int)d_db->d_op_map[op].size(); i++ ){
    cg->addCandidate( d_db->d_op_map[op][i] );
  }
  d_cand_gens[op].push_back( cg );

  Debug("efficient-e-match") << "Done." << std::endl;
}

void InstantiatorTheoryUf::outputEqClass( const char* c, Node n ){
  if( ((TheoryUF*)d_th)->d_equalityEngine.hasTerm( n ) ){
    EqClassIterator eqc_iter( getRepresentative( n ), 
                              &((TheoryUF*)d_th)->d_equalityEngine );
    bool firstTime = true;
    while( !eqc_iter.isFinished() ){
      if( !firstTime ){ Debug(c) << ", "; }
      Debug(c) << (*eqc_iter);
      firstTime = false;
      eqc_iter++;
    }
  }else{
    Debug(c) << n;
  }
}

void InstantiatorTheoryUf::outputInvertedPathString( const char* c, InvertedPathString& ips ){
  for( int i=0; i<(int)ips.size(); i++ ){
    if( i>0 ){ Debug( c ) << "."; }
    Debug( c ) << ips[i].first << "." << ips[i].second;
  }
}

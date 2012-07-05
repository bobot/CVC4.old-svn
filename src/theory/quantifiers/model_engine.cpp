/*********************                                                        */
/*! \file model_engine.cpp
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
 ** \brief Implementation of model engine class
 **/

#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/rep_set_iterator.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf_instantiator.h"

//#define ME_PRINT_WARNINGS

//#define DISABLE_EVAL_SKIP_MULTIPLE

#define EVAL_FAIL_SKIP_MULTIPLE
//#define ONE_QUANT_PER_ROUND_INST_GEN
//#define ONE_QUANT_PER_ROUND
//#define USE_RELEVANT_DOMAIN
//#define USE_EXTENDED_MODEL

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

//Model Engine constructor
ModelEngine::ModelEngine( QuantifiersEngine* qe ) :
QuantifiersModule( qe ),
d_builder(*this),
d_model( qe, qe->getSatContext() ),
d_rel_domain( qe, &d_model ){

}

void ModelEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_LAST_CALL && !d_quantEngine->hasAddedLemma() ){
    //first, check if we can minimize the model further
    if( !((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->getTheory( THEORY_UF ))->getStrongSolver()->minimize() ){
      return;
    }
    //the following will attempt to build a model and test that it satisfies all asserted universal quantifiers
    int addedLemmas = 0;
    if( optUseModel() ){
      //check if any quantifiers are un-initialized
      for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
        Node f = d_quantEngine->getAssertedQuantifier( i );
        addedLemmas += initializeQuantifier( f );
      }
    }
    if( addedLemmas==0 ){
      //quantifiers are initialized, we begin an instantiation round
      double clSet = 0;
      if( Options::current()->printModelEngine ){
        clSet = double(clock())/double(CLOCKS_PER_SEC);
        Message() << "---Model Engine Round---" << std::endl;
      }
      Debug("fmf-model-debug") << "---Begin Instantiation Round---" << std::endl;
      ++(d_statistics.d_inst_rounds);
      //reset the quantifiers engine
      d_quantEngine->resetInstantiationRound( e );
      //build the representatives
      Debug("fmf-model-debug") << "Building representatives..." << std::endl;
      buildRepresentatives();
      //construct model if optUseModel() is true
      if( optUseModel() ){
        //initialize the model
        Debug("fmf-model-debug") << "Initializing model..." << std::endl;
        initializeModel();
        //analyze the quantifiers
        Debug("fmf-model-debug") << "Analyzing quantifiers..." << std::endl;
        analyzeQuantifiers();
        //if applicable, find exceptions
        if( optInstGen() ){
          //now, see if we know that any exceptions via InstGen exist
          Debug("fmf-model-debug") << "Perform InstGen techniques for quantifiers..." << std::endl;
          for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
            Node f = d_quantEngine->getAssertedQuantifier( i );
            if( d_quant_sat.find( f )==d_quant_sat.end() ){
              addedLemmas += doInstGen( f );
              if( optOneQuantPerRoundInstGen() && addedLemmas>0 ){
                break;
              }
            }
          }
          if( Options::current()->printModelEngine ){
            if( addedLemmas>0 ){
              Message() << "InstGen, added lemmas = " << addedLemmas << std::endl;
            }else{
              Message() << "No InstGen lemmas..." << std::endl;
            }
          }
          Debug("fmf-model-debug") << "---> Added lemmas = " << addedLemmas << std::endl;
        }
        if( addedLemmas==0 ){
          //if no immediate exceptions, build the model
          //  this model will be an approximation that will need to be tested via exhaustive instantiation
          Debug("fmf-model-debug") << "Building model..." << std::endl;
          d_model.buildModel();
        }
      }
      if( addedLemmas==0 ){
        //verify we are SAT by trying exhaustive instantiation
        d_triedLemmas = 0;
        d_testLemmas = 0;
        d_totalLemmas = 0;
        Debug("fmf-model-debug") << "Do exhaustive instantiation..." << std::endl;
        for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
          Node f = d_quantEngine->getAssertedQuantifier( i );
          if( d_quant_sat.find( f )==d_quant_sat.end() ){
            addedLemmas += exhaustiveInstantiate( f );
            if( optOneQuantPerRound() && addedLemmas>0 ){
              break;
            }
          }
#ifdef ME_PRINT_WARNINGS
          if( addedLemmas>10000 ){
            break;
          }
#endif
        }
        Debug("fmf-model-debug") << "---> Added lemmas = " << addedLemmas << " / " << d_triedLemmas << " / ";
        Debug("fmf-model-debug") << d_testLemmas << " / " << d_totalLemmas << std::endl;
        if( Options::current()->printModelEngine ){
          Message() << "Added Lemmas = " << addedLemmas << " / " << d_triedLemmas << " / ";
          Message() << d_testLemmas << " / " << d_totalLemmas << std::endl;
          double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
          Message() << "Finished model engine, time = " << (clSet2-clSet) << std::endl;
        }
#ifdef ME_PRINT_WARNINGS
        if( addedLemmas>10000 ){
          Debug("fmf-exit") << std::endl;
          debugPrint("fmf-exit");
          exit( 0 );
        }
#endif
      }
    }
    if( addedLemmas==0 ){
      //CVC4 will answer SAT
      Debug("fmf-consistent") << std::endl;
      debugPrint("fmf-consistent");
    }else{
      //otherwise, the search will continue
      d_quantEngine->flushLemmas( &d_quantEngine->getOutputChannel() );
    }
  }
}

void ModelEngine::registerQuantifier( Node f ){

}

void ModelEngine::assertNode( Node f ){

}

bool ModelEngine::optUseModel() {
  return Options::current()->fmfModelBasedInst;
}

bool ModelEngine::optOneInstPerQuantRound(){
  return Options::current()->fmfOneInstPerRound;
}

bool ModelEngine::optInstGen(){
  return Options::current()->fmfInstGen;
}

bool ModelEngine::optUseRelevantDomain(){
#ifdef USE_RELEVANT_DOMAIN
  return true;
#else
  return false;
#endif
}

bool ModelEngine::optOneQuantPerRoundInstGen(){
#ifdef ONE_QUANT_PER_ROUND_INST_GEN
  return true;
#else
  return false;
#endif
}

bool ModelEngine::optOneQuantPerRound(){
#ifdef ONE_QUANT_PER_ROUND
  return true;
#else
  return false;
#endif
}

Model* ModelEngine::getModel(){
  return NULL;
}

int ModelEngine::initializeQuantifier( Node f ){
  if( d_quant_init.find( f )==d_quant_init.end() ){
    d_quant_init[f] = true;
    Debug("inst-fmf-init") << "Initialize " << f << std::endl;
    //add the model basis instantiation
    // This will help produce the necessary information for model completion.
    // We do this by extending distinguish ground assertions (those
    //   containing terms with "model basis" attribute) to hold for all cases.

    ////first, check if any variables are required to be equal
    //for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
    //    it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
    //  Node n = it->first;
    //  if( n.getKind()==EQUAL && n[0].getKind()==INST_CONSTANT && n[1].getKind()==INST_CONSTANT ){
    //    Notice() << "Unhandled phase req: " << n << std::endl;
    //  }
    //}
    std::vector< Node > ics;
    std::vector< Node > terms;
    for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
      Node ic = d_quantEngine->getInstantiationConstant( f, j );
      Node t = getModelBasisTerm( ic.getType() );
      ics.push_back( ic );
      terms.push_back( t );
      //calculate the basis match for f
      d_quant_basis_match[f].d_map[ ic ] = t;
    }
    ++(d_statistics.d_num_quants_init);
    //register model basis body
    Node n = d_quantEngine->getCounterexampleBody( f );
    Node gn = n.substitute( ics.begin(), ics.end(), terms.begin(), terms.end() );
    registerModelBasis( n, gn );
    //add model basis instantiation
    if( d_quantEngine->addInstantiation( f, terms ) ){
      return 1;
    }else{
      //shouldn't happen usually, but will occur if x != y is a required literal for f.
      //Notice() << "No model basis for " << f << std::endl;
      ++(d_statistics.d_num_quants_init_fail);
    }
  }
  return 0;
}

void ModelEngine::buildRepresentatives(){
  //initialize the model
  d_model.clear();
  d_quantEngine->getTheoryEngine()->collectModelInfo( &d_model );
  d_model.initialize();
  if( Options::current()->printModelEngine ){
    for( std::map< TypeNode, std::vector< Node > >::iterator it = d_model.d_ra.d_type_reps.begin(); it != d_model.d_ra.d_type_reps.end(); ++it ){
      if( uf::StrongSolverTheoryUf::isRelevantType( it->first ) ){
        Message() << "Cardinality( " << it->first << " )" << " = " << it->second.size() << std::endl;
      }
    }
  }
/*
  //old method
  d_model.d_ra.clear();
  uf::StrongSolverTheoryUf* ss = ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->getTheory( THEORY_UF ))->getStrongSolver();
  //collect all representatives for all types and store as representative alphabet
  for( int i=0; i<ss->getNumCardinalityTypes(); i++ ){
    TypeNode tn = ss->getCardinalityType( i );
    std::vector< Node > reps;
    ss->getRepresentatives( tn, reps );
    Assert( !reps.empty() );
    Debug("fmf-model-debug") << "   " << tn << " -> " << reps.size() << std::endl;
    Debug("fmf-model-debug") << "      ";
    for( int i=0; i<(int)reps.size(); i++ ){
      //if( reps[i].getAttribute(ModelBasisAttribute()) ){
      //  reps[i] = d_quantEngine->getEqualityQuery()->getInternalRepresentative( reps[i] );
      //}
      //Assert( !reps[i].getAttribute(ModelBasisAttribute()) );
      Debug("fmf-model-debug") << reps[i] << " ";
    }
    Debug("fmf-model-debug") << std::endl;
    //set them in the alphabet
    d_model.d_ra.set( tn, reps );
    if( Options::current()->printModelEngine ){
      Message() << "Cardinality( " << tn << " )" << " = " << reps.size() << std::endl;
      //Message() << d_quantEngine->getEqualityQuery()->getRepresentative( NodeManager::currentNM()->mkConst( true ) ) << std::endl;
    }
    //if( reps.size()!=d_model.d_ra.d_type_reps[tn].size() ){
    //  std::cout << reps.size() << " " << d_model.d_ra.d_type_reps[tn].size() << std::endl;
    //}
  }
*/
}

void ModelEngine::initializeModel(){
  d_quant_model_lits.clear();
  d_quant_sat.clear();
  d_model.d_uf_model.clear();

  for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    //collect uf terms and initialize uf models
    std::vector< Node > terms;
    collectUfTerms( f[1], terms );
    for( size_t j=0; j<terms.size(); j++ ){
      initializeUfModel( terms[j].getOperator() );
    }
  }
  if( optUseRelevantDomain() ){
    d_rel_domain.compute();
  }
}

void ModelEngine::analyzeQuantifiers(){
  int quantSatInit = 0;
  int nquantSatInit = 0;
  //analyze the preferences of each quantifier
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    Debug("fmf-model-prefs") << "Analyze quantifier " << f << std::endl;
    std::vector< Node > pro_con[2];
    std::vector< Node > constantSatOps;
    bool constantSatReconsider;
    //for each asserted quantifier f,
    // - determine which literals form model basis for each quantifier
    // - check which function/predicates have good and bad definitions according to f
    for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
         it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
      Node n = it->first;
      Node gn = d_model_basis[n];
      Debug("fmf-model-req") << "   Req: " << n << " -> " << it->second << std::endl;
      //calculate preference
      int pref = 0;
      bool value;
      if( d_quantEngine->getValuation().hasSatValue( gn, value ) ){
        if( value!=it->second ){
          //store this literal as a model basis literal
          //  this literal will force a default values in model that (modulo exceptions) shows
          //  that f is satisfied by the model
          d_quant_model_lits[f].push_back( value ? n : n.notNode() );
          pref = 1;
        }else{
          pref = -1;
        }
      }
      if( pref!=0 ){
        //Store preferences for UF
        bool isConst = !n.hasAttribute(InstConstantAttribute());
        std::vector< Node > uf_terms;
        if( gn.getKind()==APPLY_UF ){
          uf_terms.push_back( gn );
          isConst = d_model.d_uf_model[gn.getOperator()].isConstant();
        }else if( gn.getKind()==EQUAL ){
          isConst = true;
          for( int j=0; j<2; j++ ){
            if( n[j].hasAttribute(InstConstantAttribute()) ){
              if( n[j].getKind()==APPLY_UF ){
                Node op = gn[j].getOperator();
                if( d_model.d_uf_model.find( op )!=d_model.d_uf_model.end() ){
                  uf_terms.push_back( gn[j] );
                  isConst = isConst && d_model.d_uf_model[op].isConstant();
                }else{
                  isConst = false;
                }
              }else{
                isConst = false;
              }
            }
          }
        }
        Debug("fmf-model-prefs") << "  It is " << ( pref==1 ? "pro" : "con" );
        Debug("fmf-model-prefs") << " the definition of " << n << std::endl;
        if( pref==1 && isConst ){
          d_quant_sat[f] = true;
          //instead, just note to the model for each uf term that f is pro its definition
          constantSatReconsider = false;
          constantSatOps.clear();
          for( int j=0; j<(int)uf_terms.size(); j++ ){
            Node op = uf_terms[j].getOperator();
            constantSatOps.push_back( op );
            if( d_model.d_uf_model[op].d_reconsider_model ){
              constantSatReconsider = true;
            }
          }
          if( !constantSatReconsider ){
            break;
          }
	      }else{
          int pcIndex = pref==1 ? 0 : 1;
          for( int j=0; j<(int)uf_terms.size(); j++ ){
            pro_con[pcIndex].push_back( uf_terms[j] );
          }
        }
      }
    }
    if( d_quant_sat.find( f )!=d_quant_sat.end() ){
      Debug("fmf-model-prefs") << "  * Constant SAT due to definition of ops: ";
      for( int i=0; i<(int)constantSatOps.size(); i++ ){
        Debug("fmf-model-prefs") << constantSatOps[i] << " ";
        d_model.d_uf_model[constantSatOps[i]].d_reconsider_model = false;
      }
      Debug("fmf-model-prefs") << std::endl;
      quantSatInit++;
      d_statistics.d_pre_sat_quant += quantSatInit;
    }else{
      nquantSatInit++;
      d_statistics.d_pre_nsat_quant += quantSatInit;
      //note quantifier's value preferences to models
      for( int k=0; k<2; k++ ){
        for( int j=0; j<(int)pro_con[k].size(); j++ ){
          Node op = pro_con[k][j].getOperator();
          d_model.d_uf_model[op].setValuePreference( f, pro_con[k][j], k==0 );
        }
      }
    }
  }
  Debug("fmf-model-prefs") << "Pre-Model Completion: Quantifiers SAT: " << quantSatInit << " / " << (quantSatInit+nquantSatInit) << std::endl;
}

int ModelEngine::doInstGen( Node f ){
  //we wish to add all known exceptions to our model basis literal(s)
  //  this will help to refine our current model.
  //This step is advantageous over exhaustive instantiation, since we are adding instantiations that involve model basis terms,
  //  effectively acting as partial instantiations instead of pointwise instantiations.
  int addedLemmas = 0;
  for( int i=0; i<(int)d_quant_model_lits[f].size(); i++ ){
    bool phase = d_quant_model_lits[f][i].getKind()!=NOT;
    Node lit = d_quant_model_lits[f][i].getKind()==NOT ? d_quant_model_lits[f][i][0] : d_quant_model_lits[f][i];
    Assert( lit.hasAttribute(InstConstantAttribute()) );
    std::vector< Node > tr_terms;
    if( lit.getKind()==APPLY_UF ){
      //only match predicates that are contrary to this one, use literal matching
      Node eq = NodeManager::currentNM()->mkNode( IFF, lit, !phase ? d_model.d_true : d_model.d_false );
      d_quantEngine->setInstantiationConstantAttr( eq, f );
      tr_terms.push_back( eq );
    }else if( lit.getKind()==EQUAL ){
      //collect trigger terms
      for( int j=0; j<2; j++ ){
        if( lit[j].hasAttribute(InstConstantAttribute()) ){
          if( lit[j].getKind()==APPLY_UF ){
            tr_terms.push_back( lit[j] );
          }else{
            tr_terms.clear();
            break;
          }
        }
      }
      if( tr_terms.size()==1 && !phase ){
        //equality between a function and a ground term, use literal matching
        tr_terms.clear();
        tr_terms.push_back( lit );
      }
    }
    //if applicable, try to add exceptions here
    if( !tr_terms.empty() ){
      //make a trigger for these terms, add instantiations
      Trigger* tr = Trigger::mkTrigger( d_quantEngine, f, tr_terms );
      //Notice() << "Trigger = " << (*tr) << std::endl;
      tr->resetInstantiationRound();
      tr->reset( Node::null() );
      //d_quantEngine->d_optInstMakeRepresentative = false;
      //d_quantEngine->d_optMatchIgnoreModelBasis = true;
      addedLemmas += tr->addInstantiations( d_quant_basis_match[f] );
    }
  }
  return addedLemmas;
}

int ModelEngine::exhaustiveInstantiate( Node f, bool useRelInstDomain ){
  int tests = 0;
  int addedLemmas = 0;
  int triedLemmas = 0;
  Debug("inst-fmf-ei") << "Add matches for " << f << "..." << std::endl;
  Debug("inst-fmf-ei") << "   Instantiation Constants: ";
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Debug("inst-fmf-ei") << d_quantEngine->getInstantiationConstant( f, i ) << " ";
  }
  Debug("inst-fmf-ei") << std::endl;
  if( d_quant_model_lits[f].empty() ){
    Debug("inst-fmf-ei") << "WARNING: " << f << " has no model literal definitions (is f clausified?)" << std::endl;
#ifdef ME_PRINT_WARNINGS
    Message() << "WARNING: " << f << " has no model literal definitions (is f clausified?)" << std::endl;
#endif
  }else{
    Debug("inst-fmf-ei") << "  Model literal definitions:" << std::endl;
    for( size_t i=0; i<d_quant_model_lits[f].size(); i++ ){
      Debug("inst-fmf-ei") << "    " << d_quant_model_lits[f][i] << std::endl;
    }
  }
  RepSetIterator riter( d_quantEngine, f, &d_model );
  //set the domain for the iterator (the sufficient set of instantiations to try)
  if( useRelInstDomain ){
    riter.setDomain( d_rel_domain.d_quant_inst_domain[f] );
  }
  RepSetEvaluator reval( d_quantEngine, &riter );
  while( !riter.isFinished() && ( addedLemmas==0 || !optOneInstPerQuantRound() ) ){
    d_testLemmas++;
    if( optUseModel() ){
      //see if instantiation is already true in current model
      Debug("fmf-model-eval") << "Evaluating ";
      riter.debugPrintSmall("fmf-model-eval");
      //calculate represenative terms we are currently considering
      riter.calculateTerms( d_quantEngine );
      Debug("fmf-model-eval") << "Done calculating terms." << std::endl;
      tests++;
      //if evaluate(...)==1, then the instantiation is already true in the model
      //  depIndex is the index of the least significant variable that this evaluation relies upon
      int depIndex = riter.getNumTerms()-1;
      int eval = reval.evaluate( d_quantEngine->getCounterexampleBody( f ), depIndex );
      if( eval==1 ){
        Debug("fmf-model-eval") << "  Returned success with depIndex = " << depIndex << std::endl;
        riter.increment2( d_quantEngine, depIndex );
      }else{
        Debug("fmf-model-eval") << "  Returned " << (eval==-1 ? "failure" : "unknown") << ", depIndex = " << depIndex << std::endl;
        InstMatch m;
        riter.getMatch( d_quantEngine, m );
        Debug("fmf-model-eval") << "* Add instantiation " << m << std::endl;
        triedLemmas++;
        d_triedLemmas++;
        if( d_quantEngine->addInstantiation( f, m ) ){
          addedLemmas++;
#ifdef EVAL_FAIL_SKIP_MULTIPLE
          if( eval==-1 ){
            riter.increment2( d_quantEngine, depIndex );
          }else{
            riter.increment( d_quantEngine );
          }
#else
          riter.increment( d_quantEngine );
#endif
        }else{
          Debug("ajr-temp") << "* Failed Add instantiation " << m << std::endl;
          riter.increment( d_quantEngine );
        }
      }
    }else{
      InstMatch m;
      riter.getMatch( d_quantEngine, m );
      Debug("fmf-model-eval") << "* Add instantiation " << std::endl;
      triedLemmas++;
      d_triedLemmas++;
      if( d_quantEngine->addInstantiation( f, m ) ){
        addedLemmas++;
      }
      riter.increment( d_quantEngine );
    }
  }
  int totalInst = 1;
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    totalInst = totalInst * (int)getReps()->d_type_reps[ f[0][i].getType() ].size();
  }
  d_totalLemmas += totalInst;
  Debug("inst-fmf-ei") << "Finished: " << std::endl;
  Debug("inst-fmf-ei") << "   Inst Skipped: " << (totalInst-triedLemmas) << std::endl;
  Debug("inst-fmf-ei") << "   Inst Tried: " << triedLemmas << std::endl;
  Debug("inst-fmf-ei") << "   Inst Added: " << addedLemmas << std::endl;
  Debug("inst-fmf-ei") << "   # Tests: " << tests << std::endl;
///-----------
#ifdef ME_PRINT_WARNINGS
  if( addedLemmas>1000 ){
    Notice() << "WARNING: many instantiations produced for " << f << ": " << std::endl;
    Notice() << "   Inst Skipped: " << (totalInst-triedLemmas) << std::endl;
    Notice() << "   Inst Tried: " << triedLemmas << std::endl;
    Notice() << "   Inst Added: " << addedLemmas << std::endl;
    Notice() << "   # Tests: " << tests << std::endl;
    Notice() << std::endl;
    if( !d_quant_model_lits[f].empty() ){
      Notice() << "  Model literal definitions:" << std::endl;
      for( size_t i=0; i<d_quant_model_lits[f].size(); i++ ){
        Notice() << "    " << d_quant_model_lits[f][i] << std::endl;
      }
      Notice() << std::endl;
    }
  }
#endif
///-----------
  return addedLemmas;
}

void ModelEngine::registerModelBasis( Node n, Node gn ){
  if( d_model_basis.find( n )==d_model_basis.end() ){
    d_model_basis[n] = gn;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerModelBasis( n[i], gn[i] );
    }
  }
}

Node ModelEngine::getModelBasisTerm( TypeNode tn, int i ){
  if( d_model_basis_term.find( tn )==d_model_basis_term.end() ){
    std::stringstream ss;
    ss << Expr::setlanguage(Options::current()->outputLanguage);
    ss << "e_" << tn;
    d_model_basis_term[tn] = NodeManager::currentNM()->mkVar( ss.str(), tn );
    ModelBasisAttribute mba;
    d_model_basis_term[tn].setAttribute(mba,true);
  }
  return d_model_basis_term[tn];
}

Node ModelEngine::getModelBasisOpTerm( Node op ){
  if( d_model_basis_op_term.find( op )==d_model_basis_op_term.end() ){
    TypeNode t = op.getType();
    std::vector< Node > children;
    children.push_back( op );
    for( size_t i=0; i<t.getNumChildren()-1; i++ ){
      children.push_back( getModelBasisTerm( t[i] ) );
    }
    d_model_basis_op_term[op] = NodeManager::currentNM()->mkNode( APPLY_UF, children );
  }
  return d_model_basis_op_term[op];
}

void ModelEngine::collectUfTerms( Node n, std::vector< Node >& terms ){
  if( n.getKind()==APPLY_UF ){
    terms.push_back( n );
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    collectUfTerms( n[i], terms );
  }
}

void ModelEngine::initializeUfModel( Node op ){
  if( d_model.d_uf_model.find( op )==d_model.d_uf_model.end() ){
    TypeNode tn = op.getType();
    tn = tn[ (int)tn.getNumChildren()-1 ];
    if( tn==NodeManager::currentNM()->booleanType() || uf::StrongSolverTheoryUf::isRelevantType( tn ) ){
      d_model.d_uf_model[ op ] = uf::UfModel( op, &d_model, d_quantEngine );
    }
  }
}

void ModelEngine::debugPrint( const char* c ){
  Debug( c ) << "Quantifiers: " << std::endl;
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    Debug( c ) << "   ";
    if( d_quant_sat.find( f )!=d_quant_sat.end() ){
      Debug( c ) << "*SAT* ";
    }else{
      Debug( c ) << "      ";
    }
    Debug( c ) << f << std::endl;
  }
  d_model.debugPrint( c );
}

ModelEngine::Statistics::Statistics():
  d_inst_rounds("ModelEngine::Inst_Rounds", 0),
  d_pre_sat_quant("ModelEngine::Status_quant_pre_sat", 0),
  d_pre_nsat_quant("ModelEngine::Status_quant_pre_non_sat", 0),
  d_eval_formulas("ModelEngine::Eval_Formulas", 0 ),
  d_eval_eqs("ModelEngine::Eval_Equalities", 0 ),
  d_eval_uf_terms("ModelEngine::Eval_Uf_Terms", 0 ),
  d_num_quants_init("ModelEngine::Num_Quants", 0 ),
  d_num_quants_init_fail("ModelEngine::Num_Quants_No_Basis", 0 )
{
  StatisticsRegistry::registerStat(&d_inst_rounds);
  StatisticsRegistry::registerStat(&d_pre_sat_quant);
  StatisticsRegistry::registerStat(&d_pre_nsat_quant);
  StatisticsRegistry::registerStat(&d_eval_formulas);
  StatisticsRegistry::registerStat(&d_eval_eqs);
  StatisticsRegistry::registerStat(&d_eval_uf_terms);
  StatisticsRegistry::registerStat(&d_num_quants_init);
  StatisticsRegistry::registerStat(&d_num_quants_init_fail);
}

ModelEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_inst_rounds);
  StatisticsRegistry::unregisterStat(&d_pre_sat_quant);
  StatisticsRegistry::unregisterStat(&d_pre_nsat_quant);
  StatisticsRegistry::unregisterStat(&d_eval_formulas);
  StatisticsRegistry::unregisterStat(&d_eval_eqs);
  StatisticsRegistry::unregisterStat(&d_eval_uf_terms);
  StatisticsRegistry::unregisterStat(&d_num_quants_init);
  StatisticsRegistry::unregisterStat(&d_num_quants_init_fail);
}



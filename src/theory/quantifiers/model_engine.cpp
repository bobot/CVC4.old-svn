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

#include "theory/theory_engine.h"
#include "theory/uf/equality_engine_impl.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf_instantiator.h"

#define ME_PRINT_PROCESS_TIMES

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

void printRepresentative( const char* c, QuantifiersEngine* qe, Node r ){
  if( r.getType()==NodeManager::currentNM()->booleanType() ){
    if( qe->getEqualityQuery()->areEqual( r, NodeManager::currentNM()->mkConst( true ) ) ){
      Debug( c ) << "true";
    }else{
      Debug( c ) << "false";
    }
  }else{
    Debug( c ) << qe->getEqualityQuery()->getRepresentative( r );
  }
}

RepAlphabet::RepAlphabet( RepAlphabet& ra, QuantifiersEngine* qe ){
  //translate to current representatives
  for( std::map< TypeNode, std::vector< Node > >::iterator it = ra.d_type_reps.begin(); it != ra.d_type_reps.end(); ++it ){
    std::vector< Node > reps;
    for( int i=0; i<(int)it->second.size(); i++ ){
      //reps.push_back( ie->getEqualityQuery()->getRepresentative( it->second[i] ) );
      reps.push_back( it->second[i] );
    }
    set( it->first, reps );
  }
}

void RepAlphabet::set( TypeNode t, std::vector< Node >& reps ){
  d_type_reps[t].insert( d_type_reps[t].begin(), reps.begin(), reps.end() );
  for( int i=0; i<(int)reps.size(); i++ ){
    d_tmap[ reps[i] ] = i;
  }
}

void RepAlphabet::debugPrint( const char* c, QuantifiersEngine* qe ){
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    Debug( c ) << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      Debug( c ) << "   " << i << ": " << it->second[i] << std::endl;
      Debug( c ) << "         eq_class( " << it->second[i] << " ) : ";
      ((uf::InstantiatorTheoryUf*)qe->getInstantiator( THEORY_UF ))->outputEqClass( c, it->second[i] );
      Debug( c ) << std::endl;
    }
  }
}

RepAlphabetIterator::RepAlphabetIterator( QuantifiersEngine* qe, Node f, ModelEngine* model ) : d_f( f ), d_model( model ){
  //store instantiation constants
  for( int i=0; i<qe->getNumInstantiationConstants( d_f ); i++ ){
    d_ic.push_back( qe->getInstantiationConstant( d_f, i ) );
  }
  d_index.resize( f[0].getNumChildren(), 0 );
  //d_model->increment( this );
  //for testing
  d_inst_skipped = 0;
  d_inst_tried = 0;
  d_inst_tests = 0;
}

void RepAlphabetIterator::increment2( QuantifiersEngine* qe, int counter ){
  Assert( !isFinished() );
  Assert( counter>=0 );
  //increment d_index
  while( d_index[counter]==(int)(d_model->getReps()->d_type_reps[d_f[0][counter].getType()].size()-1) ){
    d_index[counter] = 0;
    counter--;
    if( counter==-1 ){
      d_index.clear();
      return;
    }
  }
  d_index[counter]++;
  //d_model->increment( this );
}

void RepAlphabetIterator::increment( QuantifiersEngine* qe ){
  if( !isFinished() ){
    int counter = (int)d_index.size()-1;
    increment2( qe, counter );
  }
}

bool RepAlphabetIterator::isFinished(){
  return d_index.empty();
}

void RepAlphabetIterator::getMatch( QuantifiersEngine* ie, InstMatch& m ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    m.d_map[ ie->getInstantiationConstant( d_f, i ) ] = getTerm( i );
  }
}

Node RepAlphabetIterator::getTerm( int i ){
  TypeNode tn = d_f[0][i].getType();
  Assert( d_model->getReps()->d_type_reps.find( tn )!=d_model->getReps()->d_type_reps.end() );
  return d_model->getReps()->d_type_reps[tn][d_index[i]];
}

void RepAlphabetIterator::calculateTerms( QuantifiersEngine* qe ){
  d_terms.clear();
  for( int i=0; i<qe->getNumInstantiationConstants( d_f ); i++ ){
    d_terms.push_back( getTerm( i ) );
  }
}

void RepAlphabetIterator::debugPrint( const char* c ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    Debug( c ) << i << ": " << d_index[i] << ", (" << getTerm( i ) << " / " << d_ic[ i ] << std::endl;
  }
}

void RepAlphabetIterator::debugPrintSmall( const char* c ){
  Debug( c ) << "RI: ";
  for( int i=0; i<(int)d_index.size(); i++ ){
    Debug( c ) << d_index[i] << ": " << getTerm( i ) << " ";
  }
  Debug( c ) << std::endl;
}

void UfModelTree::setValue2( QuantifiersEngine* qe, Node n, Node v, int argIndex, bool ground ){
  if( d_data.empty() ){
    d_value = v;
  }else if( !d_value.isNull() && d_value!=v ){
    d_value = Node::null();
  }
  if( argIndex<(int)n.getNumChildren() ){
    //take r = null when argument is the model basis
    Node r;
    if( ground || !n[ argIndex ].getAttribute(ModelBasisAttribute()) ){
      r = qe->getEqualityQuery()->getRepresentative( n[ argIndex ] );
    }
    d_data[ r ].setValue2( qe, n, v, argIndex+1, ground );
  }
}

void UfModelTree::setValue( QuantifiersEngine* qe, Node n, Node v, bool ground ) { 
  setValue2( qe, n, v, 0, ground ); 
}

Node UfModelTree::getValue2( QuantifiersEngine* qe, Node n, int& depIndex, int argIndex ){
  //std::cout << "getValue2 " << n << " " << argIndex << std::endl;
  if( !d_value.isNull() && isTotal2( n.getOperator(), argIndex ) ){
    //std::cout << "Constant, return " << d_value << ", depIndex = " << argIndex << std::endl;
    depIndex = argIndex;
    return d_value;
  }else{
    Node val;
    int index = -1;
    int childDepIndex[2] = { argIndex, argIndex };
    for( int i=0; i<2; i++ ){
      //first check the argument, then check default
      Node r;
      if( i==0 ){
        r = qe->getEqualityQuery()->getRepresentative( n[ argIndex ] );
      }
      std::map< Node, UfModelTree >::iterator it = d_data.find( r );
      if( it!=d_data.end() ){
        val = it->second.getValue2( qe, n, childDepIndex[i], argIndex+1 );
        if( !val.isNull() ){
          break;
        }
      }else{
        //argument is not a defined argument: thus, it depends on this argument
        childDepIndex[i] = argIndex+1;
      }
    }
    //update depIndex
    depIndex = childDepIndex[0]>childDepIndex[1] ? childDepIndex[0] : childDepIndex[1];
    //std::cout << "Return " << val << ", depIndex = " << depIndex;
    //std::cout << " ( " << childDepIndex[0] << ", " << childDepIndex[1] << " )" << std::endl;
    return val;
  }
}

Node UfModelTree::getValue( QuantifiersEngine* qe, Node n, int& depIndex ) { 
  return getValue2( qe, n, depIndex, 0 ); 
}

//helper function for simplify
void UfModelTree::simplify2( Node op, Node defaultVal, int argIndex ){
  if( argIndex<(int)op.getType().getNumChildren()-1 ){
    std::vector< Node > eraseData;
    //first process the default argument
    Node r;
    std::map< Node, UfModelTree >::iterator it = d_data.find( r );
    if( it!=d_data.end() ){
      if( !defaultVal.isNull() && it->second.d_value==defaultVal ){
        eraseData.push_back( r );
      }else{
        it->second.simplify2( op, defaultVal, argIndex+1 );
        if( !it->second.d_value.isNull() && it->second.isTotal2( op, argIndex+1 ) ){
          defaultVal = it->second.d_value;
        }else{
          defaultVal = Node::null();
        }
      }
    }
    //now see if any children can be removed, and simplify the ones that cannot
    for( std::map< Node, UfModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( !it->first.isNull() ){
        if( !defaultVal.isNull() && it->second.d_value==defaultVal ){
          eraseData.push_back( it->first );
        }else{
          it->second.simplify2( op, defaultVal, argIndex+1 );
        }
      }
    }
    for( int i=0; i<(int)eraseData.size(); i++ ){
      d_data.erase( eraseData[i] );
    }
  }
}

//helper function for is total
bool UfModelTree::isTotal2( Node op, int argIndex ){
  if( argIndex==(int)(op.getType().getNumChildren()-1) ){
    return !d_value.isNull();
  }else{
    Node r;
    std::map< Node, UfModelTree >::iterator it = d_data.find( r );
    if( it!=d_data.end() ){
      return it->second.isTotal2( op, argIndex+1 );
    }else{
      return false;
    }
  }
}

//Node UfModelTree::getConstantValue2( QuantifiersEngine* qe, Node n, int argIndex ){
//  return Node::null();
//}

void indent( const char* c, int ind ){
  for( int i=0; i<ind; i++ ){
    Debug( c ) << " ";
  }
}

void UfModelTree::debugPrint( const char* c, QuantifiersEngine* qe, int ind, int arg ){
  if( !d_data.empty() ){
    for( std::map< Node, UfModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( !it->first.isNull() ){
        indent( c, ind );
        Debug( c ) << "if x_" << arg << " == " << it->first << std::endl;
        it->second.debugPrint( c, qe, ind+2, arg+1 );
      }
    }
    if( d_data.find( Node::null() )!=d_data.end() ){
      d_data[ Node::null() ].debugPrint( c, qe, ind, arg+1 );
    }
  }else{
    indent( c, ind );
    Debug( c ) << "return ";
    printRepresentative( c, qe, d_value );
    //Debug( c ) << " { ";
    //for( int i=0; i<(int)d_explicit.size(); i++ ){
    //  Debug( c ) << d_explicit[i] << " ";
    //}
    //Debug( c ) << "}";
    Debug( c ) << std::endl;
  }
}

UfModel::UfModel( Node op, ModelEngine* me ) : d_op( op ), d_me( me ), d_model_constructed( false ){
  //look at ground assertions
  for( int i=0; i<(int)d_me->getQuantifiersEngine()->getTermDatabase()->d_op_map[ d_op ].size(); i++ ){
    Node n = d_me->getQuantifiersEngine()->getTermDatabase()->d_op_map[ d_op ][i];
    bool add = true;
    if( n.getAttribute(NoMatchAttribute()) ){
      add = false;
      //determine if it has model basis attribute
      for( int j=0; j<(int)n.getNumChildren(); j++ ){
        if( n[j].getAttribute(ModelBasisAttribute()) ){
          add = true;
          break;
        }
      }
    }
    if( add ){
      d_ground_asserts.push_back( n );
    }
  }
  //determine if it is constant
  if( !d_ground_asserts.empty() ){
    bool isConstant = true;
    for( int i=1; i<(int)d_ground_asserts.size(); i++ ){
      if( !d_me->areEqual( d_ground_asserts[0], d_ground_asserts[i] ) ){
        isConstant = false;
        break;
      }
    }
    if( isConstant ){
      //set constant value
      Node r = d_me->getQuantifiersEngine()->getEqualityQuery()->getRepresentative( d_ground_asserts[0] );
      Node t = d_me->getModelBasisTerm( d_op );
      setValue( t, r, false );
      d_model_constructed = true;
      Debug("fmf-model-cons") << "Function " << d_op << " is the constant function ";
      printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), r );
      Debug("fmf-model-cons") << std::endl;
    }
  }
}

void UfModel::setValue( Node n, Node v, bool ground ){
  d_tree.setValue( d_me->getQuantifiersEngine(), n, v, ground );
}

void UfModel::addRequirement( Node f, Node p, bool phase ){
  d_reqs[ phase ? 1 : 0 ][ f ].push_back( p );
}

void UfModel::addEqRequirement( Node f, Node t, Node te, bool phase ){
  d_eq_reqs[ phase ? 1 : 0 ][ f ][ t ].push_back( te );
}

Node UfModel::getConstantValue( QuantifiersEngine* qe, Node n ){
  if( d_model_constructed ){
    return d_tree.d_value;
  }else{
    return Node::null();
  }
}

bool UfModel::isConstant(){
  Node gn = d_me->getModelBasisTerm( d_op );
  Node n = getConstantValue( d_me->getQuantifiersEngine(), gn );
  return !n.isNull();
}

void UfModel::buildModel(){
  //now, construct models for each uninterpretted function/predicate
  if( !d_model_constructed ){
    if( !isEmpty() ){
      Debug("fmf-model-cons") << "Construct model for " << d_op << "..." << std::endl;
      //get the default term (this term must be defined non-ground in model)
      Node defaultTerm = d_me->getModelBasisTerm( d_op );
      //keep track of a best default value to set, if necessary
      bool setDefaultVal = true;
      //maps from values to quantifiers that prefer that value
      std::map< Node, std::vector< Node > > value_pro_con[2];
      std::map< Node, bool > values;
      //now, set the values in the model
      for( int i=0; i<(int)d_ground_asserts.size(); i++ ){
        Node n = d_ground_asserts[i];
        Node v = d_me->getQuantifiersEngine()->getEqualityQuery()->getRepresentative( n );
        values[v] = true;
        //if this assertion did not help the model, just consider it ground
        bool ground = d_me->d_quant_pro_con[0][n].empty();
        //set n = v in the model tree
        Debug("fmf-model-cons") << "  Set " << n << " = ";
        printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), v );
        Debug("fmf-model-cons") << ( !ground ? " (non-ground)" : "") << std::endl;
        setValue( n, v );
        if( !ground ){
          //also must set it as ground
          setValue( n, v, false );
        }
        //manage default value
        if( !ground && n==defaultTerm ){
          //default value incidently defined, will not need to chose one
          setDefaultVal = false;
        }else if( setDefaultVal ){
          //add pro/con quantifiers for current value
          for( int k=0; k<2; k++ ){
            for( int j=0; j<(int)d_me->d_quant_pro_con[k][n].size(); j++ ){
              if( std::find( value_pro_con[k][v].begin(), value_pro_con[k][v].end(), 
                             d_me->d_quant_pro_con[k][n][j] )==value_pro_con[k][v].end() ){
                value_pro_con[k][v].push_back( d_me->d_quant_pro_con[k][n][j] );
              }
            }
          }
        }
      }
      //set the default value, if not set already
      if( setDefaultVal ){
        //chose defaultVal based on heuristic (the best proportion of "pro" responses)
        Node defaultVal;
        double maxScore = -1;
        for( std::map< Node, bool >::iterator it = values.begin(); it != values.end(); ++it ){
          double score = ( 1.0 + (double)value_pro_con[0][it->first].size() )/( 1.0 + (double)value_pro_con[1][it->first].size() );
          Debug("fmf-model-cons") << "  - score( ";
          printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), it->first );
          Debug("fmf-model-cons") << " ) = " << score << std::endl;
          if( score>maxScore ){
            defaultVal = it->first;
            maxScore = score;
          }
        }
        if( maxScore<1.0 ){
          //consider finding another value, if possible
        }
        Assert( !defaultVal.isNull() );
        Debug("fmf-model-cons") << "  Choose ";
        printRepresentative("fmf-model-cons", d_me->getQuantifiersEngine(), defaultVal );
        Debug("fmf-model-cons") << " as default value (" << defaultTerm << ")" << std::endl;
        Debug("fmf-model-cons") << "     # quantifiers pro = " << value_pro_con[0][defaultVal].size() << std::endl;
        Debug("fmf-model-cons") << "     # quantifiers con = " << value_pro_con[1][defaultVal].size() << std::endl;
        setValue( defaultTerm, defaultVal, false );
      }else{
        Debug("fmf-model-cons") << "   Default value already set." << std::endl;
      }
      Debug("fmf-model-cons") << "  Simplifying model...";
      simplify();
      Debug("fmf-model-cons") << "  Finished constructing model for " << d_op << "." << std::endl;
    }
    d_model_constructed = true;
  }
}

void UfModel::debugPrint( const char* c ){
  //Debug( c ) << "Function " << d_op << std::endl;
  //Debug( c ) << "   Type: " << d_op.getType() << std::endl;
  //Debug( c ) << "   Ground asserts:" << std::endl;
  //for( int i=0; i<(int)d_ground_asserts.size(); i++ ){
  //  Debug( c ) << "      " << d_ground_asserts[i] << " = ";
  //  printRepresentative( c, d_me->getQuantifiersEngine(), d_ground_asserts[i] );
  //  Debug( c ) << std::endl;
  //}
  //Debug( c ) << "   Model:" << std::endl;

  TypeNode t = d_op.getType();
  Debug( c ) << d_op << "( ";
  for( int i=0; i<(int)(t.getNumChildren()-1); i++ ){
    Debug( c ) << "x_" << i << " : " << t[i];
    if( i<(int)(t.getNumChildren()-2) ){
      Debug( c ) << ", ";
    }
  }
  Debug( c ) << " ) : " << t[(int)t.getNumChildren()-1] << std::endl;
  if( d_tree.isEmpty() ){
    Debug( c ) << "   [undefined]" << std::endl;
  }else{
    d_tree.debugPrint( c, d_me->getQuantifiersEngine(), 3 );
    Debug( c ) << std::endl;
  }
  //Debug( c ) << "   Phase reqs:" << std::endl;  //for( int i=0; i<2; i++ ){
  //  for( std::map< Node, std::vector< Node > >::iterator it = d_reqs[i].begin(); it != d_reqs[i].end(); ++it ){
  //    Debug( c ) << "      " << it->first << std::endl;
  //    for( int j=0; j<(int)it->second.size(); j++ ){
  //      Debug( c ) << "         " << it->second[j] << " -> " << (i==1) << std::endl;
  //    }
  //  }
  //}
  //Debug( c ) << std::endl;
  //for( int i=0; i<2; i++ ){
  //  for( std::map< Node, std::map< Node, std::vector< Node > > >::iterator it = d_eq_reqs[i].begin(); it != d_eq_reqs[i].end(); ++it ){
  //    Debug( c ) << "      " << "For " << it->first << ":" << std::endl;
  //    for( std::map< Node, std::vector< Node > >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
  //      for( int j=0; j<(int)it2->second.size(); j++ ){
  //        Debug( c ) << "         " << it2->first << ( i==1 ? "==" : "!=" ) << it2->second[j] << std::endl;
  //      }
  //    }
  //  }
  //}
}

//Model Engine constructor
ModelEngine::ModelEngine( TheoryQuantifiers* th ){
  d_th = th;
  d_quantEngine = th->getQuantifiersEngine();
  d_ss = ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->getTheory( THEORY_UF ))->getStrongSolver();
}

void ModelEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_LAST_CALL ){
    bool quantsInit = true;
    //first, check if we can minimize the model further
    if( !d_ss->minimize() ){
      return;
    }
    if( useModel() ){
      //now, check if any quantifiers are un-initialized
      for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
        Node f = d_quantEngine->getAssertedQuantifier( i );
        if( d_quant_init.find( f )==d_quant_init.end() ){
          Debug("inst-fmf-init") << "Initialize " << f << std::endl;
          //add the model basis instantiation
          // This will help produce the necessary information for model completion.
          // We do this by extending distinguish ground assertions (those containing "model basis" terms) to hold for all cases.
          std::vector< Node > terms;
          for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
            terms.push_back( d_ss->getModelBasisTerm( f[0][j].getType() ) );
          }
          if( d_quantEngine->addInstantiation( f, terms ) ){
            quantsInit = false;
          }else{
            //should probably never happen
            //TODO: make sure it does not!!
          }
          d_quant_init[f] = true;
        }
      }
    }
    if( quantsInit ){
#ifdef ME_PRINT_PROCESS_TIMES
      std::cout << "---Instantiation Round---" << std::endl;
#endif
      Debug("fmf-model-debug") << "---Begin Instantiation Round---" << std::endl;
      d_quantEngine->getTermDatabase()->reset( e );
      //build the representatives
      Debug("fmf-model-debug") << "Building representatives..." << std::endl;
      buildRepresentatives();
      if( useModel() ){
        //initialize the model
        Debug("fmf-model-debug") << "Initializing model..." << std::endl;
        initializeModel();
        //analyze the quantifiers
        Debug("fmf-model-debug") << "Analyzing quantifiers..." << std::endl;
        analyzeQuantifiers();
        //build the model
        Debug("fmf-model-debug") << "Building model..." << std::endl;
        for( std::map< Node, UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
          it->second.buildModel();
        }
      }
      //print debug
      debugPrint("fmf-model-complete");
      //try exhaustive instantiation
      Debug("fmf-model-debug") << "Do exhaustive instantiation..." << std::endl;
      int addedLemmas = 0;
      for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
        Node f = d_quantEngine->getAssertedQuantifier( i );
        if( d_quant_sat.find( f )==d_quant_sat.end() ){
          Debug("inst-fmf-ei") << "Add matches for " << f << "..." << std::endl;
          Debug("inst-fmf-ei") << "   ";
          for( int i=0; i<f[0].getNumChildren(); i++ ){
            Debug("inst-fmf-ei") << d_quantEngine->getInstantiationConstant( f, i ) << " ";
          }
          Debug("inst-fmf-ei") << std::endl;
          int prevAddedLemmas = addedLemmas;
          RepAlphabetIterator riter( d_quantEngine, f, this );
          increment( &riter );
          while( !riter.isFinished() ){
            InstMatch m;
            riter.getMatch( d_quantEngine, m );
            Debug("fmf-model-eval") << "* Add instantiation " << std::endl;
            riter.d_inst_tried++;
            if( d_quantEngine->addInstantiation( f, m ) ){
              addedLemmas++;
            }
            riter.increment( d_quantEngine );
            increment( &riter );
          }
          Debug("inst-fmf-ei") << "Finished: " << std::endl;
          Debug("inst-fmf-ei") << "   Inst Skipped: " << riter.d_inst_skipped << std::endl;
          Debug("inst-fmf-ei") << "   Inst Tried: " << riter.d_inst_tried << std::endl;
          Debug("inst-fmf-ei") << "   Inst Added: " << (addedLemmas-prevAddedLemmas) << std::endl;
          Debug("inst-fmf-ei") << "   # Tests: " << riter.d_inst_tests << std::endl;
        }
      }
#ifdef ME_PRINT_PROCESS_TIMES
      std::cout << "Added Lemmas = " << addedLemmas << std::endl;
#endif
      if( addedLemmas==0 ){
        //debugPrint("fmf-consistent");
        //for( std::map< Node, UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
        //  it->second.simplify();
        //}
        debugPrint("fmf-consistent");
      }
    }
    d_quantEngine->flushLemmas( &d_th->getOutputChannel() );
  }
}

void ModelEngine::registerQuantifier( Node f ){

}

void ModelEngine::assertNode( Node f ){

}

bool ModelEngine::useModel() {
  return Options::current()->fmfModelBasedInst;
}

void ModelEngine::buildRepresentatives(){
  d_ra.clear();
  //collect all representatives for all types and store as representative alphabet
  for( int i=0; i<d_ss->getNumCardinalityTypes(); i++ ){
    TypeNode tn = d_ss->getCardinalityType( i );
    std::vector< Node > reps;
    d_ss->getRepresentatives( tn, reps );
    Assert( !reps.empty() );
    //if( (int)reps.size()!=d_ss->getCardinality( tn ) ){
    //  std::cout << "InstStrategyFinteModelFind::processResetInstantiationRound: Bad representatives for type." << std::endl;
    //  std::cout << "   " << tn << " has cardinality " << d_ss->getCardinality( tn );
    //  std::cout << " but only " << (int)reps.size() << " were given." << std::endl;
    //  exit( 27 );
    //}
    Debug("fmf-model-debug") << "   " << tn << " -> " << reps.size() << std::endl;
    Debug("fmf-model-debug") << "      ";
    for( int i=0; i<(int)reps.size(); i++ ){
      Debug("fmf-model-debug") << reps[i] << " ";
    }
    Debug("fmf-model-debug") << std::endl;
    //set them in the alphabet
    d_ra.set( tn, reps );
  }
#ifdef ME_PRINT_PROCESS_TIMES
  //"Representatives (" << reps.size() << ") for type " << tn << " (c=" << d_ss->getCardinality( tn ) << "): ";
#endif
}

void ModelEngine::initializeModel(){
  d_uf_model.clear();
  d_quant_pro_con[0].clear();
  d_quant_pro_con[1].clear();
  d_quant_sat.clear();
#if 1
  //now analyze quantifiers (temporary)
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    Debug("fmf-model-req") << "Phase requirements for " << f << ": " << std::endl;
    for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
         it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
      Node n = it->first;
      Debug("fmf-model-req") << "   " << n << " -> " << it->second << std::endl;
      if( n.getKind()==APPLY_UF ){
        processPredicate( f, n, it->second );
      }else if( n.getKind()==EQUAL ){
        processEquality( f, n, it->second );
      }
    }
  }
#endif
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    initializeUf( f[1] );
    //register model basis terms
    std::vector< Node > vars;
    std::vector< Node > subs;
    for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
      vars.push_back( d_quantEngine->getInstantiationConstant( f, j ) );
      subs.push_back( d_ss->getModelBasisTerm( f[0][j].getType() ) );
    }
    Node n = d_quantEngine->getCounterexampleBody( f );
    Node gn = n.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    registerModelBasis( n, gn );
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
    //check which model basis terms have good and bad definitions according to f
    for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
         it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
      Node n = it->first;
      Node gn = d_model_basis[n];
      Debug("fmf-model-req") << "   Req: " << n << " -> " << it->second << std::endl;
      int pref = 0;
      bool isConst = true;
      std::vector< Node > uf_terms;
      if( gn.getKind()==APPLY_UF ){
        if( d_quantEngine->getEqualityQuery()->hasTerm( gn ) ){
          uf_terms.push_back( gn );
          bool phase = areEqual( gn, NodeManager::currentNM()->mkConst( true ) );
          pref = phase!=it->second ? 1 : -1;
        }
      }else if( gn.getKind()==EQUAL ){
        for( int j=0; j<2; j++ ){
          if( n[j].getKind()==APPLY_UF ){
            uf_terms.push_back( n[j] );
          }else if( n[j].hasAttribute(InstConstantAttribute()) ){
            isConst = false;
          }
        }
        if( !uf_terms.empty() ){
          if( (!it->second && areEqual( gn[0], gn[1] )) || (it->second && areDisequal( gn[0], gn[1] )) ){
            pref = 1;
          }else if( (it->second && areEqual( gn[0], gn[1] )) || (!it->second && areDisequal( gn[0], gn[1] )) ){
            pref = -1;
          }
        }
      }
      if( pref!=0 ){
        Debug("fmf-model-prefs") << "  It is " << ( pref==1 ? "pro" : "con" );
        Debug("fmf-model-prefs") << " the definition of " << n << std::endl;
        if( pref==1 ){
          if( isConst ){
            for( int j=0; j<(int)uf_terms.size(); j++ ){
              //the only uf that is initialized are those that are constant
              Node op = uf_terms[j].getOperator();
              Assert( d_uf_model.find( op )!=d_uf_model.end() );
              if( !d_uf_model[op].isConstant() ){
                isConst = false;
                break;
              }
            }
            if( isConst ){
              d_quant_sat[f] = true;
              //we only need to consider current term definition(s) for this quantifier to be satisified, ignore the others
              pro_con[0].clear();
              pro_con[1].clear();
            }
          }
        }
        int index = pref==1 ? 0 : 1;
        for( int j=0; j<(int)uf_terms.size(); j++ ){
          pro_con[index].push_back( uf_terms[j] );
        }
        if( d_quant_sat.find( f )!=d_quant_sat.end() ){
          Debug("fmf-model-prefs") << "  * Constant SAT due to definition of " << n << std::endl;
          break;
        }
      }
    }
    if( d_quant_sat.find( f )!=d_quant_sat.end() ){
      quantSatInit++;
    }else{
      nquantSatInit++;
    }
    //add quantifier's preferences to vector
    for( int k=0; k<2; k++ ){
      for( int j=0; j<(int)pro_con[k].size(); j++ ){
        d_quant_pro_con[k][ pro_con[k][j] ].push_back( f );
      }
    }
  }
  Debug("fmf-model-prefs") << "Pre-Model Completion: Quantifiers SAT: " << quantSatInit << " / " << (quantSatInit+nquantSatInit) << std::endl;
}

void ModelEngine::registerModelBasis( Node n, Node gn ){
  if( d_model_basis.find( n )==d_model_basis.end() ){
    d_model_basis[n] = gn;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerModelBasis( n[i], gn[i] );
    }
  }
}

Node ModelEngine::getModelBasisTerm( Node op ){
  if( d_model_basis_term.find( op )==d_model_basis_term.end() ){
    TypeNode t = op.getType();
    std::vector< Node > children;
    children.push_back( op );
    for( int i=0; i<(int)t.getNumChildren()-1; i++ ){
      children.push_back( d_ss->getModelBasisTerm( t[i] ) );
    }
    d_model_basis_term[op] = NodeManager::currentNM()->mkNode( APPLY_UF, children );
  }
  return d_model_basis_term[op];
}

void ModelEngine::initializeUf( Node n ){
  if( n.getKind()==APPLY_UF ){
    initializeUfModel( n.getOperator() );
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    initializeUf( n[i] );
  }
}

void ModelEngine::initializeUfModel( Node op ){
  if( d_uf_model.find( op )==d_uf_model.end() ){
    d_uf_model[ op ] = UfModel( op, this );
  }
}

void ModelEngine::processPredicate( Node f, Node p, bool phase ){
  Node op = p.getOperator();
  initializeUfModel( op );
  d_uf_model[ op ].addRequirement( f, p, phase );
}

void ModelEngine::processEquality( Node f, Node eq, bool phase ){
  for( int i=0; i<2; i++ ){
    int j = i==0 ? 1 : 0;
    if( eq[i].getKind()==APPLY_UF && eq[i].hasAttribute(InstConstantAttribute()) ){
      Node op = eq[i].getOperator();
      initializeUfModel( op );
      d_uf_model[ op ].addEqRequirement( f, eq[i], eq[j], phase );
    }
  }
}

void ModelEngine::increment( RepAlphabetIterator* rai ){
  if( useModel() ){
    bool success;
    do{
      success = true;
      if( !rai->isFinished() ){
        //see if instantiation is already true in current model
        Debug("fmf-model-eval") << "Evaulating ";
        rai->debugPrintSmall("fmf-model-eval");
        //calculate represenative terms we are currently considering
        rai->calculateTerms( d_quantEngine );
        rai->d_inst_tests++;
        //if eVal is not -1, then the instantiation is already true in the model,
        // and eVal is the highest index in rai which we can safely iterate
        int eVal = evaluate( rai, d_quantEngine->getCounterexampleBody( rai->d_f ), true );
        Debug("fmf-model-eval") << "  Returned eVal = " << eVal << std::endl;
        if( eVal<(int)rai->d_index.size() ){
          //eVal = (int)rai->d_index.size()-1;  //temporary
          //TODO: make sure eVal is legitament
          //int instSkipped = 1;
          int index = (int)rai->d_index.size()-1;
          while( index>eVal ){
            rai->d_index[index] = 0;
            //instSkipped = instSkipped*( 1+(int)(getReps()->d_type_reps[rai->d_f[0][index].getType()].size()) - index );
            index--;
          }
          rai->d_inst_skipped++;
        }
        if( eVal==-1 ){
          rai->d_index.clear();
        }else if( eVal<(int)rai->d_index.size() ){
          rai->increment2( d_quantEngine, eVal );
          success = false;
        }
      }
    }while( !success );
  }
}

//if evaluate( rai, n, phaseReq ) = eVal,
// if eVal = rai->d_index.size()
//   then the formula n instantiated with rai cannot be proven to be equal to phaseReq
// otherwise,
//   each n{rai->d_index[0]/x_0...rai->d_index[eVal]/x_eVal, */x_(eVal+1) ... */x_n } is equal to phaseReq in the current model
int ModelEngine::evaluate( RepAlphabetIterator* rai, Node n, bool phaseReq ){
  //Debug("fmf-model-eval-debug") << "Evaluate " << n << " " << phaseReq << std::endl;
  EqualityQuery* q = d_quantEngine->getEqualityQuery();
  if( n.getKind()==NOT ){
    return evaluate( rai, n[0], !phaseReq );
  }else if( n.getKind()==OR || n.getKind()==AND || n.getKind()==IMPLIES ){
    //check whether we are in a fortunate case or unfortunate case
    bool followPhase = n.getKind()==AND ? !phaseReq : phaseReq;
    int eVal = followPhase ? (int)rai->d_index.size() : -1;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      //evaluate subterm
      bool newPhaseReq = ( i==0 && n.getKind()==IMPLIES ) ? !phaseReq : phaseReq;
      int eValT = evaluate( rai, n[i], newPhaseReq );
      if( followPhase ){
        if( eValT==-1 ){
          return eValT;
        }else if( eValT<eVal ){
          eVal = eValT;
        }
      }else{
        if( eValT==(int)rai->d_index.size() ){
          return eValT;
        }else if( eValT>eVal ){
          eVal = eValT;
        }
      }
    }
    return eVal;
  }else if( n.getKind()==IFF || n.getKind()==XOR || n.getKind()==ITE || n.getKind()==FORALL ){
    //do nothing
  }else{
    //Debug("fmf-model-eval-debug") << "Evaluate literal " << n << std::endl;
    //this should be a literal
    Node gn = n.substitute( rai->d_ic.begin(), rai->d_ic.end(), rai->d_terms.begin(), rai->d_terms.end() );
    //Debug("fmf-model-eval-debug") << "  Ground version = " << gn << std::endl;
    bool success = false;
    std::vector< Node > fv_deps;
    if( n.getKind()==APPLY_UF ){
      //case for boolean predicates
      Node bn = NodeManager::currentNM()->mkConst( phaseReq );
      success = evaluateEquality( n, bn, gn, bn, true, fv_deps, true );
    }else if( n.getKind()==EQUAL ){
      //case for equality
      success = evaluateEquality( n[0], n[1], gn[0], gn[1], phaseReq, fv_deps, true );
    }
    if( success ){
      int maxIndex = -1;
      for( int i=0; i<(int)fv_deps.size(); i++ ){
        int index = fv_deps[i].getAttribute(InstVarNumAttribute());
        if( index>maxIndex ){
          maxIndex = index;
          if( index==(int)rai->d_index.size()-1 ){
            break;
          }
        }
      }
      Debug("fmf-model-eval-debug") << "Evaluate literal: Success, return eval = " << maxIndex << std::endl;
      return maxIndex;
    }
  }
  return (int)rai->d_index.size();
}

bool ModelEngine::evaluateEquality( Node n1, Node n2, Node gn1, Node gn2, bool phaseReq, std::vector< Node >& fv_deps, bool calc_fv_deps ){
  Debug("fmf-model-eval-debug") << "Evaluate equality: (" << phaseReq << ")" << std::endl;
  Debug("fmf-model-eval-debug") << "   " << n1 << " = " << n2 << std::endl;
  Debug("fmf-model-eval-debug") << "   " << gn1 << " = " << gn2 << std::endl;
  Node val1 = evaluateTerm( n1, gn1, fv_deps, calc_fv_deps );
  Node val2 = evaluateTerm( n2, gn2, fv_deps, calc_fv_deps );
  Debug("fmf-model-eval-debug") << "   Values:  " << val1 << " = " << val2 << std::endl;
  bool success = false;
  if( phaseReq ){
    success = areEqual( val1, val2 );
  }else{
    success = areDisequal( val1, val2 );
  }
  if( success ){
    Debug("fmf-model-eval-debug") << "   --> Success" << std::endl;
    if( calc_fv_deps ){
      Debug("fmf-model-eval-debug") << "       Value depends on variables: ";
      for( int i=0; i<(int)fv_deps.size(); i++ ){
        Debug("fmf-model-eval-debug") << fv_deps[i] << " ";
      }
      Debug("fmf-model-eval-debug") << std::endl;
    }
  }else{
    Debug("fmf-model-eval-debug") << "   --> Failed" << std::endl;
  }
  return success;
}

Node ModelEngine::evaluateTerm( Node n, Node gn, std::vector< Node >& fv_deps, bool calc_fv_deps ){
  if( n.hasAttribute(InstConstantAttribute()) ){
    if( n.getKind()==INST_CONSTANT ){
      if( calc_fv_deps ){
        fv_deps.push_back( n );
      }
      return gn;
    }else{
      //Debug("fmf-model-eval-debug") << "Evaluate term " << n << " (" << gn << ")" << std::endl;
      //first we must evaluate the arguments
      Node val = gn;
      if( n.getKind()==APPLY_UF ){
        int depIndex = 0;
        //consult model for op to find real value
        Node op = gn.getOperator();
        Assert( d_uf_model.find( op )!=d_uf_model.end() );
        //first we must evaluate the arguments
        bool childrenChanged = false;
        std::vector< Node > children;
        children.push_back( op );
        std::map< int, std::vector< Node > > children_var_deps;
        //for each argument, calculate its value, and the variables its value depends upon
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          Node nn = evaluateTerm( n[i], gn[i], children_var_deps[i], calc_fv_deps );
          children.push_back( nn );
          childrenChanged = childrenChanged || nn!=gn[i];
        }
        //remake gn if changed
        if( childrenChanged ){
          gn = NodeManager::currentNM()->mkNode( APPLY_UF, children );
        }
        //now, consult the model
        val = d_uf_model[op].d_tree.getValue( d_quantEngine, gn, depIndex );
        Debug("fmf-model-eval-debug") << "Eval " << gn << " = " << val << ", depIndex = " << depIndex << std::endl;
        if( !val.isNull() && calc_fv_deps ){
          //calculate the free variables that the value depends on : take those in children_var_deps[0...depIndex-1]
          for( std::map< int, std::vector< Node > >::iterator it = children_var_deps.begin(); it != children_var_deps.end(); ++it ){
            if( it->first<depIndex ){
              fv_deps.insert( fv_deps.end(), it->second.begin(), it->second.end() );
            }
          }
        }
      }
      return val;
    }
  }else{
    return n;
  }
}

bool ModelEngine::areEqual( Node a, Node b ){
  return d_quantEngine->getEqualityQuery()->areEqual( a, b );
}

bool ModelEngine::areDisequal( Node a, Node b ){
  return d_quantEngine->getEqualityQuery()->areDisequal( a, b );
}

void ModelEngine::debugPrint( const char* c ){
  Debug( c ) << "---Current Model---" << std::endl;
  Debug( c ) << "Representatives: " << std::endl;
  d_ra.debugPrint( c, d_quantEngine );
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
  Debug( c ) << "Functions: " << std::endl;
  for( std::map< Node, UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.debugPrint( c );
    Debug( c ) << std::endl;
  }
}

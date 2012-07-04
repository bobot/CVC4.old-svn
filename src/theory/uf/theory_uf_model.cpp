/*********************                                                        */
/*! \file theory_uf_model.cpp
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
 ** \brief Implementation of Theory UF Model
 **/

#include "theory/quantifiers/model_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf_instantiator.h"

#define RECONSIDER_FUNC_DEFAULT_VALUE
#define RECONSIDER_FUNC_CONSTANT
#define USE_PARTIAL_DEFAULT_VALUES

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

//clear
void UfModelTree::clear(){
  d_data.clear();
  d_value = Node::null();
}

//set value function
void UfModelTree::setValue( QuantifiersEngine* qe, Node n, Node v, std::vector< int >& indexOrder, bool ground, int argIndex ){
  if( d_data.empty() ){
    d_value = v;
  }else if( !d_value.isNull() && d_value!=v ){
    d_value = Node::null();
  }
  if( argIndex<(int)n.getNumChildren() ){
    //take r = null when argument is the model basis
    Node r;
    if( ground || !n[ indexOrder[argIndex] ].getAttribute(ModelBasisAttribute()) ){
      r = qe->getEqualityQuery()->getRepresentative( n[ indexOrder[argIndex] ] );
    }
    d_data[ r ].setValue( qe, n, v, indexOrder, ground, argIndex+1 );
  }
}

//get value function
Node UfModelTree::getValue( QuantifiersEngine* qe, Node n, std::vector< int >& indexOrder, int& depIndex, int argIndex ){
  if( !d_value.isNull() && isTotal( n.getOperator(), argIndex ) ){
    //Notice() << "Constant, return " << d_value << ", depIndex = " << argIndex << std::endl;
    depIndex = argIndex;
    return d_value;
  }else{
    Node val;
    int childDepIndex[2] = { argIndex, argIndex };
    for( int i=0; i<2; i++ ){
      //first check the argument, then check default
      Node r;
      if( i==0 ){
        r = qe->getEqualityQuery()->getRepresentative( n[ indexOrder[argIndex] ] );
      }
      std::map< Node, UfModelTree >::iterator it = d_data.find( r );
      if( it!=d_data.end() ){
        val = it->second.getValue( qe, n, indexOrder, childDepIndex[i], argIndex+1 );
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
    //Notice() << "Return " << val << ", depIndex = " << depIndex;
    //Notice() << " ( " << childDepIndex[0] << ", " << childDepIndex[1] << " )" << std::endl;
    return val;
  }
}

//simplify function
void UfModelTree::simplify( Node op, Node defaultVal, int argIndex ){
  if( argIndex<(int)op.getType().getNumChildren()-1 ){
    std::vector< Node > eraseData;
    //first process the default argument
    Node r;
    std::map< Node, UfModelTree >::iterator it = d_data.find( r );
    if( it!=d_data.end() ){
      if( !defaultVal.isNull() && it->second.d_value==defaultVal ){
        eraseData.push_back( r );
      }else{
        it->second.simplify( op, defaultVal, argIndex+1 );
        if( !it->second.d_value.isNull() && it->second.isTotal( op, argIndex+1 ) ){
          defaultVal = it->second.d_value;
        }else{
          defaultVal = Node::null();
          if( it->second.isEmpty() ){
            eraseData.push_back( r );
          }
        }
      }
    }
    //now see if any children can be removed, and simplify the ones that cannot
    for( std::map< Node, UfModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( !it->first.isNull() ){
        if( !defaultVal.isNull() && it->second.d_value==defaultVal ){
          eraseData.push_back( it->first );
        }else{
          it->second.simplify( op, defaultVal, argIndex+1 );
          if( it->second.isEmpty() ){
            eraseData.push_back( it->first );
          }
        }
      }
    }
    for( int i=0; i<(int)eraseData.size(); i++ ){
      d_data.erase( eraseData[i] );
    }
  }
}

//is total function
bool UfModelTree::isTotal( Node op, int argIndex ){
  if( argIndex==(int)(op.getType().getNumChildren()-1) ){
    return !d_value.isNull();
  }else{
    Node r;
    std::map< Node, UfModelTree >::iterator it = d_data.find( r );
    if( it!=d_data.end() ){
      return it->second.isTotal( op, argIndex+1 );
    }else{
      return false;
    }
  }
}

Node UfModelTree::getConstantValue( QuantifiersEngine* qe, Node n, std::vector< int >& indexOrder, int argIndex ){
  return d_value;
}

void indent( const char* c, int ind ){
  for( int i=0; i<ind; i++ ){
    Debug( c ) << " ";
  }
}

void UfModelTree::debugPrint( const char* c, QuantifiersEngine* qe, std::vector< int >& indexOrder, int ind, int arg ){
  if( !d_data.empty() ){
    for( std::map< Node, UfModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( !it->first.isNull() ){
        indent( c, ind );
        Debug( c ) << "if x_" << indexOrder[arg] << " == " << it->first << std::endl;
        it->second.debugPrint( c, qe, indexOrder, ind+2, arg+1 );
      }
    }
    if( d_data.find( Node::null() )!=d_data.end() ){
      d_data[ Node::null() ].debugPrint( c, qe, indexOrder, ind, arg+1 );
    }
  }else{
    indent( c, ind );
    Debug( c ) << "return ";
    Model::printRepresentative( c, qe, d_value );
    //Debug( c ) << " { ";
    //for( int i=0; i<(int)d_explicit.size(); i++ ){
    //  Debug( c ) << d_explicit[i] << " ";
    //}
    //Debug( c ) << "}";
    Debug( c ) << std::endl;
  }
}

UfModel::UfModel( Node op, quantifiers::ModelEngine* me ) : d_op( op ), d_me( me ),
  d_model_constructed( false ), d_reconsider_model( false ){
  d_tree = UfModelTreeOrdered( op );
  TypeNode tn = d_op.getType();
  tn = tn[(int)tn.getNumChildren()-1];
  Assert( tn==NodeManager::currentNM()->booleanType() || uf::StrongSolverTheoryUf::isRelevantType( tn ) );
  //look at ground assertions
  for( int i=0; i<(int)d_me->getQuantifiersEngine()->getTermDatabase()->d_op_map[ d_op ].size(); i++ ){
    Node n = d_me->getQuantifiersEngine()->getTermDatabase()->d_op_map[ d_op ][i];
    computeModelBasisArgAttribute( n );
    if( !n.getAttribute(NoMatchAttribute()) || n.getAttribute(ModelBasisArgAttribute())==1 ){
      Node r = d_me->getQuantifiersEngine()->getEqualityQuery()->getRepresentative( n );
      d_ground_asserts_reps.push_back( r );
      d_ground_asserts.push_back( n );
    }
  }
  //determine if it is constant
  if( !d_ground_asserts.empty() ){
    bool isConstant = true;
    for( int i=1; i<(int)d_ground_asserts.size(); i++ ){
      if( d_ground_asserts_reps[0]!=d_ground_asserts_reps[i] ){
        isConstant = false;
        break;
      }
    }
    if( isConstant ){
      //set constant value
      Node t = d_me->getModelBasisOpTerm( d_op );
      Node r = d_ground_asserts_reps[0];
      setValue( t, r, false );
      setModel();
      d_reconsider_model = true;
      Debug("fmf-model-cons") << "Function " << d_op << " is the constant function ";
      Model::printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), r );
      Debug("fmf-model-cons") << std::endl;
    }
  }
}

void UfModel::computeModelBasisArgAttribute( Node n ){
  if( !n.hasAttribute(ModelBasisArgAttribute()) ){
    uint64_t val = 0;
    //determine if it has model basis attribute
    for( int j=0; j<(int)n.getNumChildren(); j++ ){
      if( n[j].getAttribute(ModelBasisAttribute()) ){
        val = 1;
        break;
      }
    }
    ModelBasisArgAttribute mbaa;
    n.setAttribute( mbaa, val );
  }
}

Node UfModel::getIntersection( Node n1, Node n2, bool& isGround ){
  //Notice() << "Get intersection " << n1 << " " << n2 << std::endl;
  isGround = true;
  std::vector< Node > children;
  children.push_back( n1.getOperator() );
  for( int i=0; i<(int)n1.getNumChildren(); i++ ){
    if( n1[i]==n2[i] ){
      if( n1[i].getAttribute(ModelBasisAttribute()) ){
        isGround = false;
      }
      children.push_back( n1[i] );
    }else if( n1[i].getAttribute(ModelBasisAttribute()) ){
      children.push_back( n2[i] );
    }else if( n2[i].getAttribute(ModelBasisAttribute()) ){
      children.push_back( n1[i] );
    }else if( d_me->areEqual( n1[i], n2[i] ) ){
      children.push_back( n1[i] );
    }else{
      return Node::null();
    }
  }
  return NodeManager::currentNM()->mkNode( APPLY_UF, children );
}

void UfModel::setValue( Node n, Node v, bool ground, bool isReq ){
  Assert( !n.isNull() );
  Assert( !v.isNull() );
  d_set_values[ isReq ? 1 : 0 ][ ground ? 1 : 0 ][n] = v;
#ifdef USE_PARTIAL_DEFAULT_VALUES
  if( !ground ){
    int defSize = (int)d_defaults.size();
    for( int i=0; i<defSize; i++ ){
      bool isGround;
      //for soundness, to allow variable order-independent function interpretations,
      //  we must ensure that the intersection of all default terms
      //  is also defined.
      //for example, if we have that f( e, a ) = a, and f( b, e ) = b,
      //  then we must define f( a, b ).
      Node ni = getIntersection( n, d_defaults[i], isGround );
      if( !ni.isNull() ){
        //if the intersection exists, and is not already defined
        if( d_set_values[0][ isGround ? 1 : 0 ].find( ni )==d_set_values[0][ isGround ? 1 : 0 ].end() &&
            d_set_values[1][ isGround ? 1 : 0 ].find( ni )==d_set_values[1][ isGround ? 1 : 0 ].end() ){
          //use the current value
          setValue( ni, v, isGround, false );
        }
      }
    }
    d_defaults.push_back( n );
  }
  if( isReq && d_set_values[0][ ground ? 1 : 0 ].find( n )!=d_set_values[0][ ground ? 1 : 0 ].end()){
    d_set_values[0][ ground ? 1 : 0 ].erase( n );
  }
#endif
  if( d_me->optUseRelevantDomain() ){
    int raIndex = d_me->getReps()->getIndexFor( v );
    Assert( raIndex!=-1 );
    if( std::find( d_active_range.begin(), d_active_range.end(), raIndex )==d_active_range.end() ){
      d_active_range.push_back( raIndex );
    }
  }
}

void UfModel::setModel(){
  makeModel( d_me->getQuantifiersEngine(), d_tree );
  d_model_constructed = true;
}

void UfModel::clearModel(){
  for( int j=0; j<2; j++ ){
    for( int k=0; k<2; k++ ){
      d_set_values[j][k].clear();
    }
  }
  d_tree.clear();
  d_model_constructed = false;
  d_active_range.clear();
}

Node UfModel::getConstantValue( QuantifiersEngine* qe, Node n ){
  if( d_model_constructed ){
    return d_tree.getConstantValue( qe, n );
  }else{
    return Node::null();
  }
}

bool UfModel::isConstant(){
  Node gn = d_me->getModelBasisOpTerm( d_op );
  Node n = getConstantValue( d_me->getQuantifiersEngine(), gn );
  return !n.isNull();
}

void UfModel::buildModel(){
#ifdef RECONSIDER_FUNC_CONSTANT
  if( d_model_constructed ){
    if( d_reconsider_model ){
      //if we are allowed to reconsider default value, then see if the default value can be improved
      Node t = d_me->getModelBasisOpTerm( d_op );
      Node v = d_set_values[1][0][t];
      if( d_value_pro_con[0][v].empty() ){
        Debug("fmf-model-cons-debug") << "Consider changing the default value for " << d_op << std::endl;
        clearModel();
      }
    }
  }
#endif
  if( !d_model_constructed ){
    //construct the model for the uninterpretted function/predicate
    bool setDefaultVal = true;
    Node defaultTerm = d_me->getModelBasisOpTerm( d_op );
    Debug("fmf-model-cons") << "Construct model for " << d_op << "..." << std::endl;
    //set the values in the model
    for( int i=0; i<(int)d_ground_asserts.size(); i++ ){
      Node n = d_ground_asserts[i];
      Node v = d_ground_asserts_reps[i];
      //if this assertion did not help the model, just consider it ground
      //set n = v in the model tree
      Debug("fmf-model-cons") << "  Set " << n << " = ";
      Model::printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), v );
      Debug("fmf-model-cons") << std::endl;
      //set it as ground value
      setValue( n, v );
#ifdef USE_PARTIAL_DEFAULT_VALUES
      //also set as default value if necessary
      //if( n.getAttribute(ModelBasisArgAttribute())==1 && !d_term_pro_con[0][n].empty() ){
      if( n.getAttribute(ModelBasisArgAttribute())==1 ){
        setValue( n, v, false );
        if( n==defaultTerm ){
          //incidentally already set, we will not need to find a default value
          setDefaultVal = false;
        }
      }
#else
      if( n==defaultTerm ){
        setValue( n, v, false );
        //incidentally already set, we will not need to find a default value
        setDefaultVal = false;
      }
#endif
    }
    //set the overall default value if not set already  (is this necessary??)
    if( setDefaultVal ){
      Debug("fmf-model-cons") << "  Choose default value..." << std::endl;
      //chose defaultVal based on heuristic (the best ratio of "pro" responses)
      Node defaultVal;
      double maxScore = -1;
      for( int i=0; i<(int)d_values.size(); i++ ){
        Node v = d_values[i];
        double score = ( 1.0 + (double)d_value_pro_con[0][v].size() )/( 1.0 + (double)d_value_pro_con[1][v].size() );
        Debug("fmf-model-cons") << "  - score( ";
        Model::printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), v );
        Debug("fmf-model-cons") << " ) = " << score << std::endl;
        if( score>maxScore ){
          defaultVal = v;
          maxScore = score;
        }
      }
#ifdef RECONSIDER_FUNC_DEFAULT_VALUE
      if( maxScore<1.0 ){
        //consider finding another value, if possible
        Debug("fmf-model-cons-debug") << "Poor choice for default value, score = " << maxScore << std::endl;
        TypeNode tn = d_op.getType();
        Node newDefaultVal = d_me->getArbitraryElement( tn[(int)tn.getNumChildren()-1], d_values );
        if( !newDefaultVal.isNull() ){
          defaultVal = newDefaultVal;
          Debug("fmf-model-cons-debug") << "-> Change default value to ";
          Model::printRepresentative( "fmf-model-cons-debug", d_me->getQuantifiersEngine(), defaultVal );
          Debug("fmf-model-cons-debug") << std::endl;
        }else{
          Debug("fmf-model-cons-debug") << "-> Could not find arbitrary element of type " << tn[(int)tn.getNumChildren()-1] << std::endl;
          Debug("fmf-model-cons-debug") << "      Excluding: ";
          for( int i=0; i<(int)d_values.size(); i++ ){
            Debug("fmf-model-cons-debug") << d_values[i] << " ";
          }
          Debug("fmf-model-cons-debug") << std::endl;
        }
      }
#endif
      Assert( !defaultVal.isNull() );
      //get the default term (this term must be defined non-ground in model)
      Debug("fmf-model-cons") << "  Choose ";
      Model::printRepresentative("fmf-model-cons", d_me->getQuantifiersEngine(), defaultVal );
      Debug("fmf-model-cons") << " as default value (" << defaultTerm << ")" << std::endl;
      Debug("fmf-model-cons") << "     # quantifiers pro = " << d_value_pro_con[0][defaultVal].size() << std::endl;
      Debug("fmf-model-cons") << "     # quantifiers con = " << d_value_pro_con[1][defaultVal].size() << std::endl;
      setValue( defaultTerm, defaultVal, false );
    }
    Debug("fmf-model-cons") << "  Making model...";
    setModel();
    Debug("fmf-model-cons") << "  Finished constructing model for " << d_op << "." << std::endl;
    //Notice() << "  Finished constructing model for " << d_op << "." << std::endl;

    //for debugging, make sure model satisfies all ground assertions
    for( int i=0; i<(int)d_ground_asserts.size(); i++ ){
      int depIndex;
      Node n = d_tree.getValue( d_me->getQuantifiersEngine(), d_ground_asserts[i], depIndex );
      if( n!=d_ground_asserts_reps[i] ){
        Debug("fmf-bad") << "Bad model : " << d_ground_asserts[i] << " := ";
        Model::printRepresentative("fmf-bad", d_me->getQuantifiersEngine(), n );
        Debug("fmf-bad") << " != ";
        Model::printRepresentative("fmf-bad", d_me->getQuantifiersEngine(), d_ground_asserts_reps[i] );
        Debug("fmf-bad") << std::endl;
      }
    }
  }
}

void UfModel::setValuePreference( Node f, Node n, bool isPro ){
  Node v = d_me->getQuantifiersEngine()->getEqualityQuery()->getRepresentative( n );
  if( std::find( d_values.begin(), d_values.end(), v )==d_values.end() ){
    d_values.push_back( v );
  }
  int index = isPro ? 0 : 1;
  if( std::find( d_value_pro_con[index][v].begin(), d_value_pro_con[index][v].end(), f )==d_value_pro_con[index][v].end() ){
    d_value_pro_con[index][v].push_back( f );
  }
  d_term_pro_con[index][n].push_back( f );
}

void UfModel::makeModel( QuantifiersEngine* qe, UfModelTreeOrdered& tree ){
  for( int j=0; j<2; j++ ){
    for( int k=0; k<2; k++ ){
      for( std::map< Node, Node >::iterator it = d_set_values[j][k].begin(); it != d_set_values[j][k].end(); ++it ){
        tree.setValue( qe, it->first, it->second, k==1 );
      }
    }
  }
  tree.simplify();
}

void UfModel::computeRelevantDomain(){
  for( int i=0; i<(int)d_ground_asserts.size(); i++ ){
    Node n = d_ground_asserts[i];
    //add arguments to domain
    for( int j=0; j<(int)n.getNumChildren(); j++ ){
      if( d_me->getReps()->hasType( n[j].getType() ) ){
        Node ra = d_me->getQuantifiersEngine()->getEqualityQuery()->getRepresentative( n[j] );
        int raIndex = d_me->getReps()->getIndexFor( ra );
        Assert( raIndex!=-1 );
        if( std::find( d_active_domain[j].begin(), d_active_domain[j].end(), raIndex )==d_active_domain[j].end() ){
          d_active_domain[j].push_back( raIndex );
        }
      }
    }
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
  //Debug( c ) << "   Phase reqs:" << std::endl;  //for( int i=0; i<2; i++ ){
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

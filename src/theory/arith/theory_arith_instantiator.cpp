/*********************                                                        */
/*! \file instantiator_arith_instantiator.cpp
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
 ** \brief Implementation of instantiator_arith_instantiator class
 **/

#include "theory/arith/theory_arith_instantiator.h"
#include "theory/arith/theory_arith.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

#define ARITH_INSTANTIATOR_USE_DELTA
#define ARITH_INSTANTIATOR_STRONG_DELTA_LEMMA

InstantiatorTheoryArith::InstantiatorTheoryArith(context::Context* c, InstantiationEngine* ie, Theory* th) :
Instantiator( c, ie, th ){

}

void InstantiatorTheoryArith::check( Node assertion ){
  Debug("quant-arith-assert") << "InstantiatorTheoryArith::check: " << assertion << std::endl;
}

void InstantiatorTheoryArith::resetInstantiation(){
  d_instRows.clear();
  d_tableaux_term.clear();
  d_tableaux.clear();
  d_ceTableaux.clear();
  //search for instantiation rows in simplex tableaux
  ArithVarToNodeMap avtnm = ((TheoryArith*)getTheory())->d_arithvarNodeMap.getArithVarToNodeMap();
  for( ArithVarToNodeMap::iterator it = avtnm.begin(); it != avtnm.end(); ++it ){
    ArithVar x = (*it).first;
    if( ((TheoryArith*)getTheory())->d_partialModel.hasEitherBound( x ) ){
      Node n = (*it).second;
      Node f;
      NodeBuilder<> t(kind::PLUS);
      if( n.getKind()==PLUS ){
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          addTermToRow( x, n[i], f, t );
        }
      }else{
        addTermToRow( x, n, f, t );
      }
      if( f!=Node::null() ){
        d_instRows[f].push_back( x );
        //this theory has constraints from f
        setHasConstraintsFrom( f );
        //set tableaux term
        if( t.getNumChildren()==0 ){
          d_tableaux_term[x] = NodeManager::currentNM()->mkConst( Rational(0) ); 
        }else if( t.getNumChildren()==1 ){
          d_tableaux_term[x] = t.getChild( 0 );
        }else{
          d_tableaux_term[x] = t;
        }
      }
    }
  }
  //print debug
  debugPrint( "quant-arith-debug" );
}

void InstantiatorTheoryArith::addTermToRow( ArithVar x, Node n, Node& f, NodeBuilder<>& t ){
  if( n.getKind()==MULT ){
    if( n[1].hasAttribute(InstConstantAttribute()) ){
      if( n[1].getKind()==INST_CONSTANT ){
        f = n[1].getAttribute(InstConstantAttribute());
        d_ceTableaux[x][ n[1] ] = n[0];
      }else{
        d_tableaux_ce_term[x][ n[1] ] = n[0];
      }
    }else{
      d_tableaux[x][ n[1] ] = n[0];
      t << n;
    }
  }else{
    if( n.hasAttribute(InstConstantAttribute()) ){
      if( n.getKind()==INST_CONSTANT ){
        f = n.getAttribute(InstConstantAttribute());
        d_ceTableaux[x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      }else{
        d_tableaux_ce_term[x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      }
    }else{
      d_tableaux[x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      t << n;
    }
  }
}

void InstantiatorTheoryArith::debugPrint( const char* c ){
  ArithVarToNodeMap avtnm = ((TheoryArith*)getTheory())->d_arithvarNodeMap.getArithVarToNodeMap();
  for( ArithVarToNodeMap::iterator it = avtnm.begin(); it != avtnm.end(); ++it ){
    ArithVar x = (*it).first;
    Node n = (*it).second;
    if( ((TheoryArith*)getTheory())->d_partialModel.hasEitherBound( x ) ){
      Debug(c) << x << " : " << n << ", bounds = ";
      if( ((TheoryArith*)getTheory())->d_partialModel.hasLowerBound( x ) ){
        Debug(c) << ((TheoryArith*)getTheory())->d_partialModel.getLowerBound( x );
      }else{
        Debug(c) << "-infty";
      }
      Debug(c) << " <= ";
      Debug(c) << ((TheoryArith*)getTheory())->d_partialModel.getAssignment( x );
      Debug(c) << " <= ";
      if( ((TheoryArith*)getTheory())->d_partialModel.hasUpperBound( x ) ){
        Debug(c) << ((TheoryArith*)getTheory())->d_partialModel.getUpperBound( x );
      }else{
        Debug(c) << "+infty";
      }
      Debug(c) << std::endl;
      //Debug(c) << "   Term = " << d_tableaux_term[x] << std::endl;
      //Debug(c) << "   ";
      //for( std::map< Node, Node >::iterator it2 = d_tableaux[x].begin(); it2 != d_tableaux[x].end(); ++it2 ){
      //  Debug(c) << "( " << it2->first << ", " << it2->second << " ) ";
      //}
      //for( std::map< Node, Node >::iterator it2 = d_ceTableaux[x].begin(); it2 != d_ceTableaux[x].end(); ++it2 ){
      //  Debug(c) << "(CE)( " << it2->first << ", " << it2->second << " ) ";
      //}
      //Debug(c) << std::endl;
    }
  }

  for( std::map< Node, std::vector< Node > >::iterator it = d_instEngine->d_inst_constants.begin(); 
        it != d_instEngine->d_inst_constants.end(); ++it ){
    Node f = it->first;
    Debug(c) << f << std::endl;
    Debug(c) << "   Inst constants: ";
    for( int i=0; i<(int)it->second.size(); i++ ){
      if( i>0 ){
        Debug(c) << ", ";
      }
      Debug(c) << it->second[i];
    }
    Debug(c) << std::endl;
    Debug(c) << "   Instantiation rows: ";
    for( int i=0; i<(int)d_instRows[f].size(); i++ ){
      if( i>0 ){
        Debug(c) << ", ";
      }
      Debug(c) << d_instRows[f][i];
    }
    Debug(c) << std::endl;
  }
}

void InstantiatorTheoryArith::process( Node f, int effort ){
  Debug("quant-arith") << "Arith: Try to solve (" << effort << ") for " << f << "... " << std::endl;
  if( effort>1 ){
    d_quantStatus = STATUS_UNKNOWN;
  }else if( effort==0 ){

  }else{
    ArithVarToNodeMap avtnm = ((TheoryArith*)getTheory())->d_arithvarNodeMap.getArithVarToNodeMap();
    for( int j=0; j<(int)d_instRows[f].size(); j++ ){
      ArithVar x = d_instRows[f][j];
      Debug("quant-arith") << "Process instantiation row " << avtnm[x] << "..." << std::endl;
      Assert( !d_ceTableaux[x].empty() );
      DeltaRational dr = ((TheoryArith*)getTheory())->d_partialModel.getAssignment( x );
      Node beta = NodeManager::currentNM()->mkConst( dr.getNoninfinitesimalPart() );
#ifdef ARITH_INSTANTIATOR_USE_DELTA
      if( dr.getInfinitesimalPart()!=0 ){
        Node delta = NodeManager::currentNM()->mkNode( MULT, getDelta( d_ceTableaux[x].begin()->first ),
                                                        NodeManager::currentNM()->mkConst( dr.getInfinitesimalPart() ) );
        beta = NodeManager::currentNM()->mkNode( PLUS, beta, delta );
      }
#endif

      //instantiation row will be A*e + B*t + C*t[e] = beta,
      // where e is a vector of instantiation variables, 
      // t is vector of terms, and t[e] is a vector of terms containing instantiation constants.
      // Say one instantiation constant in e is coeff*e_i.
      // We construct the term ( beta - (B*t + C*beta(t[e]))/coeff to use for e_i,
      // where beta(t[e]) is the vector of constants by replacing each term with its current model.
      Node term;
      if( d_tableaux_ce_term[x].empty() ){
        term = d_tableaux_term[x];
      }else{
        NodeBuilder<> plus_term(kind::PLUS);
        plus_term << d_tableaux_term[x];
        for( std::map< Node, Node >::iterator it = d_tableaux_ce_term[x].begin(); it != d_tableaux_ce_term[x].end(); ++it ){
          ArithVar v = ((TheoryArith*)getTheory())->d_arithvarNodeMap.asArithVar( it->first );
          DeltaRational drv = ((TheoryArith*)getTheory())->d_partialModel.getAssignment( v );
          Node val = NodeManager::currentNM()->mkConst( drv.getNoninfinitesimalPart() );
#ifdef ARITH_INSTANTIATOR_USE_DELTA
          if( drv.getInfinitesimalPart()!=0 ){
            Node delta = NodeManager::currentNM()->mkNode( MULT, getDelta( d_ceTableaux[x].begin()->first ),
                                                            NodeManager::currentNM()->mkConst( drv.getInfinitesimalPart() ) );
            val = NodeManager::currentNM()->mkNode( PLUS, val, delta );
          } 
#endif
          plus_term << NodeManager::currentNM()->mkNode( MULT, it->second, val );
        }
        term = plus_term;
      }
      Node instVal = NodeManager::currentNM()->mkNode( MINUS, beta, term );
      Rational value(1);
      Node coeff = NodeManager::currentNM()->mkConst( value / d_ceTableaux[x].begin()->second.getConst<Rational>() );
      instVal = NodeManager::currentNM()->mkNode( MULT, coeff, instVal );
      instVal = Rewriter::rewrite( instVal );
      Debug("quant-arith") << "   Suggest " << instVal << " for " << d_ceTableaux[x].begin()->first << std::endl;
      InstMatch m( f, d_instEngine );
      //for( int k=0; k<(int)d_instEngine->d_inst_constants[f].size(); k++ ){
      //  if( d_instEngine->d_inst_constants[f][k].getType()==NodeManager::currentNM()->integerType() ||
      //     d_instEngine->d_inst_constants[f][k].getType()==NodeManager::currentNM()->realType() ){
      //    Rational z(0);
      //    m.setMatch( d_instEngine->d_inst_constants[f][k], NodeManager::currentNM()->mkConst( z ) );
      //  }
      //}
      m.setMatch( d_ceTableaux[x].begin()->first, instVal );
      d_instEngine->addInstantiation( &m );
    }
  }
}

Node InstantiatorTheoryArith::getDelta( Node n ){
  std::map< TypeNode, Node >::iterator it = d_deltas.find( n.getType() );
  if( it==d_deltas.end() ){
    Node delta = NodeManager::currentNM()->mkVar( n.getType() ); 
    d_deltas[ n.getType() ] = delta;
    Node gt = NodeManager::currentNM()->mkNode( GT, delta, NodeManager::currentNM()->mkConst( Rational(0) ) ); 
    //add split
#ifdef ARITH_INSTANTIATOR_STRONG_DELTA_LEMMA
    d_instEngine->addLemma( gt );
#else
    gt = Rewriter::rewrite( gt );
    d_instEngine->addSplit( gt );
    d_instEngine->d_curr_out->requirePhase( gt, true );
#endif
    return delta;
  }
  return it->second;
}

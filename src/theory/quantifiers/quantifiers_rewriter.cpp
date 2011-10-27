/*********************                                                        */
/*! \file theory_quantifiers_rewriter.cpp
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
 ** \brief Implementation of QuantifiersRewriter class
 **/

#include "theory/quantifiers/quantifiers_rewriter.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

bool QuantifiersRewriter::isClause( Node n ){
  if( isLiteral( n ) ){
    return true;
  }else if( n.getKind()==OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isClause( n[i] ) ){
        return false;
      }
    }
    return true;
  }else if( n.getKind()==IMPLIES ){
    return isCube( n[0] ) && isClause( n[1] );
  }else{
    return false;
  }
}

bool QuantifiersRewriter::isLiteral( Node n ){
  switch( n.getKind() ){
  case NOT:
    return isLiteral( n[0] );
    break;
  case OR:
  case AND:
  case IMPLIES:
  case XOR:
  case ITE:
  case IFF:
    return false;
    break;
  case EQUAL:
    return n[0].getType()!=NodeManager::currentNM()->booleanType();
    break;
  default:
    break;
  }
  return true;
}

bool QuantifiersRewriter::isCube( Node n ){
  if( isLiteral( n ) ){
    return true;
  }else if( n.getKind()==AND ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isCube( n[i] ) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

void QuantifiersRewriter::computeArgs( std::map< Node, bool >& active, Node n ){
  if( active.find( n )!=active.end() ){
    active[n] = true;
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeArgs( active, n[i] );
    }
  }
}

void QuantifiersRewriter::computeArgs( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n ){
  std::map< Node, bool > active;
  for( int i=0; i<(int)args.size(); i++ ){
    active[ args[i] ] = false;
  }
  computeArgs( active, n );
  activeArgs.clear();
  for( std::map< Node, bool >::iterator it = active.begin(); it != active.end(); ++it ){
    if( it->second ){ //only add bound variables that occur in body
      activeArgs.push_back( it->first );
    }
  }
}

Node QuantifiersRewriter::mkForAll( std::vector< Node >& args, Node n ){
  std::vector< Node > children;
  computeArgs( args, children, n );
  children.push_back( n );
  return NodeManager::currentNM()->mkNode(kind::FORALL, children );
}

void QuantifiersRewriter::setNestedQuantifiers( Node n, Node q ){
  if( n.getKind()==FORALL || n.getKind()==EXISTS ){
    NestedQuantAttribute nqai;
    n.setAttribute(nqai,q);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setNestedQuantifiers( n[i], q );
  }
}

Node QuantifiersRewriter::rewriteQuant( std::vector< Node >& args, Node body, NodeBuilder<>& nb ){
  //std::cout << "do rewrite " << body << std::endl;
  if( isLiteral( body ) ){
    return body;
  }else if( body.getKind()==NOT ){
    Node n = rewriteQuant( args, body[0], nb );
    return n.notNode();
  }else{
    //recurse on subterms
    NodeBuilder<> t( body.getKind() );
    for( int i=0; i<(int)body.getNumChildren(); i++ ){
      t << rewriteQuant( args, body[i], nb );
    }
    Node tn = t;

    //make a boolean predicate representing this term
    std::vector< Node > activeArgs;
    computeArgs( args, activeArgs, tn );
    std::vector< TypeNode > argTypes;
    for( int i=0; i<(int)activeArgs.size(); i++ ){
      argTypes.push_back( activeArgs[i].getType() );
    }
    TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, NodeManager::currentNM()->booleanType() );
    Node op = NodeManager::currentNM()->mkVar( typ );
    std::vector< Node > retArgs;
    retArgs.push_back( op );
    retArgs.insert( retArgs.end(), activeArgs.begin(), activeArgs.end() );
    Node retVal = NodeManager::currentNM()->mkNode( APPLY_UF, retArgs );

    //add quantifier definitions for retVal
    switch( tn.getKind() ){
    case OR:
    {
      NodeBuilder<> bodTot( kind::OR );
      for( int i=0; i<(int)tn.getNumChildren(); i++ ){
        NodeBuilder<> bod( kind::OR );
        bod << tn[i].notNode();
        bod << retVal;
        Node n = bod;
        activeArgs.push_back( n );
        nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
        activeArgs.pop_back();
        bodTot << tn[i];
      }
      bodTot << retVal.notNode();
      Node n = bodTot;
      activeArgs.push_back( n );
      nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
      activeArgs.pop_back();
    }
      break;
    case AND:
    {
      NodeBuilder<> bodTot( kind::OR );
      for( int i=0; i<(int)tn.getNumChildren(); i++ ){
        NodeBuilder<> bod( kind::OR );
        bod << tn[i];
        bod << retVal.notNode();
        Node n = bod;
        activeArgs.push_back( n );
        nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
        activeArgs.pop_back();
        bodTot << tn[i].notNode();
      }
      bodTot << retVal;
      Node n = bodTot;
      activeArgs.push_back( n );
      nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
      activeArgs.pop_back();
    }
      break;
    case IMPLIES:
    {

    }
      break;
    case EQUAL:
    case IFF:
    {
      for( int i=0; i<4; i++ ){
        NodeBuilder<> bod( kind::OR );
        bod << ( ( i==0 || i==3 ) ? retVal.notNode() : retVal );
        bod << ( i%2==0 ? tn[0] : tn[0].notNode() );
        bod << ( i>=2 ? tn[1] : tn[1].notNode() );
        Node n = bod;
        activeArgs.push_back( n );
        nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
        activeArgs.pop_back();
      }
    }
      break;
    case XOR:
      
      break;
    case ITE:
      
      break;
    default:
      break;
    }
    return retVal;
  }
}

Node QuantifiersRewriter::rewriteQuant( std::vector< Node >& args, Node body, bool isExists ){
  //std::cout << "rewrite quant " << body << std::endl;
  if( isExists ){
    Node retVal = rewriteQuant( args, body.notNode() );
    return retVal.notNode();
  }else{
    //push down not node
    if( body.getKind()==NOT ){
      if( body[0].getKind()==NOT ){
        return rewriteQuant( args, body[0][0] );
      }else if( body[0].getKind()==OR ){
        NodeBuilder<> t(kind::AND);
        for( int i=0; i<(int)body.getNumChildren(); i++ ){
          t << rewriteQuant( args, body[i].notNode() );
        }
        Node retVal = t;
        return t;
      }
    }else if( body.getKind()==FORALL ){
      //combine arguments
      std::vector< Node > newArgs;
      for( int i=0; i<(int)( body.getNumChildren()-1 ); i++ ){
        newArgs.push_back( body[i] );
      }
      newArgs.insert( newArgs.end(), args.begin(), args.end() );
      return mkForAll( newArgs, body[ body.getNumChildren()-1 ] );
    }else if( body.getKind()==AND ){
      NodeBuilder<> t(kind::AND);
      for( int i=0; i<(int)body.getNumChildren(); i++ ){
        t << rewriteQuant( args, body[i], isExists );
      }
      Node retVal = t;
      return t;
    }else if( isClause( body ) ){
      return mkForAll( args, body );
    }
  }
  NodeBuilder<> nb(kind::AND);
  Node n = rewriteQuant( args, body, nb );
  nb << mkForAll( args, n );
  Node retVal = nb.getNumChildren()==1 ? nb.getChild( 0 ) : nb;
  return retVal;
}

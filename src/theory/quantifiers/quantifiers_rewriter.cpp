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

//#define QUANTIFIERS_REWRITE_SPLIT_AND
//#define QUANTIFIERS_REWRITE_SPLIT_AND_EXTENSIONS
#define QUANTIFIERS_REWRITE_PUSH_OUT_GROUND_SUBFORMULAS

bool QuantifiersRewriter::isClause( Node n ){
  if( isLiteral( n ) ){
    return true;
  }else if( n.getKind()==NOT ){
    return isCube( n[0] );
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
  }else if( n.getKind()==NOT ){
    return isClause( n[0] );
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

Node QuantifiersRewriter::mkForAll( std::vector< Node >& args, Node n, Node ipl ){
  std::vector< Node > children;
  computeArgs( args, children, n );
  //std::cout << n << " " << args.size() << ", arguments = " << children.size() << std::endl;
  if( children.empty() ){
    return n;
  }else{
    std::vector< Node > args;
    args.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, children ) );
    args.push_back( n );
    if( !ipl.isNull() ){
      //must determine patterns that we can use
      args.push_back( ipl );
    }
    return NodeManager::currentNM()->mkNode(kind::FORALL, args );
  }
}

bool QuantifiersRewriter::hasArg( std::vector< Node >& args, Node n ){
  if( std::find( args.begin(), args.end(), n )!=args.end() ){
    return true;
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( hasArg( args, n[i] ) ){
        return true;
      }
    }
    return false;
  }
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

//Node QuantifiersRewriter::mkPredicate( std::vector< Node >& args, Node body, NodeBuilder<>& defs ){
  //std::cout << "do rewrite " << body << std::endl;
  //if( isLiteral( body ) ){
  //  return body;
  //}else{
  //  //make a boolean predicate representing this term
  //  std::vector< Node > activeArgs;
  //  computeArgs( args, activeArgs, body );
  //  std::vector< TypeNode > argTypes;
  //  for( int i=0; i<(int)activeArgs.size(); i++ ){
  //    argTypes.push_back( activeArgs[i].getType() );
  //  }
  //  TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, NodeManager::currentNM()->booleanType() );
  //  Node op = NodeManager::currentNM()->mkVar( typ );
  //  std::vector< Node > retArgs;
  //  retArgs.push_back( op );
  //  retArgs.insert( retArgs.end(), activeArgs.begin(), activeArgs.end() );
  //  Node retVal = NodeManager::currentNM()->mkNode( APPLY_UF, retArgs );
  //  
  //  Node n = NodeManager::currentNM()->mkNode(EQUAL, retVal, body );
  //  defs << rewriteQuant( activeArgs, n, defs, isNested );

    ////add quantifier definitions for retVal
    //switch( tn.getKind() ){
    //case OR:
    //{
    //  NodeBuilder<> bodTot( kind::OR );
    //  for( int i=0; i<(int)tn.getNumChildren(); i++ ){
    //    NodeBuilder<> bod( kind::OR );
    //    bod << tn[i].notNode();
    //    bod << retVal;
    //    Node n = bod;
    //    activeArgs.push_back( n );
    //    nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
    //    activeArgs.pop_back();
    //    bodTot << tn[i];
    //  }
    //  bodTot << retVal.notNode();
    //  Node n = bodTot;
    //  activeArgs.push_back( n );
    //  nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
    //  activeArgs.pop_back();
    //}
    //  break;
    //case AND:
    //{
    //  NodeBuilder<> bodTot( kind::OR );
    //  for( int i=0; i<(int)tn.getNumChildren(); i++ ){
    //    NodeBuilder<> bod( kind::OR );
    //    bod << tn[i];
    //    bod << retVal.notNode();
    //    Node n = bod;
    //    activeArgs.push_back( n );
    //    nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
    //    activeArgs.pop_back();
    //    bodTot << tn[i].notNode();
    //  }
    //  bodTot << retVal;
    //  Node n = bodTot;
    //  activeArgs.push_back( n );
    //  nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
    //  activeArgs.pop_back();
    //}
    //  break;
    //case IMPLIES:
    //{

    //}
    //  break;
    //case EQUAL:
    //case IFF:
    //{
    //  for( int i=0; i<4; i++ ){
    //    NodeBuilder<> bod( kind::OR );
    //    bod << ( ( i==0 || i==3 ) ? retVal.notNode() : retVal );
    //    bod << ( i%2==0 ? tn[0] : tn[0].notNode() );
    //    bod << ( i>=2 ? tn[1] : tn[1].notNode() );
    //    Node n = bod;
    //    activeArgs.push_back( n );
    //    nb << NodeManager::currentNM()->mkNode(kind::FORALL, activeArgs );
    //    activeArgs.pop_back();
    //  }
    //}
    //  break;
    //case XOR:
    //  
    //  break;
    //case ITE:
    //  
    //  break;
    //default:
    //  break;
    //}
    //return retVal;
  //}
//}

Node QuantifiersRewriter::rewriteQuant( std::vector< Node >& args, Node body, NodeBuilder<>& defs, Node ipl, 
                                        bool isNested, bool isExists ){
  //std::cout << "rewrite quant " << body << std::endl;
  if( isExists ){
    Node retVal = rewriteQuant( args, body.notNode(), defs, ipl, isNested );
    return retVal.notNode();
  }else{
    if( body.getKind()==FORALL ){
      //combine arguments
      std::vector< Node > newArgs;
      for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
        newArgs.push_back( body[0][i] );
      }
      newArgs.insert( newArgs.end(), args.begin(), args.end() );
      return mkForAll( newArgs, body[ 1 ], ipl );   //Note that we may lose instantiation patterns on nested quantifiers FIXME?
    }else if( !isNested && !isClause( body ) ){
      NodeBuilder<> body_split(kind::OR);
      Node newBody = body;
      if( body.getKind()==NOT ){
        //push not downwards
        if( body[0].getKind()==NOT ){
          return rewriteQuant( args, body[0][0], defs, ipl );
        }else if( body[0].getKind()==AND ){
#ifdef QUANTIFIERS_REWRITE_PUSH_OUT_GROUND_SUBFORMULAS
          NodeBuilder<> t(kind::OR);
          for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
            t <<  body[0][i].notNode();
          }
          Node quant = t;
          return rewriteQuant( args, quant, defs, ipl );
#endif
        }else if( body[0].getKind()==OR || body[0].getKind()==IMPLIES ){
#ifdef QUANTIFIERS_REWRITE_SPLIT_AND
          NodeBuilder<> t(kind::AND);
          for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
            Node trm = ( body[0].getKind()==IMPLIES && i==0 ) ? body[0][i] : body[0][i].notNode();
            t << rewriteQuant( args, trm, defs, ipl );
          }
          Node retVal = t;
          return retVal;
#endif
        }else{
#ifdef QUANTIFIERS_REWRITE_SPLIT_AND_EXTENSIONS
          if( body[0].getKind()==IFF || body[0].getKind()==EQUAL ){
            Assert( body[0][0].getType()==NodeManager::currentNM()->booleanType() );
            return rewriteQuant( args, NodeManager::currentNM()->mkNode( body[0].getKind(), body[0][0], body[0][1].notNode() ), defs, ipl );
          }else if( body[0].getKind()==XOR ){
            return rewriteQuant( args, NodeManager::currentNM()->mkNode( XOR, body[0][0], body[0][1].notNode() ), defs, ipl );
          }else if( body[0].getKind()==ITE ){
            return rewriteQuant( args, NodeManager::currentNM()->mkNode( ITE, body[0][0], body[0][1].notNode(), body[0][2].notNode() ), defs, ipl );
          }
#endif
        }
      }else if( body.getKind()==AND ){
#ifdef QUANTIFIERS_REWRITE_SPLIT_AND
        //break apart
        NodeBuilder<> t(kind::AND);
        for( int i=0; i<(int)body.getNumChildren(); i++ ){
          t << rewriteQuant( args, body[i], defs, ipl );
        }
        Node retVal = t;
        return retVal;
#endif
      }else if( body.getKind()==OR || body.getKind()==IMPLIES ){
#ifdef QUANTIFIERS_REWRITE_PUSH_OUT_GROUND_SUBFORMULAS
        NodeBuilder<> tb(kind::OR);
        for( int i=0; i<(int)body.getNumChildren(); i++ ){
          Node trm = ( body.getKind()==IMPLIES && i==0 ) ? body[i].notNode() : body[i];
          if( hasArg( args, body[i] ) ){
            tb << trm;
          }else{
            body_split << trm;
          }
        }
        newBody = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
#endif
      }else if( body.getKind()==IFF || body.getKind()==EQUAL ){
#ifdef QUANTIFIERS_REWRITE_SPLIT_AND_EXTENSIONS
        Node n1 = rewriteQuant( args, NodeManager::currentNM()->mkNode( IMPLIES, body[0], body[1] ), defs, ipl );
        Node n2 = rewriteQuant( args, NodeManager::currentNM()->mkNode( IMPLIES, body[1], body[0] ), defs, ipl );
        return NodeManager::currentNM()->mkNode( AND, n1, n2 );
#endif
      }else if( body.getKind()==XOR ){
#ifdef QUANTIFIERS_REWRITE_SPLIT_AND_EXTENSIONS
        Node n1 = rewriteQuant( args, NodeManager::currentNM()->mkNode( OR, body[0], body[1] ), defs, ipl, isNested );
        Node n2 = rewriteQuant( args, NodeManager::currentNM()->mkNode( OR, body[0].notNode(), body[1].notNode() ), defs, ipl );
        return NodeManager::currentNM()->mkNode( AND, n1, n2 );
#endif
      }else if( body.getKind()==ITE ){
#ifdef QUANTIFIERS_REWRITE_SPLIT_AND_EXTENSIONS
        Node n1 = rewriteQuant( args, NodeManager::currentNM()->mkNode( OR, body[0], body[1] ), defs, ipl, isNested );
        Node n2 = rewriteQuant( args, NodeManager::currentNM()->mkNode( OR, body[0].notNode(), body[2] ), defs, ipl );
        return NodeManager::currentNM()->mkNode( AND, n1, n2 );
#endif
      }
      //if( !isNested && !isClause( newBody ) ){
      //  std::cout << "non-clausal " << body;
      //  exit( 8 );
      //}
      body_split << mkForAll( args, newBody, ipl );
      Node retVal = body_split.getNumChildren()==1 ? body_split.getChild( 0 ) : body_split;
      return retVal;
    }
    return mkForAll( args, body, ipl );
  }
}
